import CertiFri
import CertiFriP3
import CertiFriProofs

/-!
# Axiom check

Run from `Proofs/`, after `lake build`, with `lake env lean ../scripts/CheckAxioms.lean`
(`scripts/ci.sh axioms` does this).

Every constant declared in a module of `CertiFri`, `CertiFriP3` or `CertiFriProofs` must depend
on no axiom other than `propext`, `Classical.choice` and `Quot.sound`. Dependencies are followed
through types, values, proofs, constructors and recursor rules, across the whole environment
(Mathlib and the core library included). This excludes `sorry` (`sorryAx`), `native_decide`
(`Lean.ofReduceBool`), `Lean.trustCompiler` and any declared axiom. The dependencies are computed
here from the constants the kernel accepted, not taken from `Lean.collectAxioms`.

The canary below is an axiom of this file and a theorem that uses it. The check fails unless
the traversal finds that dependency, so it cannot pass by finding nothing.
-/

axiom CertiFriAxiomCheck.canary : True

theorem CertiFriAxiomCheck.canaryUse : True := CertiFriAxiomCheck.canary

open Lean

namespace CertiFriAxiomCheck

/-- The constants a constant refers to: its type, its value or proof, its constructors or its
inductive type, and its recursor rules. -/
def deps : ConstantInfo → Array Name
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo v => v.type.getUsedConstants
  | .ctorInfo v => v.type.getUsedConstants.push v.induct
  | .recInfo v => v.type.getUsedConstants ++ v.rules.toArray.flatMap (·.rhs.getUsedConstants)
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- The axioms the checked libraries may use. -/
def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The checked libraries, as module-name prefixes. -/
def libraries : Array Name := #[`CertiFri, `CertiFriP3, `CertiFriProofs]

end CertiFriAxiomCheck

open CertiFriAxiomCheck in
run_meta do
  let env ← getEnv
  let kenv := env.checked.get
  -- The reverse dependency graph of the whole environment, and its axioms.
  let (rev, axs) := kenv.constants.fold
    (init := (({} : Std.HashMap Name (Array Name)), (#[] : Array Name)))
    fun (acc : Std.HashMap Name (Array Name) × Array Name) n ci =>
      let (g, axs) := acc
      let axs := if ci matches .axiomInfo _ then axs.push n else axs
      ((deps ci).foldl (fun g u => let a := g.getD u #[]; (g.erase u).insert u (a.push n)) g, axs)
  -- Every constant that depends on an axiom outside `allowed`, with those axioms.
  let bad := axs.filter (!allowed.contains ·)
  let mut reach : Std.HashMap Name (Array Name) := {}
  for a in bad do
    reach := reach.insert a ((reach.getD a #[]).push a)
    let mut seen : Std.HashSet Name := {}
    let mut todo : Array Name := #[a]
    while h : todo.size > 0 do
      let n := todo.back
      todo := todo.pop
      for d in rev.getD n #[] do
        unless seen.contains d do
          seen := seen.insert d
          todo := todo.push d
          reach := reach.insert d ((reach.getD d #[]).push a)
  unless (reach.getD ``CertiFriAxiomCheck.canaryUse #[]).contains ``CertiFriAxiomCheck.canary do
    throwError "axiom check: the canary dependency was not found; the traversal is broken"
  let mut mods := 0
  let mut consts := 0
  let mut thms := 0
  let mut dirty : Array (Name × Name × Array Name) := #[]
  for m in env.header.moduleNames, md in env.header.moduleData do
    unless libraries.any (·.isPrefixOf m) do continue
    mods := mods + 1
    for c in md.constants do
      consts := consts + 1
      if c matches .thmInfo _ then thms := thms + 1
      if let some axs := reach.get? c.name then
        dirty := dirty.push (m, c.name, axs)
  IO.println s!"axiom check: {mods} modules, {consts} constants ({thms} theorems) of {libraries.toList}"
  IO.println s!"axiom check: axioms of the environment outside {allowed.toList}: {bad.toList}"
  for (m, n, axs) in dirty do
    IO.println s!"  {m}: {n} depends on {axs.toList}"
  if mods == 0 then
    throwError "axiom check: no module of {libraries.toList} is imported"
  unless dirty.isEmpty do
    throwError "axiom check: {dirty.size} constants depend on axioms outside {allowed.toList}"
  IO.println "axiom check: passed"
