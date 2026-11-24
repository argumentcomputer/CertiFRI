import CertiFri.Field

/-!
# Constraint graphs

The constraints of one circuit of a multi-stark system, as the verifier holds
them: a vector of arithmetic nodes over the base field, each node referring to
earlier ones by index, with the list of nodes that must vanish and the list of
lookups. Port of `ConstraintGraph` (`src/graph.rs`) and of its evaluator
(`src/eval.rs`) from multi-stark at revision `3515632`.

A graph is data of the verifying key. The verifier never builds one: the
compiler that produces them (`compile` in `src/graph.rs`) is outside this
port, and so is the per-node degree it records, which the verifier does not
read.

`sweep` evaluates every node once, first to last, for given values of the
column variables, the public values and the three row selectors. The verifier
runs it in the extension field, on the values opened at the out-of-domain
point.

## Differences from multi-stark

* A node that refers to a node at or after itself, a column outside its row or
  a public value outside the list reads zero. multi-stark's sweep has undefined
  behaviour on the first and panics on the others; its compiler never produces
  such a graph.

Nothing is proved here. The proofs package has the same evaluation over a
commutative ring and its properties
(`Proofs/CertiFriProofs/Theory/Stark/Graph.lean`).
-/

namespace CertiFri.Stark

/-- Which committed matrix a column variable refers to. -/
inductive Source where
  /-- The fixed trace, committed with the verifying key. -/
  | preprocessed
  /-- The main trace, committed first. -/
  | main
  /-- The lookup trace, committed after the lookup challenges, in its layout
  of base-field coordinate columns. -/
  | stage2
  deriving Repr, DecidableEq, Inhabited

/-- A column of a committed matrix, at the current row or the next one. -/
structure ColRef where
  /-- The matrix. -/
  source : Source
  /-- Whether the next row is meant. -/
  next : Bool
  /-- The column. -/
  index : Nat
  deriving Repr, DecidableEq, Inhabited

/-- One node of a constraint graph. The operands of an operation are indices
of earlier nodes. -/
inductive Node (F : Type) where
  /-- A constant. -/
  | const (c : F)
  /-- A column variable. -/
  | var (col : ColRef)
  /-- A public value, by position. -/
  | pub (index : Nat)
  /-- The selector of the first row. -/
  | isFirstRow
  /-- The selector of the last row. -/
  | isLastRow
  /-- The selector of every row but the last. -/
  | isTransition
  /-- The sum of two nodes. -/
  | add (a b : Nat)
  /-- The difference of two nodes. -/
  | sub (a b : Nat)
  /-- The product of two nodes. -/
  | mul (a b : Nat)
  /-- The negation of a node. -/
  | neg (a : Nat)
  deriving Repr, Inhabited

/-- A lookup: on every row, the message `args` is sent with multiplicity
`multiplicity`. Both are given by nodes of the graph. -/
structure Lookup where
  /-- The node of the multiplicity. -/
  multiplicity : Nat
  /-- The nodes of the arguments, in order. -/
  args : Array Nat
  deriving Repr, Inhabited

/-- The constraint graph of a circuit. -/
structure Graph (F : Type) where
  /-- The nodes; an operation refers to nodes before itself. -/
  nodes : Array (Node F)
  /-- The nodes that must be zero on every row. -/
  zeros : Array Nat
  /-- The lookups of the circuit. -/
  lookups : Array Lookup
  deriving Inhabited

/-- What the nodes of a graph are evaluated on: two adjacent rows of each
matrix, the public values and the row selectors. -/
structure RowValues (W : Type) where
  /-- The current row of the fixed trace. -/
  preprocessed : Array W
  /-- The next row of the fixed trace. -/
  preprocessedNext : Array W
  /-- The current row of the main trace. -/
  main : Array W
  /-- The next row of the main trace. -/
  mainNext : Array W
  /-- The current row of the lookup trace. -/
  stage2 : Array W
  /-- The next row of the lookup trace. -/
  stage2Next : Array W
  /-- The public values. -/
  publics : Array W
  /-- The value of the first-row selector. -/
  isFirstRow : W
  /-- The value of the last-row selector. -/
  isLastRow : W
  /-- The value of the transition selector. -/
  isTransition : W

section Eval

variable {F EF : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF]

/-- The value of a column variable; zero if the row has no such column. -/
def RowValues.var (v : RowValues EF) (col : ColRef) : EF :=
  let row :=
    match col.source, col.next with
    | .preprocessed, false => v.preprocessed
    | .preprocessed, true => v.preprocessedNext
    | .main, false => v.main
    | .main, true => v.mainNext
    | .stage2, false => v.stage2
    | .stage2, true => v.stage2Next
  row.getD col.index 0

/-- The value of one node, given the values `buf` of the nodes before it. -/
def evalNode (v : RowValues EF) (buf : Array EF) : Node F → EF
  | .const c => ExtensionOps.embed c
  | .var col => v.var col
  | .pub index => v.publics.getD index 0
  | .isFirstRow => v.isFirstRow
  | .isLastRow => v.isLastRow
  | .isTransition => v.isTransition
  | .add a b => buf.getD a 0 + buf.getD b 0
  | .sub a b => buf.getD a 0 - buf.getD b 0
  | .mul a b => buf.getD a 0 * buf.getD b 0
  | .neg a => -buf.getD a 0

/-- The values of all nodes, first to last (`ConstraintGraph::sweep`). -/
def Graph.sweep (g : Graph F) (v : RowValues EF) : Array EF :=
  g.nodes.foldl (fun buf node => buf.push (evalNode v buf node)) (Array.mkEmpty g.nodes.size)

/-- The values of the nodes that must vanish, read off the values of all
nodes (`ConstraintGraph::constraint_values`). -/
def Graph.constraintValues (g : Graph F) (buf : Array EF) : Array EF :=
  g.zeros.map fun z => buf.getD z 0

end Eval

end CertiFri.Stark
