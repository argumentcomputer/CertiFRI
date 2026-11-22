import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree
import CertiFriP3.GoldilocksExt3
import CertiFriProofs.P3.Goldilocks
import CertiFriProofs.Exec.SoundnessUnconditional
import CertiFriProofs.Exec.Extract
import CertiFriProofs.Exec.Binding

/-!
# Formal verification of Goldilocks cubic trinomial extension `Fp3` (`X^3 - X - 1`)

This file proves, strictly in Lean's kernel without `sorry`, `axiom`,
`native_decide`, or `bv_decide`, that `CertiFri.P3.GoldilocksExt3` faithfully
implements the cubic extension field `Fp3Model ≃+* GF(p)[X] / (X^3 - X - 1)` of
order `p^3 = (2^64 - 2^32 + 1)^3 ≈ 2^192`, and instantiates the unconditional
executable verifier soundness, knowledge soundness, and binding theorems over
`Goldilocks` / `GoldilocksExt3`:

* `cubicTrinomial_irreducible`: `X^3 - X - 1 ∈ (ZMod Goldilocks.order)[X]` is
  irreducible, proved by verifying `N(X^p - X) ≠ 0` in the quotient ring via
  kernel-checked 64-bit binary exponentiation.
* `Fp3Model` with `Field Fp3Model` and `card_fp3Model : Fintype.card Fp3Model = Goldilocks.order ^ 3`.
* `goldilocksExt3_refines`: `Refines GoldilocksExt3 Fp3Model` (including
  Karatsuba multiplication and exact adjugate/norm inversion).
* `goldilocksExt3_fieldModel`: `Exec.FieldModel Goldilocks GoldilocksExt3 Fp3Model`.
* `goldilocksExt3_wellFormed`: `Exec.WellFormed goldilocksExt3_fieldModel params shape`
  for every shape with `logMaxHeight params.logBlowup shape ≤ 32`.
* `Exec.goldilocksExt3_soundness_uniqueDecoding`,
  `Exec.goldilocksExt3_knowledge_soundness`, and
  `Exec.goldilocksExt3_binding`: concrete, zero-`sorry` security theorems for
  `Fri.verify` over `Goldilocks` / `GoldilocksExt3` with explicit field size
  `Goldilocks.order ^ 3` (`≈ 2^192`).
-/

namespace CertiFri.P3

open Polynomial

/-- Alias for the Goldilocks base prime field `ZMod Goldilocks.order`. -/
abbrev GoldilocksField : Type := ZMod Goldilocks.order

/-- Mathematical model of the cubic trinomial extension
`GF(p)[X] / (X^3 - X - 1)` in basis `(1, X, X^2)`. -/
@[ext]
structure Fp3Model where
  c0 : GoldilocksField
  c1 : GoldilocksField
  c2 : GoldilocksField
  deriving DecidableEq

namespace Fp3Model

def zero : Fp3Model := ⟨0, 0, 0⟩
def one : Fp3Model := ⟨1, 0, 0⟩
def xElem : Fp3Model := ⟨0, 1, 0⟩
def embed (a : GoldilocksField) : Fp3Model := ⟨a, 0, 0⟩

def add (a b : Fp3Model) : Fp3Model :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩

def sub (a b : Fp3Model) : Fp3Model :=
  ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩

def neg (a : Fp3Model) : Fp3Model :=
  ⟨-a.c0, -a.c1, -a.c2⟩

/-- Multiplication modulo `X^3 - X - 1` (`X^3 = X + 1`, `X^4 = X^2 + X`). -/
def mul (a b : Fp3Model) : Fp3Model :=
  ⟨a.c0 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1,
   a.c0 * b.c1 + a.c1 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1 + a.c2 * b.c2,
   a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + a.c2 * b.c2⟩

instance : Zero Fp3Model := ⟨zero⟩
instance : One Fp3Model := ⟨one⟩
instance : Add Fp3Model := ⟨add⟩
instance : Sub Fp3Model := ⟨sub⟩
instance : Neg Fp3Model := ⟨neg⟩
instance : Mul Fp3Model := ⟨mul⟩

@[simp] theorem zero_c0 : (0 : Fp3Model).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp3Model).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : Fp3Model).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp3Model).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp3Model).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : Fp3Model).c2 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp3Model) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp3Model) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : Fp3Model) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem sub_c0 (a b : Fp3Model) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp3Model) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : Fp3Model) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem neg_c0 (a : Fp3Model) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp3Model) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : Fp3Model) : (-a).c2 = -a.c2 := rfl
@[simp] theorem mul_c0 (a b : Fp3Model) :
    (a * b).c0 = a.c0 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1 := rfl
@[simp] theorem mul_c1 (a b : Fp3Model) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1 + a.c2 * b.c2 := rfl
@[simp] theorem mul_c2 (a b : Fp3Model) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + a.c2 * b.c2 := rfl

instance : CommRing Fp3Model where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec
  add_comm a b := by ext <;> simp <;> ring
  zsmul := zsmulRec
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  mul_comm a b := by ext <;> simp <;> ring

instance : Nontrivial Fp3Model :=
  ⟨⟨1, 0, fun h => one_ne_zero (congrArg Fp3Model.c0 h)⟩⟩

/-- Equivalence with triples over `ZMod Goldilocks.order`, giving `Fintype` and cardinality `p^3`. -/
def equivTriple : Fp3Model ≃ GoldilocksField × GoldilocksField × GoldilocksField where
  toFun a := (a.c0, a.c1, a.c2)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv a := by cases a; rfl
  right_inv t := by rcases t with ⟨_, _, _⟩; rfl

private theorem card_triple_zmod (p : ℕ) [NeZero p] :
    Fintype.card (ZMod p × ZMod p × ZMod p) = p ^ 3 := by
  rw [Fintype.card_prod, Fintype.card_prod, ZMod.card]
  ring

noncomputable instance : Fintype Fp3Model :=
  Fintype.ofEquiv _ equivTriple.symm

theorem card_fp3Model : Fintype.card Fp3Model = Goldilocks.order ^ 3 :=
  (Fintype.card_congr equivTriple).trans (card_triple_zmod Goldilocks.order)

/-- Ring homomorphism embedding `ZMod Goldilocks.order` into `Fp3Model`. -/
def embedHom : GoldilocksField →+* Fp3Model where
  toFun := embed
  map_one' := rfl
  map_mul' a b := by ext <;> simp [embed]
  map_zero' := rfl
  map_add' a b := by ext <;> simp [embed]

@[simp] theorem embedHom_apply (a : GoldilocksField) : embedHom a = embed a := rfl
@[simp] theorem embed_c0 (a : GoldilocksField) : (embed a).c0 = a := rfl
@[simp] theorem embed_c1 (a : GoldilocksField) : (embed a).c1 = 0 := rfl
@[simp] theorem embed_c2 (a : GoldilocksField) : (embed a).c2 = 0 := rfl

theorem embedHom_injective : Function.Injective embedHom := fun _ _ h =>
  congrArg Fp3Model.c0 h

/-- First column of the adjugate of the `3 × 3` multiplication matrix. -/
def adjugate (a : Fp3Model) : Fp3Model :=
  let a02 := a.c0 + a.c2
  ⟨a02 * a02 - a.c1 * (a.c1 + a.c2),
   a.c2 * a.c2 - a.c0 * a.c1,
   a.c1 * a.c1 - a.c2 * a02⟩

/-- Field norm `N(a) = det M_a`. -/
def norm (a : Fp3Model) : GoldilocksField :=
  let adj := a.adjugate
  a.c0 * adj.c0 + a.c2 * adj.c1 + a.c1 * adj.c2

theorem mul_adjugate (a : Fp3Model) : a * a.adjugate = embedHom a.norm := by
  ext <;> simp only [mul_c0, mul_c1, mul_c2, adjugate, norm, embedHom_apply, embed_c0, embed_c1,
    embed_c2] <;> ring

theorem xElem_cube : xElem ^ 3 - xElem - 1 = 0 := by
  have h3 : xElem ^ 3 = xElem * xElem * xElem := by ring
  rw [h3]
  ext <;> simp [xElem]

/-! ## Irreducibility of `X^3 - X - 1` over `ZMod Goldilocks.order` -/

/-- The cubic trinomial `X^3 - X - 1 ∈ (ZMod Goldilocks.order)[X]`. -/
noncomputable def cubicTrinomial : Polynomial GoldilocksField :=
  X ^ 3 - X - 1

/-- Natural-number arithmetic in `(ℕ/mℕ)[X] / (X^3 - X - 1)` for kernel-verified
evaluation of `X^p - X`. -/
private def fp3NatMul (m : ℕ) (a b : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let (a0, a1, a2) := a
  let (b0, b1, b2) := b
  ((a0 * b0 + a1 * b2 + a2 * b1) % m,
   (a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2) % m,
   (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) % m)

private def checkFp3SqTable (m : ℕ) : (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | cur, x :: rest => (cur == x) && checkFp3SqTable m (fp3NatMul m x x) rest

/-- Step-by-step certified binary exponentiation in `(ℕ/mℕ)[X] / (X^3 - X - 1)`.
Each step compares literal triples, avoiding call-by-name thunk duplication in
the Lean kernel. -/
private def checkFp3MulSteps (m : ℕ) :
    ℕ → List (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ) → Option (ℕ × ℕ × ℕ)
  | 0, [], acc, [] => some acc
  | e, sq :: sqs, acc, acc' :: accs =>
    if (if e % 2 = 1 then fp3NatMul m acc sq else acc) == acc' then
      checkFp3MulSteps m (e / 2) sqs acc' accs
    else none
  | _, _, _, _ => none

private def ofNatTriple (t : ℕ × ℕ × ℕ) : Fp3Model :=
  ⟨(t.1 : GoldilocksField), (t.2.1 : GoldilocksField), (t.2.2 : GoldilocksField)⟩

private theorem ofNatTriple_mul (a b : ℕ × ℕ × ℕ) :
    ofNatTriple (fp3NatMul Goldilocks.order a b) = ofNatTriple a * ofNatTriple b := by
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  ext <;> simp [fp3NatMul, ofNatTriple, ZMod.natCast_mod]

private theorem ofNatTriple_checkFp3MulSteps :
    ∀ (sqs steps : List (ℕ × ℕ × ℕ)) (cur acc res : ℕ × ℕ × ℕ) (e : ℕ),
      checkFp3SqTable Goldilocks.order cur sqs = true →
      checkFp3MulSteps Goldilocks.order e sqs acc steps = some res →
      ofNatTriple res = ofNatTriple acc * (ofNatTriple cur) ^ e
  | [], [], _, acc, res, 0, _, hchk => by
    simp only [checkFp3MulSteps, Option.some.injEq] at hchk
    subst hchk
    simp
  | [], [], _, _, _, _ + 1, _, hchk => by simp [checkFp3MulSteps] at hchk
  | [], _ :: _, _, _, _, e, _, hchk => by cases e <;> simp [checkFp3MulSteps] at hchk
  | _ :: _, [], _, _, _, e, _, hchk => by cases e <;> simp [checkFp3MulSteps] at hchk
  | sq :: sqs, acc' :: steps, cur, acc, res, e, hsq, hchk => by
    simp only [checkFp3SqTable, Bool.and_eq_true, beq_iff_eq] at hsq
    obtain ⟨hcur, hsqs⟩ := hsq
    subst hcur
    have hstep : (if e % 2 = 1 then fp3NatMul Goldilocks.order acc cur else acc) = acc' ∧
        checkFp3MulSteps Goldilocks.order (e / 2) sqs acc' steps = some res := by
      simp only [checkFp3MulSteps] at hchk
      by_cases hcond : ((if e % 2 = 1 then fp3NatMul Goldilocks.order acc cur else acc) == acc') = true
      · rw [ite_eq_left hcond] at hchk
        exact ⟨beq_iff_eq.mp hcond, hchk⟩
      · rw [ite_eq_right hcond] at hchk
        cases hchk
    have ih := ofNatTriple_checkFp3MulSteps sqs steps (fp3NatMul Goldilocks.order cur cur)
      acc' res (e / 2) hsqs hstep.2
    rw [ih, ofNatTriple_mul, ← sq, ← pow_mul, ← hstep.1]
    split_ifs with hodd
    · rw [ofNatTriple_mul, mul_assoc, ← pow_succ']
      congr 2
      omega
    · congr 2
      omega

/-- Certified squaring table `X^(2^k)` in `Fp3Model` for `k = 0, …, 63`. -/
private def sqTableX : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 0), (0, 0, 1), (0, 1, 1), (2, 3, 2), (16, 28, 21), (1432, 2513, 1897),
   (11584946, 20330163, 15346786), (758216295635152, 1330576843394428, 1004422742303477),
   (17372766340139064469, 9557085918088446932, 15354445961624571197),
   (3509459721280925154, 11514812652314720115, 1200991702222341375),
   (6841103724816679185, 11222150267719621178, 15563510825788724668),
   (9440462931311328392, 13857090502216904544, 17589633011169988068),
   (16819528958367300955, 8615056102248217534, 569232632836573868),
   (17140222094744348464, 14165951618730066331, 17152841575636035006),
   (8418318907588004139, 22428703637656057, 6582359677925617020),
   (767722960220274515, 14627373815190563013, 8710411886900515978),
   (385693368393256935, 8603804293785492277, 6124110923987225995),
   (2853122117199794220, 7512198633866561946, 16971451762190044101),
   (12151902958023338546, 13484842841101145280, 3582304359794017908),
   (10224992181480688384, 16633454005149103480, 13033421829960845217),
   (13449938289856480782, 7374674915123898758, 5845395811342087090),
   (10696057721481665275, 8798528314102901544, 16917761466840770533),
   (13537386044881551521, 3705677173898304428, 8032460359406040182),
   (13859138746956445181, 1776075322834998865, 2909434198963183692),
   (14764577181388025928, 17746581676041222082, 12108162915781342237),
   (4003639200154987791, 15739832279603431212, 2427710258508434300),
   (1428184821664116465, 3486696471522010340, 16316167142954428440),
   (13079628040886172071, 557744702066876284, 11172352635674949692),
   (9787163918615041340, 15146493807739145252, 5331292245756089361),
   (9799591891816256491, 17330899312865648572, 13450600588678059457),
   (15598322179228703257, 9325043480286899252, 4648274645770861737),
   (628221846932513290, 4594102871486117174, 5907837206726511540),
   (4313033625783026847, 4123756567369592585, 13756005300681981762),
   (12607646404735112778, 13327610258238037934, 17734291532653803390),
   (925354551479961996, 12030666936299136886, 7461415465917693229),
   (13044331408263984252, 11461860201702712917, 573795447562038500),
   (3212809479733501104, 18163099207507449997, 9473894190016332280),
   (6791493080144351004, 14727176535711091984, 3066030207150266780),
   (873402866144866480, 10250051513113493641, 5897162659479242306),
   (6961751116629775684, 8264568878050814716, 3483752813938653528),
   (4358114576167036254, 14139296206291393548, 1451789787186608704),
   (14292943501030182470, 5274624153182619279, 2630426797643177756),
   (6900172909268517948, 12021914562984351733, 5679212788924843667),
   (11559249486530646911, 5799295627439068525, 10782907988370352600),
   (3927598984488543255, 18274156811450324139, 12277857525045962116),
   (8775030492173327093, 2935290626899303650, 311936205690203242),
   (15468691063565846067, 9976909525582568813, 17672104663686149782),
   (17532020344685104948, 18107403598486519936, 748845027959109220),
   (8854585105112987765, 13589489451603127301, 9357132992060661220),
   (5502671418524984555, 13850104363691969497, 138165383596815434),
   (13658946683378723015, 16220459973757844118, 15688061723879106835),
   (1954228645075490959, 2246885487649248541, 7915590249961340229),
   (4070455656583887321, 11541362485559587522, 7330029841607960957),
   (748266820931762279, 2106639283174989949, 5620466764628126715),
   (2410863489923985612, 3941615857195757976, 5548256865122182134),
   (3630708328067381459, 1747863527317022142, 9845007181724105359),
   (4715927453802294321, 9424413537322174545, 10212156649832762384),
   (9706472742729618523, 13146487865350974557, 18171348228166988615),
   (15974640668512086343, 7209491194420303510, 6060780110821425449),
   (15026713309929068331, 13862660483710538649, 12503989524729962017),
   (13211469218323652638, 11052365528177614630, 6686435503645086313),
   (14295561104199821264, 16851938212622414037, 9153851763062612586),
   (11527829033624401907, 1113397040867984224, 1261379089236372842),
   (17973959301433576331, 16711574814292626461, 2598692120067411561)]

private theorem sqTableX_ok :
    checkFp3SqTable Goldilocks.order (0, 1, 0) sqTableX = true := rfl

/-- Certified intermediate accumulator values for `X^p` in `Fp3Model`. -/
private def frobSteps : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0),
   (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0),
   (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0),
   (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0), (0, 1, 0),
   (13756005300681981762, 18069038926465008609, 4123756567369592585),
   (14788276583284992632, 8624662332760850783, 16664750556704292885),
   (5648395988117470330, 11489871049659818264, 17938638662720282782),
   (152582786219834161, 3651534002201260491, 6510031807883927247),
   (7816523760977747343, 5487495084232784878, 5726929811366469537),
   (6473875601695286106, 7250402975713006707, 1643615404057431027),
   (2417065094252531395, 5064802584823705121, 5363070825360050648),
   (4700304545418720823, 9069446577355141834, 3889352830628654893),
   (7517982354384105320, 8379794758232866497, 9932282168703094968),
   (4041419698346949644, 4047713920395647522, 80945731623332076),
   (10305915652627155303, 8304588242045625342, 10221275072110923096),
   (5123695769270267454, 12122069449662226533, 8604823813282103939),
   (8462760899231792340, 1808573973663206075, 5224991730793090756),
   (13731033738556686815, 8337322273196182833, 7125303417532212055),
   (13544296421190429963, 4368513979953522887, 10185725551880715040),
   (7062317736847679890, 273982680656749754, 584849719765196763),
   (14769472413589966205, 9416344092730214773, 14128986140863883091),
   (2255220646195946601, 14240730180668909256, 17042745085532974169),
   (17961045964899708224, 5634196570782204891, 14530546398341862725),
   (728864376745618720, 7210668684118941395, 14771291465906418642),
   (16852160913527562802, 15842325830175187484, 17739867042803366574),
   (17192444078005075649, 6940239454699280941, 244307394227808025),
   (11201237148682570709, 9415976534514806667, 16487193729234643908),
   (10989308258477163207, 12823301331734201992, 210872546212437047),
   (18066636080420455369, 4832192216006151128, 17219199301267404537),
   (12589591097798671034, 8893995212420565976, 3122711287675573655),
   (991521261010686639, 17949223314271865966, 1172244867328587387),
   (3975397510050098427, 14772861818582861511, 7430779088538326180),
   (10380806728570174415, 1920500345583365085, 16121707541280195496),
   (7345957444685127115, 3862743107043666844, 3554028541125304450),
   (2966080377479370921, 15376424789583843415, 4341787508243352093),
   (10615703402128488253, 10050274602728160328, 11746561000929144102)]

private def frobXNat : ℕ × ℕ × ℕ :=
  (10615703402128488253, 10050274602728160328, 11746561000929144102)

private theorem frobSteps_ok :
    checkFp3MulSteps Goldilocks.order Goldilocks.order sqTableX (1, 0, 0) frobSteps =
      some frobXNat := rfl

private def fp3NatNorm (m : ℕ) (a : ℕ × ℕ × ℕ) : ℕ :=
  let (a0, a1, a2) := a
  let a02 := (a0 + a2) % m
  let s0 := ((a02 * a02) % m + m - (a1 * ((a1 + a2) % m)) % m) % m
  let s1 := ((a2 * a2) % m + m - (a0 * a1) % m) % m
  let s2 := ((a1 * a1) % m + m - (a2 * a02) % m) % m
  (a0 * s0 + a2 * s1 + a1 * s2) % m

private theorem nat_sub_mod_zmod (x y : ℕ) :
    (((x % Goldilocks.order + Goldilocks.order - y % Goldilocks.order) % Goldilocks.order : ℕ) :
      GoldilocksField) = (x : GoldilocksField) - (y : GoldilocksField) := by
  have hm : 0 < Goldilocks.order := by unfold Goldilocks.order; decide
  have hy : y % Goldilocks.order ≤ x % Goldilocks.order + Goldilocks.order := by
    have := Nat.mod_lt y hm
    omega
  rw [ZMod.natCast_mod, Nat.cast_sub hy, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod,
    ZMod.natCast_self, add_zero]

private theorem fp3NatNorm_spec (a : ℕ × ℕ × ℕ) :
    (fp3NatNorm Goldilocks.order a : GoldilocksField) = (ofNatTriple a).norm := by
  rcases a with ⟨a0, a1, a2⟩
  unfold fp3NatNorm norm adjugate ofNatTriple
  dsimp only
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    nat_sub_mod_zmod, nat_sub_mod_zmod, nat_sub_mod_zmod]
  simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_mod]

/-- The element `X^p - X` in `Fp3Model`, represented as a literal triple modulo `p`. -/
private def frobSubXNat : ℕ × ℕ × ℕ :=
  (10615703402128488253, 10050274602728160327, 11746561000929144102)

private theorem ofNatTriple_frobSubXNat :
    ofNatTriple frobSubXNat = xElem ^ Goldilocks.order - xElem := by
  have ht : ofNatTriple frobXNat = xElem ^ Goldilocks.order := by
    have h1 : ofNatTriple (1, 0, 0) = 1 := by ext <;> simp [ofNatTriple]
    have hx : ofNatTriple (0, 1, 0) = xElem := by ext <;> simp [ofNatTriple, xElem]
    have := ofNatTriple_checkFp3MulSteps sqTableX frobSteps (0, 1, 0) (1, 0, 0) frobXNat
      Goldilocks.order sqTableX_ok frobSteps_ok
    simpa [h1, hx] using this
  rw [← ht]
  ext
  · rfl
  · simp only [ofNatTriple, frobSubXNat, frobXNat, xElem, sub_c1]
    have hsub : (10050274602728160327 : ℕ) + 1 = 10050274602728160328 := rfl
    have hc := congrArg (Nat.cast (R := GoldilocksField)) hsub
    simp only [Nat.cast_add, Nat.cast_one] at hc
    exact eq_sub_of_add_eq hc
  · simp [ofNatTriple, frobSubXNat, frobXNat, xElem]

/-- Kernel-checked certificate: `N(X^p - X) % p ≠ 0`. -/
private theorem frobSubXNat_norm_ne_zero :
    fp3NatNorm Goldilocks.order frobSubXNat ≠ 0 := by
  decide

private theorem frobSubX_norm_ne_zero :
    (xElem ^ Goldilocks.order - xElem).norm ≠ 0 := by
  rw [← ofNatTriple_frobSubXNat, ← fp3NatNorm_spec]
  intro h0
  have hdvd : Goldilocks.order ∣ fp3NatNorm Goldilocks.order frobSubXNat :=
    (ZMod.natCast_eq_zero_iff _ _).mp h0
  have hlt : fp3NatNorm Goldilocks.order frobSubXNat < Goldilocks.order :=
    Nat.mod_lt _ (by unfold Goldilocks.order; decide)
  exact frobSubXNat_norm_ne_zero (Nat.eq_zero_of_dvd_of_lt hdvd hlt)

/-- Evaluation of `Fp3Model` at a hypothetical root `r` of `X^3 - X - 1`. -/
private def evalRoot (r : GoldilocksField) (hr : r ^ 3 - r - 1 = 0) :
    Fp3Model →+* GoldilocksField where
  toFun a := a.c0 + a.c1 * r + a.c2 * r ^ 2
  map_one' := by simp
  map_mul' a b := by
    simp only [mul_c0, mul_c1, mul_c2]
    linear_combination -(a.c1 * b.c2 + a.c2 * b.c1 + a.c2 * b.c2 * r) * hr
  map_zero' := by simp
  map_add' a b := by simp; ring

/-- `X^3 - X - 1` has no roots in `ZMod Goldilocks.order`. -/
theorem cubicTrinomial_no_root (r : GoldilocksField) :
    cubicTrinomial.eval r ≠ 0 := by
  intro hr
  have hr' : r ^ 3 - r - 1 = 0 := by
    simpa [cubicTrinomial] using hr
  let ev := evalRoot r hr'
  have hevX : ev xElem = r := by simp [ev, evalRoot, xElem]
  have hevU : ev (xElem ^ Goldilocks.order - xElem) = 0 := by
    rw [map_sub, map_pow, hevX, ZMod.pow_card, sub_self]
  have hevN : ev ((xElem ^ Goldilocks.order - xElem) *
      (xElem ^ Goldilocks.order - xElem).adjugate) =
      (xElem ^ Goldilocks.order - xElem).norm := by
    rw [mul_adjugate]
    simp [ev, evalRoot]
  rw [map_mul, hevU, zero_mul] at hevN
  exact frobSubX_norm_ne_zero hevN.symm

theorem natDegree_cubicTrinomial : cubicTrinomial.natDegree = 3 := by
  unfold cubicTrinomial
  compute_degree!

theorem cubicTrinomial_ne_zero : cubicTrinomial ≠ 0 := by
  intro h
  have hd := natDegree_cubicTrinomial
  rw [h, natDegree_zero] at hd
  omega

/-- **Irreducibility of `X^3 - X - 1` over `ZMod Goldilocks.order`.** -/
theorem cubicTrinomial_irreducible : Irreducible cubicTrinomial := by
  refine ⟨?_, ?_⟩
  · intro hu
    have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [natDegree_cubicTrinomial] at hd
    omega
  · intro f g hfg
    have hf0 : f ≠ 0 := by rintro rfl; exact cubicTrinomial_ne_zero (by simpa using hfg)
    have hg0 : g ≠ 0 := by rintro rfl; exact cubicTrinomial_ne_zero (by simpa using hfg)
    have hdeg : f.natDegree + g.natDegree = 3 := by
      rw [← natDegree_mul hf0 hg0, ← hfg, natDegree_cubicTrinomial]
    have hno1 : ∀ p : Polynomial GoldilocksField, p ∣ cubicTrinomial → p.natDegree ≠ 1 := by
      intro p hp hdeg1
      have hd1 : p.degree = 1 := by
        rw [Polynomial.degree_eq_natDegree (by intro hp0; rw [hp0] at hdeg1; simp at hdeg1), hdeg1]
        rfl
      obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one hd1
      obtain ⟨q, hq⟩ := hp
      have hroot : cubicTrinomial.eval r = 0 := by
        rw [hq, eval_mul, hr, zero_mul]
      exact cubicTrinomial_no_root r hroot
    have hf1 : f.natDegree ≠ 1 := hno1 f ⟨g, hfg⟩
    have hg1 : g.natDegree ≠ 1 := hno1 g ⟨f, by rw [mul_comm]; exact hfg⟩
    by_cases hf0d : f.natDegree = 0
    · left
      exact Polynomial.isUnit_iff_degree_eq_zero.mpr
        (by rw [Polynomial.degree_eq_natDegree hf0, hf0d]; rfl)
    · right
      have hg0d : g.natDegree = 0 := by omega
      exact Polynomial.isUnit_iff_degree_eq_zero.mpr
        (by rw [Polynomial.degree_eq_natDegree hg0, hg0d]; rfl)

/-! ## `Field Fp3Model` via `AdjoinRoot cubicTrinomial` -/

private instance : Fact (Irreducible cubicTrinomial) := ⟨cubicTrinomial_irreducible⟩

private noncomputable def adjoinLift : AdjoinRoot cubicTrinomial →+* Fp3Model :=
  AdjoinRoot.lift embedHom xElem (by
    simp only [cubicTrinomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    exact xElem_cube)

private theorem adjoinLift_bijective : Function.Bijective adjoinLift := by
  refine ⟨adjoinLift.injective, fun a => ?_⟩
  refine ⟨AdjoinRoot.mk cubicTrinomial (C a.c0 + C a.c1 * X + C a.c2 * X ^ 2), ?_⟩
  simp only [adjoinLift, AdjoinRoot.lift_mk, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    embedHom_apply]
  rw [sq]
  ext <;> simp [xElem]

/-- Ring isomorphism `AdjoinRoot (X^3 - X - 1) ≃+* Fp3Model`. -/
noncomputable def adjoinEquiv : AdjoinRoot cubicTrinomial ≃+* Fp3Model :=
  RingEquiv.ofBijective adjoinLift adjoinLift_bijective

instance : IsDomain Fp3Model :=
  adjoinEquiv.symm.toMulEquiv.isDomain (AdjoinRoot cubicTrinomial)

/-- Every nonzero element of `Fp3Model` has nonzero norm. -/
theorem norm_ne_zero_of_ne_zero {a : Fp3Model} (ha : a ≠ 0) : a.norm ≠ 0 := by
  intro hn
  have hmul : a * a.adjugate = 0 := by
    rw [mul_adjugate, hn, map_zero]
  have hadj : a.adjugate = 0 := (mul_eq_zero.mp hmul).resolve_left ha
  have hs0 : (a.c0 + a.c2) * (a.c0 + a.c2) - a.c1 * (a.c1 + a.c2) = 0 :=
    congrArg Fp3Model.c0 hadj
  have hs1 : a.c2 * a.c2 - a.c0 * a.c1 = 0 := congrArg Fp3Model.c1 hadj
  have hs2 : a.c1 * a.c1 - a.c2 * (a.c0 + a.c2) = 0 := congrArg Fp3Model.c2 hadj
  by_cases hc1 : a.c1 = 0
  · have hc2 : a.c2 = 0 := by
      have : a.c2 * a.c2 = 0 := by simpa [hc1] using hs1
      exact mul_self_eq_zero.mp this
    have hc0 : a.c0 = 0 := by
      have : a.c0 * a.c0 = 0 := by simpa [hc1, hc2] using hs0
      exact mul_self_eq_zero.mp this
    exact ha (by ext <;> simp [hc0, hc1, hc2])
  · set r : GoldilocksField := a.c2 / a.c1
    have hc2 : a.c2 = r * a.c1 := (div_mul_cancel₀ a.c2 hc1).symm
    have hc0 : a.c0 = r ^ 2 * a.c1 := by
      have h1 : a.c0 * a.c1 = (r ^ 2 * a.c1) * a.c1 := by
        rw [hc2] at hs1
        linear_combination -hs1
      exact mul_right_cancel₀ hc1 h1
    have hpoly : r ^ 3 + r ^ 2 = 1 := by
      have h2 : (r ^ 3 + r ^ 2) * (a.c1 * a.c1) = 1 * (a.c1 * a.c1) := by
        rw [hc0, hc2] at hs2
        linear_combination -hs2
      exact mul_right_cancel₀ (mul_ne_zero hc1 hc1) h2
    have hr0 : r ≠ 0 := by
      intro hr
      rw [hr] at hpoly
      norm_num at hpoly
    have hroot : cubicTrinomial.eval r⁻¹ = 0 := by
      simp only [cubicTrinomial, eval_sub, eval_pow, eval_X, eval_one]
      have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr0
      apply mul_right_cancel₀ hr3
      rw [zero_mul]
      have hinv1 : r⁻¹ ^ 3 * r ^ 3 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr0, one_pow]
      have hinv2 : r⁻¹ * r ^ 3 = r ^ 2 := by
        rw [show r ^ 3 = r * r ^ 2 by ring, ← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
      linear_combination hinv1 - hinv2 - hpoly
    exact cubicTrinomial_no_root r⁻¹ hroot

/-- Exact adjugate/norm inverse on `Fp3Model`, mapping `0` to `0`. -/
def inv (a : Fp3Model) : Fp3Model :=
  if a.norm = 0 then 0 else embedHom a.norm⁻¹ * a.adjugate

instance : Inv Fp3Model := ⟨inv⟩

noncomputable instance : Field Fp3Model where
  inv := inv
  inv_zero := by simp [inv, norm, adjugate]
  mul_inv_cancel a ha := by
    have hn : a.norm ≠ 0 := norm_ne_zero_of_ne_zero ha
    change a * inv a = 1
    unfold inv
    rw [ite_eq_right hn, mul_left_comm, mul_adjugate, ← map_mul, inv_mul_cancel₀ hn, map_one]
  nnqsmul := _
  qsmul := _

end Fp3Model

/-! ## Refinement `Refines GoldilocksExt3 Fp3Model` and `Exec.FieldModel` -/

namespace GoldilocksExt3

/-- Abstraction map from executable `GoldilocksExt3` to `Fp3Model`. -/
def toModel (a : GoldilocksExt3) : Fp3Model :=
  ⟨Goldilocks.toZMod a.c0, Goldilocks.toZMod a.c1, Goldilocks.toZMod a.c2⟩

theorem toModel_zero : toModel (0 : GoldilocksExt3) = 0 := by
  ext <;> exact Goldilocks.toZMod_zero

theorem toModel_one : toModel (1 : GoldilocksExt3) = 1 := by
  ext
  · exact Goldilocks.toZMod_one
  · exact Goldilocks.toZMod_zero
  · exact Goldilocks.toZMod_zero

theorem toModel_add (a b : GoldilocksExt3) : toModel (a + b) = toModel a + toModel b := by
  ext <;> exact Goldilocks.toZMod_add _ _

theorem toModel_sub (a b : GoldilocksExt3) : toModel (a - b) = toModel a - toModel b := by
  ext <;> exact Goldilocks.toZMod_sub _ _

theorem toModel_neg (a : GoldilocksExt3) : toModel (-a) = -toModel a := by
  ext <;> exact Goldilocks.toZMod_neg _

private theorem goldilocks_toZMod_add (a b : Goldilocks) :
    Goldilocks.toZMod (a.add b) = Goldilocks.toZMod a + Goldilocks.toZMod b :=
  Goldilocks.toZMod_add a b

private theorem goldilocks_toZMod_sub (a b : Goldilocks) :
    Goldilocks.toZMod (a.sub b) = Goldilocks.toZMod a - Goldilocks.toZMod b :=
  Goldilocks.toZMod_sub a b

private theorem goldilocks_toZMod_mul (a b : Goldilocks) :
    Goldilocks.toZMod (a.mul b) = Goldilocks.toZMod a * Goldilocks.toZMod b :=
  Goldilocks.toZMod_mul a b

private theorem goldilocks_toZMod_inv (a : Goldilocks) :
    Goldilocks.toZMod a.inv = (Goldilocks.toZMod a)⁻¹ :=
  Goldilocks.toZMod_inv a

/-- Karatsuba multiplication in `GoldilocksExt3` refines `Fp3Model` multiplication. -/
theorem toModel_mul (a b : GoldilocksExt3) : toModel (a * b) = toModel a * toModel b := by
  show toModel (GoldilocksExt3.mul a b) = toModel a * toModel b
  unfold GoldilocksExt3.mul toModel
  dsimp only
  ext <;>
    simp only [goldilocks_toZMod_add, goldilocks_toZMod_sub, goldilocks_toZMod_mul,
      Fp3Model.mul_c0, Fp3Model.mul_c1, Fp3Model.mul_c2] <;>
    ring

theorem toModel_adjugate (a : GoldilocksExt3) :
    toModel a.adjugate = (toModel a).adjugate := by
  unfold GoldilocksExt3.adjugate Fp3Model.adjugate toModel
  dsimp only
  ext <;>
    simp only [goldilocks_toZMod_add, goldilocks_toZMod_sub, goldilocks_toZMod_mul]

theorem toModel_norm (a : GoldilocksExt3) :
    Goldilocks.toZMod a.norm = (toModel a).norm := by
  unfold GoldilocksExt3.norm Fp3Model.norm
  dsimp only
  have hadj := toModel_adjugate a
  have hc0 : Goldilocks.toZMod a.adjugate.c0 = (toModel a).adjugate.c0 := congrArg Fp3Model.c0 hadj
  have hc1 : Goldilocks.toZMod a.adjugate.c1 = (toModel a).adjugate.c1 := congrArg Fp3Model.c1 hadj
  have hc2 : Goldilocks.toZMod a.adjugate.c2 = (toModel a).adjugate.c2 := congrArg Fp3Model.c2 hadj
  simp only [goldilocks_toZMod_add, goldilocks_toZMod_mul, hc0, hc1, hc2, toModel]

/-- Exact adjugate/norm inversion in `GoldilocksExt3` refines `Fp3Model.inv`. -/
theorem toModel_inv (a : GoldilocksExt3) : toModel a⁻¹ = (toModel a)⁻¹ := by
  show toModel (GoldilocksExt3.inv a) = Fp3Model.inv (toModel a)
  unfold GoldilocksExt3.inv GoldilocksExt3.inv? Fp3Model.inv
  dsimp only
  set n := ((a.c0.mul a.adjugate.c0).add (a.c2.mul a.adjugate.c1)).add (a.c1.mul a.adjugate.c2)
  have hn_eq : Goldilocks.toZMod n = (toModel a).norm := toModel_norm a
  have hbeq : (n == Goldilocks.zero) = true ↔ (toModel a).norm = 0 := by
    have hz : Goldilocks.zero.toZMod = 0 := Goldilocks.toZMod_zero
    rw [Goldilocks.beq_iff_toZMod, hn_eq, hz]
  by_cases h0 : (toModel a).norm = 0
  · rw [ite_eq_left (hbeq.mpr h0), ite_eq_left h0, Option.getD_none]
    exact toModel_zero
  · have hfalse : ¬ (n == Goldilocks.zero) = true := mt hbeq.mp h0
    rw [ite_eq_right hfalse, ite_eq_right h0, Option.getD_some]
    have hadj := toModel_adjugate a
    have hc0 : Goldilocks.toZMod a.adjugate.c0 = (toModel a).adjugate.c0 := congrArg Fp3Model.c0 hadj
    have hc1 : Goldilocks.toZMod a.adjugate.c1 = (toModel a).adjugate.c1 := congrArg Fp3Model.c1 hadj
    have hc2 : Goldilocks.toZMod a.adjugate.c2 = (toModel a).adjugate.c2 := congrArg Fp3Model.c2 hadj
    have hinvN : Goldilocks.toZMod n.inv = (toModel a).norm⁻¹ := by
      rw [goldilocks_toZMod_inv, hn_eq]
    ext
    · simp only [toModel, goldilocks_toZMod_mul, hc0, hinvN, Fp3Model.mul_c0,
        Fp3Model.embedHom_apply, Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2]
      ring
    · simp only [toModel, goldilocks_toZMod_mul, hc1, hinvN, Fp3Model.mul_c1,
        Fp3Model.embedHom_apply, Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2]
      ring
    · simp only [toModel, goldilocks_toZMod_mul, hc2, hinvN, Fp3Model.mul_c2,
        Fp3Model.embedHom_apply, Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2]
      ring

theorem beq_iff_toModel (a b : GoldilocksExt3) :
    (a == b) = true ↔ toModel a = toModel b := by
  change decide (a = b) = true ↔ toModel a = toModel b
  rw [decide_eq_true_eq]
  constructor
  · intro h; rw [h]
  · intro h
    cases a with | mk a0 a1 a2 =>
    cases b with | mk b0 b1 b2 =>
    have h0 := (Goldilocks.beq_iff_toZMod a0 b0).mpr (congrArg Fp3Model.c0 h)
    have h1 := (Goldilocks.beq_iff_toZMod a1 b1).mpr (congrArg Fp3Model.c1 h)
    have h2 := (Goldilocks.beq_iff_toZMod a2 b2).mpr (congrArg Fp3Model.c2 h)
    change decide (a0 = b0) = true at h0
    change decide (a1 = b1) = true at h1
    change decide (a2 = b2) = true at h2
    rw [decide_eq_true_eq] at h0 h1 h2
    subst h0; subst h1; subst h2
    rfl

end GoldilocksExt3

/-- **Refinement of executable `GoldilocksExt3` to `Fp3Model`.** -/
def goldilocksExt3_refines : Refines GoldilocksExt3 Fp3Model where
  toModel := GoldilocksExt3.toModel
  map_zero := GoldilocksExt3.toModel_zero
  map_one := GoldilocksExt3.toModel_one
  map_add := GoldilocksExt3.toModel_add
  map_sub := GoldilocksExt3.toModel_sub
  map_mul := GoldilocksExt3.toModel_mul
  map_neg := GoldilocksExt3.toModel_neg
  map_inv := GoldilocksExt3.toModel_inv
  beq_iff := GoldilocksExt3.beq_iff_toModel

/-- Refinement of executable `Goldilocks` into the base subfield of `Fp3Model`. -/
def goldilocksBase_refines_fp3 : Refines Goldilocks Fp3Model where
  toModel a := Fp3Model.embedHom (Goldilocks.toZMod a)
  map_zero := by rw [Goldilocks.toZMod_zero, map_zero]
  map_one := by rw [Goldilocks.toZMod_one, map_one]
  map_add a b := by rw [Goldilocks.toZMod_add, map_add]
  map_sub a b := by rw [Goldilocks.toZMod_sub, map_sub]
  map_mul a b := by rw [Goldilocks.toZMod_mul, map_mul]
  map_neg a := by rw [Goldilocks.toZMod_neg, map_neg]
  map_inv a := by
    change Fp3Model.embedHom (Goldilocks.toZMod a⁻¹) =
      Fp3Model.inv (Fp3Model.embedHom (Goldilocks.toZMod a))
    rw [Goldilocks.toZMod_inv]
    unfold Fp3Model.inv Fp3Model.norm Fp3Model.adjugate
    simp only [Fp3Model.embedHom_apply, Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2,
      add_zero, zero_mul, sub_zero, mul_zero]
    by_cases ha : Goldilocks.toZMod a = 0
    · simp only [ha, mul_zero, ite_true, Fp3Model.embed]
      ext <;> simp
    · have hcube : Goldilocks.toZMod a * (Goldilocks.toZMod a * Goldilocks.toZMod a) ≠ 0 :=
        mul_ne_zero ha (mul_ne_zero ha ha)
      rw [ite_eq_right hcube]
      ext
      · simp only [Fp3Model.mul_c0, Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2,
          mul_zero, add_zero]
        field_simp [ha]
      · simp
      · simp
  beq_iff a b := by
    rw [Goldilocks.beq_iff_toZMod]
    exact Fp3Model.embedHom_injective.eq_iff.symm

private def zmodToGoldilocks (x : GoldilocksField) : Goldilocks :=
  ⟨x.val.toUInt64, by
    have hx : x.val < Goldilocks.order := x.val_lt
    have hp_lt : Goldilocks.order < 2 ^ 64 := by unfold Goldilocks.order; decide
    have hto : x.val.toUInt64.toNat = x.val := by
      show x.val % 2 ^ 64 = x.val
      exact Nat.mod_eq_of_lt (by omega)
    rw [UInt64.lt_iff_toNat_lt, hto]
    exact hx⟩

private theorem toZMod_zmodToGoldilocks (x : GoldilocksField) :
    Goldilocks.toZMod (zmodToGoldilocks x) = x := by
  unfold Goldilocks.toZMod zmodToGoldilocks
  dsimp only
  have hx : x.val < Goldilocks.order := x.val_lt
  have hp_lt : Goldilocks.order < 2 ^ 64 := by unfold Goldilocks.order; decide
  have hto : x.val.toUInt64.toNat = x.val := by
    show x.val % 2 ^ 64 = x.val
    exact Nat.mod_eq_of_lt (by omega)
  rw [hto, ZMod.natCast_zmod_val]

/-- **Complete `Exec.FieldModel` for `Goldilocks` and `GoldilocksExt3` over `Fp3Model`.** -/
def goldilocksExt3_fieldModel : Exec.FieldModel Goldilocks GoldilocksExt3 Fp3Model where
  base := goldilocksBase_refines_fp3
  ext := goldilocksExt3_refines
  embed a := by
    change GoldilocksExt3.toModel ⟨a, Goldilocks.zero, Goldilocks.zero⟩ =
      Fp3Model.embedHom (Goldilocks.toZMod a)
    ext
    · rfl
    · exact Goldilocks.toZMod_zero
    · exact Goldilocks.toZMod_zero
  surj y :=
    ⟨⟨zmodToGoldilocks y.c0, zmodToGoldilocks y.c1, zmodToGoldilocks y.c2⟩, by
      ext <;> exact toZMod_zmodToGoldilocks _⟩

/-- **Complete `Exec.WellFormed` for `Goldilocks` / `GoldilocksExt3` on every
shape whose first domain has log-size `≤ 32`.** -/
theorem goldilocksExt3_wellFormed (params : FriParams) (shape : Fri.ClaimShape)
    (hlog : Fri.logMaxHeight params.logBlowup shape ≤ 32) :
    Exec.WellFormed goldilocksExt3_fieldModel params shape where
  prim :=
    (goldilocks_twoAdicGenerator_isPrimitiveRoot _ hlog).map_of_injective
      Fp3Model.embedHom_injective
  shift_ne := fun h => by
    change Fp3Model.embedHom Goldilocks.generator.toZMod = 0 at h
    exact goldilocks_cosetShift_ne_zero
      (Fp3Model.embedHom_injective (h.trans (map_zero Fp3Model.embedHom).symm))

/-! ## Unconditional executable verifier soundness over `Goldilocks` / `GoldilocksExt3` -/

namespace Exec

open Oracle OracleComp Fri
open PcsRbr (ClaimsFail)

/-- **Unconditional soundness of `Fri.verify` over Goldilocks cubic trinomial
`Fp3` (`X^3 - X - 1`, `|K| = p^3 ≈ 2^192`), up to the unique-decoding radius.**

No proximity hypotheses, no field-model assumptions, and no well-formedness
assumptions remain: only `logMaxHeight ≤ 32`, `logFinalHeight ≤ logMaxHeight`,
and `2 * δ + (1 / 2) ^ logBlowup ≤ 1`. -/
theorem goldilocksExt3_soundness_uniqueDecoding {D : Type} [DecidableEq D] [Inhabited D]
    [Fintype D] (params : FriParams) (shape : ClaimShape)
    (hlog : logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (Exec.OracleAnswer (D := D) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hlog)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Exec.Attempt Goldilocks GoldilocksExt3 D) :
    prob (fun res l =>
        (∃ f : ∀ x, Exec.OracleAnswer (D := D) goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog) x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            Exec.accepts goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog) f (attempt res.1) = true) ∧
        ClaimsFail (Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).ldt
          (Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).shift
          (1 - δ)
          ((Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).claims
            (Exec.view goldilocksExt3_fieldModel params shape
              (firstMessage (attempt res.1).commitments
                (attempt res.1).points (attempt res.1).values))
            (committedRow l)))
      (Exec.experiment goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hlog) adv attempt) [] ≤
      (Q + ((Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).rounds + 2) +
          (Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).verifierQueries) * εmax +
        ((max ((Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).batches +
          (Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).rounds + 2) +
            (Exec.modelParams goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog)).verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model]
    push_cast
    rfl
  exact CertiFri.Exec.soundness_uniqueDecoding goldilocksExt3_fieldModel params shape
    (goldilocksExt3_wellFormed params shape hlog) hheight hδ hrate
    (by rwa [hcard]) (by rwa [hcard]) hq hadv attempt

/-- **Knowledge soundness of `Fri.verify` over Goldilocks cubic trinomial `Fp3`.** -/
theorem goldilocksExt3_knowledge_soundness {D : Type} [DecidableEq D] [Inhabited D]
    [Fintype D] (params : FriParams) (shape : ClaimShape)
    (hlog : logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1)
    (hmargin : ∀ j ≤ numRounds params shape,
      (Exec.modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hlog)).numClaims j ≠ 0 →
      2 * δ + (1 / 2) ^ params.logBlowup +
        3 / 2 ^ (logMaxHeight params.logBlowup shape - j) ≤ 1)
    {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (Exec.OracleAnswer (D := D) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hlog)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Exec.Attempt Goldilocks GoldilocksExt3 D) :
    prob (fun res l =>
        (∃ f : ∀ x, Exec.OracleAnswer (D := D) goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog) x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            Exec.accepts goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog) f (attempt res.1) = true) ∧
        ∃ c ∈ claimRefs params.logBlowup shape,
          (Exec.extractColumn goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog) (1 - δ)
              (attempt res.1).commitments l c).eval
              (goldilocksExt3_fieldModel.ext.toModel ((attempt res.1).points.getD c.pointIdx 0)) ≠
            goldilocksExt3_fieldModel.ext.toModel ((attempt res.1).values.getD c.valueIdx 0))
      (Exec.experiment goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hlog) adv attempt) [] ≤
      (Q + ((Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).rounds + 2) +
          (Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).verifierQueries) * εmax +
        ((max ((Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).batches +
          (Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).rounds + 2) +
            (Exec.modelParams goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog)).verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model]
    push_cast
    rfl
  exact CertiFri.Exec.knowledge_soundness_of_rate goldilocksExt3_fieldModel params shape
    (goldilocksExt3_wellFormed params shape hlog) hheight hδ hrate hmargin
    (by rwa [hcard]) (by rwa [hcard]) hq hadv attempt

/-- **Binding of the commitment scheme over Goldilocks cubic trinomial `Fp3`.** -/
theorem goldilocksExt3_binding {D : Type} [DecidableEq D] [Inhabited D]
    [Fintype D] (params : FriParams) (shape : ClaimShape)
    (hlog : logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1)
    (hmargin : ∀ j ≤ numRounds params shape,
      (Exec.modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hlog)).numClaims j ≠ 0 →
      2 * δ + (1 / 2) ^ params.logBlowup +
        3 / 2 ^ (logMaxHeight params.logBlowup shape - j) ≤ 1)
    {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (Exec.OracleAnswer (D := D) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hlog)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt₁ attempt₂ : A → Exec.Attempt Goldilocks GoldilocksExt3 D) :
    prob (fun res l =>
        Exec.Accepted goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog) (attempt₁ res.1) l ∧
          Exec.Accepted goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog) (attempt₂ res.1) l ∧
          Exec.Conflict goldilocksExt3_fieldModel params shape (attempt₁ res.1) (attempt₂ res.1))
      (Exec.experiment₂ goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hlog) adv attempt₁ attempt₂) [] ≤
      2 * ((Q + 2 * (((Exec.modelParams goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog)).rounds + 2) +
            (Exec.modelParams goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog)).verifierQueries)) * εmax +
        ((max ((Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).batches +
          (Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + 2 * (((Exec.modelParams goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog)).rounds + 2) +
            (Exec.modelParams goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog)).verifierQueries)) ^ 2 /
          (4 * Fintype.card D)) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model]
    push_cast
    rfl
  exact CertiFri.Exec.binding_of_rate goldilocksExt3_fieldModel params shape
    (goldilocksExt3_wellFormed params shape hlog) hheight hδ hrate hmargin
    (by rwa [hcard]) (by rwa [hcard]) hq hadv attempt₁ attempt₂

end Exec

end CertiFri.P3
