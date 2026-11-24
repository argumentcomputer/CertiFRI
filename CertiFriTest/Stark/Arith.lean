import CertiFri.Stark.Logup
import CertiFriP3.GoldilocksExt

/-!
# The coordinate arithmetic of the lookup constraints

Checks of the pieces of `CertiFri/Stark` that compute in coordinates, over
Goldilocks and its quadratic extension: the image of a natural number, powers
by repeated squaring, the product of coordinate tuples against the product of
the extension, and the reassembly of an element from its coordinates.
-/

namespace CertiFriTest.Stark

open CertiFri CertiFri.Stark CertiFri.P3

/-- The coordinates of an extension element, embedded in the extension. -/
def coords (e : GoldilocksExt) : Array GoldilocksExt :=
  (ExtensionOps.toBasis (F := Goldilocks) e).map ExtensionOps.embed

def table : Array GoldilocksExt := basisTable Goldilocks

def x : GoldilocksExt := ⟨Goldilocks.ofNat 0x0123456789ABCDEF, Goldilocks.ofNat 0xFEDCBA9876543210⟩
def y : GoldilocksExt := ⟨Goldilocks.ofNat 0xFFFFFFFF00000000, Goldilocks.ofNat 3⟩
def z : GoldilocksExt := ⟨Goldilocks.ofNat 17, Goldilocks.ofNat 0x8000000000000000⟩

/-! ## Natural numbers and powers -/

#guard [0, 1, 2, 3, 255, 256, 2 ^ 32, 2 ^ 63 + 5, Goldilocks.order - 1, Goldilocks.order,
    Goldilocks.order + 7, 2 ^ 64 - 1, 2 ^ 70 + 3].all fun n =>
  (fieldOfNat n : Goldilocks) == Goldilocks.ofNat n

#guard (List.range 8).all fun k => fieldPowTwo x k == fieldPow x (2 ^ k)

/-! ## The basis and its structure constants -/

-- The basis is `1, X` with `X * X = 7`.
#guard (basisElem Goldilocks 0 : GoldilocksExt) == 1
#guard (basisElem Goldilocks 1 : GoldilocksExt) * basisElem Goldilocks 1
  == ExtensionOps.embed (Goldilocks.ofNat 7)
#guard table == #[1, 0, 0, 1, 0, 1, ExtensionOps.embed (Goldilocks.ofNat 7), 0]

/-! ## Products of coordinate tuples -/

-- On the coordinates of two elements, the product is that of the extension.
#guard [(x, y), (y, z), (x, x), (z, 1), (0, y)].all fun (a, b) =>
  coordMul 2 table (coords a) (coords b) == coords (a * b)

-- The coordinates may be any extension elements: the product is bilinear.
#guard coordMul 2 table #[x, y] #[z, x] == #[x * z + y * x * ExtensionOps.embed (Goldilocks.ofNat 7),
  x * x + y * z]

#guard coordMul 2 table (coordOne 2) #[x, y] == #[x, y]

/-! ## Reassembly -/

#guard [x, y, z, 0, 1].all fun e => fromExtBasis Goldilocks (coords e) == e

-- With extension coordinates: `c0 + c1 * X`.
#guard fromExtBasis Goldilocks #[x, y] == x + y * basisElem Goldilocks 1

/-! ## Groups of lookups -/

#guard lookupGroups 0 1 == 1 && lookupGroups 0 0 == 1 && lookupGroups 3 1 == 3
  && lookupGroups 3 2 == 2 && lookupGroups 4 2 == 2 && lookupGroups 5 8 == 1
  && lookupGroups 5 0 == 5

/-- A message and its multiplicity, in coordinates, for the checks of
`groupConstraint`. -/
def m0 : Array GoldilocksExt := #[x, y]
def m1 : Array GoldilocksExt := #[z, x]
def m2 : Array GoldilocksExt := #[y, y]
def diff : Array GoldilocksExt := #[z, y]

def mul (a b : Array GoldilocksExt) : Array GoldilocksExt := coordMul 2 table a b

def sub (a b : Array GoldilocksExt) : Array GoldilocksExt := #[a.getD 0 0 - b.getD 0 0, a.getD 1 0 - b.getD 1 0]

def scale (a : Array GoldilocksExt) (c : GoldilocksExt) : Array GoldilocksExt :=
  #[a.getD 0 0 * c, a.getD 1 0 * c]

-- No message: the constraint is the step itself.
#guard groupConstraint 2 table #[] #[] diff == diff

-- One message: `m * diff - c`.
#guard groupConstraint 2 table #[m0] #[z] diff == sub (mul m0 diff) #[z, 0]

-- Three messages: `m0 m1 m2 * diff - c0 m1 m2 - c1 m0 m2 - c2 m0 m1`.
#guard groupConstraint 2 table #[m0, m1, m2] #[x, y, z] diff
  == sub (sub (sub (mul (mul (mul m0 m1) m2) diff) (scale (mul m1 m2) x)) (scale (mul m0 m2) y))
    (scale (mul m0 m1) z)

end CertiFriTest.Stark
