import CertiFriP3.GoldilocksExt

/-!
# Tests of the quadratic extension of Goldilocks

Checks of `CertiFriP3/GoldilocksExt.lean`: the field laws on a few elements,
the embedding and the basis, and vectors computed by Plonky3 at revision
`3152b14a` (`BinomialExtensionField<Goldilocks, 2>`): sums, differences,
products, opposites, inverses, powers and products by base elements.

In the vectors an element is the pair of its coordinates as Plonky3's
`as_basis_coefficients_slice` lists them, and the operands may be words that
are not canonical; the results are canonical.
-/

namespace CertiFriTest.P3.GoldilocksExt

open CertiFri CertiFri.P3

/-- The coordinates of an element, as words. -/
abbrev E := UInt64 × UInt64

/-- The base element a word represents. -/
def g (word : UInt64) : Goldilocks := Goldilocks.ofUInt64 word

/-- The element with the given coordinates. -/
def e (coords : E) : GoldilocksExt := ⟨g coords.1, g coords.2⟩

/-- The coordinates of an element. -/
def coords (x : GoldilocksExt) : E := (x.c0.val, x.c1.val)

/-- The basis element `X`. -/
def X : GoldilocksExt := e (0, 1)

/-! ## The embedding and the basis -/

#guard ExtensionOps.degree Goldilocks GoldilocksExt = 2
#guard coords (0 : GoldilocksExt) = (0, 0) ∧ coords (1 : GoldilocksExt) = (1, 0)
#guard coords (default : GoldilocksExt) = (0, 0)
-- Plonky3: `EF::from(5)` has coordinates `(5, 0)`.
#guard coords (ExtensionOps.embed (g 5)) = (5, 0)
-- Plonky3: `ith_basis_element(1)` has coordinates `(0, 1)` and its square is `7`.
#guard coords (X * X) = (7, 0)
#guard X * X = ExtensionOps.embed GoldilocksExt.nonResidue
-- Plonky3: `from_basis_coefficients_fn(|i| 100 + i)` has coordinates `(100, 101)`.
#guard coords (ExtensionOps.ofBasis #[g 100, g 101]) = (100, 101)
#guard ExtensionOps.toBasis (F := Goldilocks) (e (100, 101)) = #[g 100, g 101]
#guard e (3, 4) = ExtensionOps.embed (g 3) + ExtensionOps.embed (g 4) * X
#guard ExtensionOps.ofBasis (F := Goldilocks) (ExtensionOps.toBasis (e (11, 12))) = e (11, 12)
#guard ExtensionOps.toBasis (ExtensionOps.ofBasis (EF := GoldilocksExt) #[g 11, g 12])
  = #[g 11, g 12]
-- Missing coordinates are zero; coordinates past the second are ignored.
#guard coords (ExtensionOps.ofBasis (#[] : Array Goldilocks)) = (0, 0)
#guard coords (ExtensionOps.ofBasis #[g 9]) = (9, 0)
#guard coords (ExtensionOps.ofBasis #[g 9, g 8, g 7]) = (9, 8)
#guard e (1, 2) ≠ e (1, 3) ∧ e (1, 2) == e (1, 2) ∧ !(e (1, 2) == e (2, 2))
#guard (0 : GoldilocksExt)⁻¹ = 0

/-! ## Field laws on a few elements -/

/-- Elements to check the laws on. -/
def samples : Array GoldilocksExt :=
  #[0, 1, X, e (7, 0), e (0xFFFFFFFF00000000, 0xFFFFFFFF00000000), e (0x100000000, 0xFFFFFFFF),
    e (0x0123456789ABCDEF, 0xFEDCBA9876543210), e (0x8000000000000000, 0x7FFFFFFFFFFFFFFF)]

#guard samples.all fun a => samples.all fun b =>
  a + b == b + a && a * b == b * a && a - b == a + -b && a - b + b == a

#guard samples.all fun a => samples.all fun b => samples.all fun c =>
  a * (b + c) == a * b + a * c && a * (b * c) == a * b * c

#guard samples.all fun a => a == 0 || (a * a⁻¹ == 1 && a⁻¹⁻¹ == a)

-- The multiplicative group has order `p^2 - 1`.
#guard samples.all fun a =>
  a == 0 || fieldPow a (Goldilocks.order ^ 2 - 1) == 1

/-! ## Against Plonky3 -/

/-- `(a, b, a + b, a - b, a * b)`, each element as its coordinates `(c0, c1)`. -/
def arithmeticVectors : Array (E × E × E × E × E) := #[
  ((0x0000000000000000, 0x0000000000000000), (0x0000000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x0000000000000000), (0x0000000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x0000000000000000)),
  ((0x0000000000000000, 0x0000000000000000), (0x0000000000000001, 0x0000000000000000),
    (0x0000000000000001, 0x0000000000000000), (0xffffffff00000000, 0x0000000000000000),
    (0x0000000000000000, 0x0000000000000000)),
  ((0x0000000000000000, 0x0000000000000000), (0x0000000000000000, 0x0000000000000001),
    (0x0000000000000000, 0x0000000000000001), (0x0000000000000000, 0xffffffff00000000),
    (0x0000000000000000, 0x0000000000000000)),
  ((0x0000000000000000, 0x0000000000000000), (0xffffffff00000000, 0xffffffff00000000),
    (0xffffffff00000000, 0xffffffff00000000), (0x0000000000000001, 0x0000000000000001),
    (0x0000000000000000, 0x0000000000000000)),
  ((0x0000000000000000, 0x0000000000000000), (0x0000000100000000, 0x00000000ffffffff),
    (0x0000000100000000, 0x00000000ffffffff), (0xfffffffe00000001, 0xfffffffe00000002),
    (0x0000000000000000, 0x0000000000000000)),
  ((0x0000000000000001, 0x0000000000000000), (0x0000000000000000, 0x0000000000000000),
    (0x0000000000000001, 0x0000000000000000), (0x0000000000000001, 0x0000000000000000),
    (0x0000000000000000, 0x0000000000000000)),
  ((0x0000000000000001, 0x0000000000000000), (0x0000000000000001, 0x0000000000000000),
    (0x0000000000000002, 0x0000000000000000), (0x0000000000000000, 0x0000000000000000),
    (0x0000000000000001, 0x0000000000000000)),
  ((0x0000000000000001, 0x0000000000000000), (0x0000000000000000, 0x0000000000000001),
    (0x0000000000000001, 0x0000000000000001), (0x0000000000000001, 0xffffffff00000000),
    (0x0000000000000000, 0x0000000000000001)),
  ((0x0000000000000001, 0x0000000000000000), (0xffffffff00000000, 0xffffffff00000000),
    (0x0000000000000000, 0xffffffff00000000), (0x0000000000000002, 0x0000000000000001),
    (0xffffffff00000000, 0xffffffff00000000)),
  ((0x0000000000000001, 0x0000000000000000), (0x0000000100000000, 0x00000000ffffffff),
    (0x0000000100000001, 0x00000000ffffffff), (0xfffffffe00000002, 0xfffffffe00000002),
    (0x0000000100000000, 0x00000000ffffffff)),
  ((0x0000000000000000, 0x0000000000000001), (0x0000000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x0000000000000001), (0x0000000000000000, 0x0000000000000001),
    (0x0000000000000000, 0x0000000000000000)),
  ((0x0000000000000000, 0x0000000000000001), (0x0000000000000001, 0x0000000000000000),
    (0x0000000000000001, 0x0000000000000001), (0xffffffff00000000, 0x0000000000000001),
    (0x0000000000000000, 0x0000000000000001)),
  ((0x0000000000000000, 0x0000000000000001), (0x0000000000000000, 0x0000000000000001),
    (0x0000000000000000, 0x0000000000000002), (0x0000000000000000, 0x0000000000000000),
    (0x0000000000000007, 0x0000000000000000)),
  ((0x0000000000000000, 0x0000000000000001), (0xffffffff00000000, 0xffffffff00000000),
    (0xffffffff00000000, 0x0000000000000000), (0x0000000000000001, 0x0000000000000002),
    (0xfffffffefffffffa, 0xffffffff00000000)),
  ((0x0000000000000000, 0x0000000000000001), (0x0000000100000000, 0x00000000ffffffff),
    (0x0000000100000000, 0x0000000100000000), (0xfffffffe00000001, 0xfffffffe00000003),
    (0x00000006fffffff9, 0x0000000100000000)),
  ((0xffffffff00000000, 0xffffffff00000000), (0x0000000000000000, 0x0000000000000000),
    (0xffffffff00000000, 0xffffffff00000000), (0xffffffff00000000, 0xffffffff00000000),
    (0x0000000000000000, 0x0000000000000000)),
  ((0xffffffff00000000, 0xffffffff00000000), (0x0000000000000001, 0x0000000000000000),
    (0x0000000000000000, 0xffffffff00000000), (0xfffffffeffffffff, 0xffffffff00000000),
    (0xffffffff00000000, 0xffffffff00000000)),
  ((0xffffffff00000000, 0xffffffff00000000), (0x0000000000000000, 0x0000000000000001),
    (0xffffffff00000000, 0x0000000000000000), (0xffffffff00000000, 0xfffffffeffffffff),
    (0xfffffffefffffffa, 0xffffffff00000000)),
  ((0xffffffff00000000, 0xffffffff00000000), (0xffffffff00000000, 0xffffffff00000000),
    (0xfffffffeffffffff, 0xfffffffeffffffff), (0x0000000000000000, 0x0000000000000000),
    (0x0000000000000008, 0x0000000000000002)),
  ((0xffffffff00000000, 0xffffffff00000000), (0x0000000100000000, 0x00000000ffffffff),
    (0x00000000ffffffff, 0x00000000fffffffe), (0xfffffffe00000000, 0xfffffffe00000001),
    (0xfffffff700000008, 0xfffffffd00000002)),
  ((0x0000000100000000, 0x00000000ffffffff), (0x0000000000000000, 0x0000000000000000),
    (0x0000000100000000, 0x00000000ffffffff), (0x0000000100000000, 0x00000000ffffffff),
    (0x0000000000000000, 0x0000000000000000)),
  ((0x0000000100000000, 0x00000000ffffffff), (0x0000000000000001, 0x0000000000000000),
    (0x0000000100000001, 0x00000000ffffffff), (0x00000000ffffffff, 0x00000000ffffffff),
    (0x0000000100000000, 0x00000000ffffffff)),
  ((0x0000000100000000, 0x00000000ffffffff), (0x0000000000000000, 0x0000000000000001),
    (0x0000000100000000, 0x0000000100000000), (0x0000000100000000, 0x00000000fffffffe),
    (0x00000006fffffff9, 0x0000000100000000)),
  ((0x0000000100000000, 0x00000000ffffffff), (0xffffffff00000000, 0xffffffff00000000),
    (0x00000000ffffffff, 0x00000000fffffffe), (0x0000000100000001, 0x0000000100000000),
    (0xfffffff700000008, 0xfffffffd00000002)),
  ((0x0000000100000000, 0x00000000ffffffff), (0x0000000100000000, 0x00000000ffffffff),
    (0x0000000200000000, 0x00000001fffffffe), (0x0000000000000000, 0x0000000000000000),
    (0xfffffff900000000, 0xfffffffeffffffff)),
  ((0x975835de1c9756ce, 0xbfc846100bfc1e42), (0x987bbcbfdd7e532f, 0xc3f2827affe7f664),
    (0x2fd3f29efa15a9fc, 0x83bac88c0be414a5), (0xfedc791d3f1903a0, 0xfbd5c3940c1427df),
    (0x84b455bc692e52ce, 0x19e1776e68dcd616)),
  ((0x4fc446b53f17fb29, 0x58bc3cb37bc7b2b3), (0xb9f24f7bae4a6586, 0xbd34d3aef603e583),
    (0x09b69631ed6260ae, 0x15f1106371cb9835), (0x95d1f73890cd95a4, 0x9b87690385c3cd31),
    (0x040a927e2074caed, 0x7752311cfc5892d4)),
  ((0x401478bc5887ccff, 0xba450a33ef6ff86c), (0x56e84498e8b0e635, 0x701560ad31bb9977),
    (0x96fcbd554138b334, 0x2a5a6ae2212b91e2), (0xe92c34226fd6e6cb, 0x4a2fa986bdb45ef5),
    (0xc5c8750fe02afa9f, 0x048511b0b7fd23ed)),
  ((0x8e4858b561b10361, 0x5fb1940eb8cbf1ae), (0xee979f2730a45df3, 0x34116e681eda3219),
    (0x7cdff7dd92556153, 0x93c30276d7a623c7), (0x9fb0b98d310ca56f, 0x2ba025a699f1bf95),
    (0xb13d8d35dff8d332, 0x3d8faf81330d87fa)),
  ((0x333c04e09d9ae712, 0x5d3e47ecad6ef3d4), (0x60b92d2a699b5d52, 0x35ceedaace1296d5),
    (0x93f5320b07364464, 0x930d35977b818aa9), (0xd282d7b533ff89c1, 0x276f5a41df5c5cff),
    (0x1ca47b01c3c1c248, 0xb1d9e1d096a1b591)),
  ((0x0c56cd8a4cfc66c1, 0x8704799a02f1631d), (0x6189abe28d8e28b1, 0x54a802d271b82a96),
    (0x6de0796cda8a8f72, 0xdbac7c6c74a98db3), (0xaacd21a6bf6e3e11, 0x325c76c791393887),
    (0x670ec94c72cf3a22, 0x53202ff10dbb1e50)),
  ((0xea8bbd50dcc507e4, 0xbd80b4cb2ebfa252), (0x8675d8d1e5ceef8e, 0x9ea9566e32510720),
    (0x71019623c293f771, 0x5c2a0b3a6110a971), (0x6415e47ef6f61856, 0x1ed75e5cfc6e9b32),
    (0xf47eaf3c37628e19, 0x080154c11e7666af)),
  ((0x02fc1efe0fccd72d, 0x4d06d2051c9d6d82), (0xddfcd92ab490c639, 0x9a7aa72430f9ca55),
    (0xe0f8f828c45d9d66, 0xe78179294d9737d7), (0x24ff45d25b3c10f5, 0xb28c2adfeba3a32e),
    (0x4e4a51cf0f5852e7, 0xc578111f32d1918b)),
  ((0x444bcaba22bb690f, 0x57c883255f0f9e24), (0xe2311b535f1fb0a9, 0x594dac74e9d05dd3),
    (0x267ce60e81db19b7, 0xb1162f9a48dffbf7), (0x621aaf65c39bb867, 0xfe7ad6af753f4052),
    (0x2fdd84e0d965a1df, 0x1f78a4f4b24d735b)),
  ((0x47602afae0d99c3c, 0x02bdde9d861af7d1), (0xe6efa7fa171cc347, 0x391cf0d00f6269a1),
    (0x2e4fd2f5f7f65f82, 0x3bdacf6d957d6172), (0x607082ffc9bcd8f6, 0xc9a0edcc76b88e31),
    (0xaf862a4d5e563131, 0xd5734e5de8f3f867)),
  ((0xcb0714a2c315d7be, 0x2b3757448c2f7e6a), (0x021aa27732571887, 0xad98bc04e64e33b7),
    (0xcd21b719f56cf045, 0xd8d01349727db221), (0xc8ec722b90bebf37, 0x7d9e9b3ea5e14ab4),
    (0x074da1d2e257cb76, 0x6d663cb8e07af111)),
  ((0xd6bc3af4ce1a0e50, 0x6faa36ceb3ac305a), (0xfac91851b0a82be1, 0xd9d9fe7c79a5c5a0),
    (0xd18553477ec23a30, 0x4984354c2d51f5f9), (0xdbf322a21d71e270, 0x95d038513a066abb),
    (0x7545a14c8b8d5af7, 0x2f3c30e7118730e8)),
  ((0x2cddd68e22c9399e, 0x8cb4863827a66cd3), (0x789e2d53857ddf21, 0xc069b999d14cb5d7),
    (0xa57c03e1a84718bf, 0x4d1e3fd2f8f322a9), (0xb43fa9399d4b5a7e, 0xcc4acc9d5659b6fd),
    (0x312e2ea5ec684599, 0x8f44da4d5c75ef13)),
  ((0x51595134ecf9dcc7, 0x9839e745b98cdaa6), (0x99865fd6f4009b0d, 0x3b3a8762bfcb6581),
    (0xeadfb10be0fa77d4, 0xd3746ea879584027), (0xb7d2f15cf8f941bb, 0x5cff5fe2f9c17525),
    (0x1a3835325359642a, 0xdedbc9ceeaf513a7)),
  ((0x98928208b19cbbfe, 0x5b27a18e385a182b), (0x66fddff5b4309191, 0x2b4319a4d8416088),
    (0xff9061fe65cd4d8f, 0x866abb33109b78b3), (0x3194a212fd6c2a6d, 0x2fe487e96018b7a3),
    (0xdc88442a5759b8bc, 0x7b4b458b433495dd)),
  ((0xe5afeade560a4ebb, 0x5dd5d1bec99ae953), (0xe8c387e8e1f9a484, 0x530a8475bf4879d0),
    (0xce7372c83803f33e, 0xb0e0563488e36323), (0xfcec62f47410aa38, 0x0acb4d490a526f83),
    (0xef5bfdbced315645, 0xd944181a817cdfe8)),
  ((0x017536a38c412830, 0x9d84c218a3dff3bc), (0x98e99ec22e29a257, 0x2d57fe002233bec5),
    (0x9a5ed565ba6aca87, 0xcadcc018c613b281), (0x688b97e05e1785da, 0x702cc41881ac34f7),
    (0xb98725a52754940e, 0xb5e891ec357787bc)),
  ((0x94dd0dca0260488c, 0xd0e5c3767c8efa67), (0x3f1ff7f7fc353c04, 0x1f0a010d1838e891),
    (0xd3fd05c1fe958490, 0xefefc48394c7e2f8), (0x55bd15d2062b0c88, 0xb1dbc269645611d6),
    (0xef4c7e4ea9eeb159, 0x40f2d824a9f7f3a3)),
  ((0x867c64929b90a0c3, 0xe8ba0b20f5093837), (0xb1bafb13d6cdfc8b, 0x374a9fea566dbddd),
    (0x38375fa7725e9d4d, 0x2004ab0c4b76f613), (0xd4c1697dc4c2a439, 0xb16f6b369e9b7a5a),
    (0x6ca65ac51e21d352, 0xb56d3f64259a12eb)),
  ((0x6d6bae6a85f5d90d, 0x600a293bce34ce56), (0x8c850dcecaf91228, 0xc259cac4e698bf9c),
    (0xf9f0bc3950eeeb35, 0x2263f401b4cd8df1), (0xe0e6a09abafcc6e6, 0x9db05e75e79c0ebb),
    (0x6e221858ab25245a, 0xb7d216dbdaa79c39)),
  ((0xd0140f443f63ef0b, 0x5eb31425ab9a718f), (0x2c256428715e16f4, 0x13132ce05621168c),
    (0xfc39736cb0c205ff, 0x71c6410601bb881b), (0xa3eeab1bce05d817, 0x4b9fe74555795b03),
    (0x63f87ba0d4485ec6, 0xb58d241e00919b1d)),
  ((0x4e10e46c6ed5e249, 0x7a969a03967b7748), (0xf6f2e3414c8f366d, 0xee14a5ac1daa9573),
    (0x4503c7aebb6518b5, 0x68ab3fb0b4260cba), (0x571e012a2246abdd, 0x8c81f45678d0e1d6),
    (0xdc2a9442c10de4b4, 0x4f6c157e4fc1d16d)),
  ((0xc27b9fafae3e2397, 0xef085b3b4ba484cc), (0x5224d2453bf55d34, 0xdc6ae1f52acfaac4),
    (0x14a071f5ea3380ca, 0xcb733d3176742f8f), (0x7056cd6a7248c663, 0x129d794620d4da08),
    (0x24c275f457515af0, 0x10e6b89a2dbdb101)),
  ((0x62755ef4b6130fd8, 0x3aec667ee4c337d8), (0x73e3f10efbe0f760, 0x556a135c797831bd),
    (0xd6595003b1f40738, 0x905679db5e3b6995), (0xee916de4ba321879, 0xe58253216b4b061c),
    (0x91d467d4181711da, 0x501bbea869841457)),
  ((0x912f822b1e8fe1e4, 0xf8606cc314fb6b96), (0x2067fe22cf322e4f, 0x8bc513e5906a18ab),
    (0xb197804dedc21033, 0x842580a9a5658440), (0x70c784084f5db395, 0x6c9b58dd849152eb),
    (0xaa7dde476004d45d, 0x5b756662518132f9))]

/-- `(a, -a, a⁻¹)` for nonzero `a`. -/
def unaryVectors : Array (E × E × E) := #[
  ((0x0000000000000001, 0x0000000000000000), (0xffffffff00000000, 0x0000000000000000),
    (0x0000000000000001, 0x0000000000000000)),
  ((0x0000000000000000, 0x0000000000000001), (0x0000000000000000, 0xffffffff00000000),
    (0x0000000000000000, 0x249249246db6db6e)),
  ((0xffffffff00000000, 0xffffffff00000000), (0x0000000000000001, 0x0000000000000001),
    (0xd555555480000001, 0x2aaaaaaa80000000)),
  ((0x0000000100000000, 0x00000000ffffffff), (0xfffffffe00000001, 0xfffffffe00000002),
    (0xb823ee083ee08fb9, 0x08fb823eb823ee09)),
  ((0xb1ea028886fb6b3c, 0xedf1072d5d60db98), (0x4e15fd76790494c5, 0x120ef8d1a29f2469),
    (0x8bf965b4ae11d442, 0xfc08f922865fccf5)),
  ((0x5dae3e9624291a41, 0xd82f63b48106a743), (0xa251c168dbd6e5c0, 0x27d09c4a7ef958be),
    (0x82b0173846ff595e, 0x11eb292837c30409)),
  ((0x4ecfebcf44055533, 0x65f6f9091847bab3), (0xb130142fbbfaaace, 0x9a0906f5e7b8454e),
    (0x9814463ffb1259ab, 0xe11230401b0f4ed3)),
  ((0xabd84c2da396cf60, 0xe15e79ca53942f21), (0x5427b3d15c6930a1, 0x1ea18634ac6bd0e0),
    (0x2c2b18173ee17bac, 0x46b8121770b8dde3)),
  ((0x000bbe1e4ae78dca, 0xc47e438593c64693), (0xfff441e0b5187237, 0x3b81bc796c39b96e),
    (0xef76404cd9a43982, 0xaff9bea5565e375f)),
  ((0xb7422dfe9e97ec96, 0x1eedc9af7adfc473), (0x48bdd2006168136b, 0xe112364f85203b8e),
    (0x9b1b82747b1f5305, 0x8b14a2f234d9658e)),
  ((0x63c102baca4fc607, 0xcb9f82c5fc0a9cbf), (0x9c3efd4435b039fa, 0x34607d3903f56342),
    (0x8466d5b2f921b0a3, 0x25d5b535f25b5d44)),
  ((0x97a55f31057342e0, 0xf0f846e916acde9c), (0x685aa0cdfa8cbd21, 0x0f07b915e9532165),
    (0x6fa597caf24a00be, 0xefc5b0602f7a833c)),
  ((0xc40291c88688d51b, 0x19588dc18f57c3d0), (0x3bfd6e3679772ae6, 0xe6a7723d70a83c31),
    (0x853d8e016a03f640, 0x3931be585d0538ae)),
  ((0xff19ef7d5b51d5eb, 0x5520eee2ed2a3111), (0x00e61081a4ae2a16, 0xaadf111c12d5cef0),
    (0x3ed95102a8334563, 0x76aa6fabfdafc70d)),
  ((0x9f9678ed02f19714, 0x1eeb922d0a84940d), (0x60698711fd0e68ed, 0xe1146dd1f57b6bf4),
    (0x7a32cc505d7deba0, 0x07e79fa09003581b)),
  ((0x69d0a0f25f40d7c1, 0x8923a1d574aee5be), (0x962f5f0ca0bf2840, 0x76dc5e298b511a43),
    (0x7e1a70d9dc10b975, 0x650d1ac2ef45c4eb)),
  ((0xe17fd85bdc0247e6, 0x630342cb274fee6d), (0x1e8027a323fdb81b, 0x9cfcbd33d8b01194),
    (0x145a832fc0095f6f, 0xd44a7e826d4e6763)),
  ((0x4495775e6dfd8d8f, 0x7ace0e6a05997d63), (0xbb6a88a092027272, 0x8531f194fa66829e),
    (0x8c7da6fc32c842f2, 0x027c68408e4eb9a9)),
  ((0x755cf36e6886f3e8, 0x70d935326b3c16c5), (0x8aa30c9097790c19, 0x8f26cacc94c3e93c),
    (0x258e7022835c9117, 0x87c477d0a2ed38a9)),
  ((0x6a109bc5a16570af, 0x4f16bd1da528300b), (0x95ef64395e9a8f52, 0xb0e942e15ad7cff6),
    (0x350466e144751c52, 0x76932a021e800fd8)),
  ((0xeca8be5ea6a8a61a, 0xa7fad5258a164356), (0x135741a0595759e7, 0x58052ad975e9bcab),
    (0x1942c8e005fd2dc8, 0x39c8f47d4d9b261d)),
  ((0x59927723f6098ebc, 0x39f3cf6ddbda2c06), (0xa66d88db09f67145, 0xc60c30912425d3fb),
    (0x3178d2f69421cc62, 0x51cfba5d3b3e31cb)),
  ((0x16419014ab48c979, 0x8665a9e658864d2c), (0xe9be6fea54b73688, 0x799a5618a779b2d5),
    (0xa809f18543db103c, 0xf3b7ad1fccc24327)),
  ((0x8be312d166bdfec6, 0xd243196bd780f8c7), (0x741ced2d9942013b, 0x2dbce693287f073a),
    (0xb4d9d07cf4a03c71, 0xf2085d52dfd4ac53))]

/-- `(a, n, a ^ n)`. -/
def powerVectors : Array (E × Nat × E) := #[
  ((0x4bf251135161e2a8, 0xc53959bd3f96aa5a), 0,
    (0x0000000000000001, 0x0000000000000000)),
  ((0xf4e17231ecea8c61, 0xa58c3dd44f44230e), 1,
    (0xf4e17231ecea8c61, 0xa58c3dd44f44230e)),
  ((0xabe0e436c861fb73, 0xf2042ab74651aaeb), 2,
    (0x1575bd43eb4c119a, 0x21cfc5cb2a3f301f)),
  ((0x5fd76a559c113292, 0x35e3b5e5cbebd691), 5,
    (0x0ad7aa848361fed8, 0x5f5115e766627e80)),
  ((0x03811ac1bb42d5b0, 0xb669b6fcc114a378), 4294967297,
    (0x3b2c097abb0efde6, 0xc40e74cba51e7d60)),
  ((0xae01825f2ca91fda, 0x3da49499bd18432b), 18446744069414584321,
    (0xae01825f2ca91fda, 0xc25b6b6542e7bcd6)),
  ((0x363a91e9b7ef55bb, 0xe3d73f420e511c73), 18446744073709551615,
    (0x0448ad3940103f05, 0x2fd9fbda2aa74f14))]

/-- `(a, e, EF::from(a) * e)`: the base element `a` times the extension element
`e`. -/
def embedVectors : Array (UInt64 × E × E) := #[
  (0x0e4694e1f0ad58c9, (0xb86641752f94c77c, 0x2e6c4f9ba30a2a99),
    (0x5c4e7b6c592daa10, 0x722aaa9ada184214)),
  (0x05fca9529c9addb4, (0xf87916ddb06bb977, 0xd1b2f53b9035607a),
    (0x9061bd362512fe96, 0xe91158c0765beabb)),
  (0x25b30ea66c194033, (0xe166ad40111a11ea, 0x539141003a77d260),
    (0xed3dbbcfb7d473f3, 0x98d7d075d8e4954a)),
  (0xfd5f051d8ffac562, (0xcf6b2d01ff1d1768, 0x071eb34fa43396ae),
    (0x9a01713579e1798d, 0x1a687a0633c2aff2)),
  (0x1227044a45ccf28e, (0x47c70d73ca245004, 0x7544d558906b789d),
    (0x8169240325b511b5, 0xaa147a5a45928e76)),
  (0x671138797bff24dd, (0xb3a89d4d7ef1ffad, 0xe1b5b04c5cc01d63),
    (0x050447295e82f37c, 0xa23ae96348914487)),
  (0xbaf40c6b2d4c0d10, (0x91e0485d1dc380e7, 0x684b68b0ad6526b2),
    (0xded1f1a2087cfaf6, 0x41f753af1ab53485)),
  (0xd5b5ae9724916278, (0xeac4b0fb936b7fdf, 0x8949df4fe1bb67d4),
    (0xaf89ec588749fe84, 0x4b5db3231bcd083a))]

#guard arithmeticVectors.size = 50
#guard arithmeticVectors.all fun (a, b, sum, difference, product) =>
  coords (e a + e b) == sum && coords (e a - e b) == difference && coords (e a * e b) == product

#guard unaryVectors.size = 24
#guard unaryVectors.all fun (a, opposite, inverse) =>
  coords (-e a) == opposite && coords (e a)⁻¹ == inverse

#guard powerVectors.size = 7
#guard powerVectors.all fun (a, n, power) => coords (fieldPow (e a) n) == power

#guard embedVectors.size = 8
#guard embedVectors.all fun (a, b, product) =>
  coords (ExtensionOps.embed (g a) * e b) == product

end CertiFriTest.P3.GoldilocksExt
