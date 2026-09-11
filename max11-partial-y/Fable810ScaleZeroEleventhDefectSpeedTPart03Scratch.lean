import Fable810ScaleZeroEleventhDefectSpeedTPart02Scratch

/-! # Scale-zero eleventh defect for the normalized `(8,10)`, `H = 0` leaf

The tenth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first ten octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, `h³⁵`, `h⁴²`, `h⁴⁹`, `h⁵⁶`, `h⁶³`, `h⁷⁰`, and `h⁷⁷`.  This file
consumes the next unused Keller coefficient of the same monic
octic-decic depression: the degree-`5` Jacobian row is
`6 R G' + 5 S F' + 4 T E' + 3 U D' + 2 V C' + W B'
- F S' - 2 E T' - 3 D U' - 4 C V' - 5 B W' - 6 A X' = 0`.  The
corresponding twelfth cleared polynomial defect of weight eighty-four
is likewise a ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`84` defect itself.  Root-evaluation from a scale-two
face is unavailable, because a nonzero constant has no finite root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`4` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

/-! ## Literal next Keller coefficient -/

section Depression810TwelfthClearing

variable {F : Type*} [Field F] [CharZero F]

-- Fix the carrier of standard arithmetic while elaborating the scalar identity.
local infixl:65 (priority := high) " + " => (HAdd.hAdd (α := F) (β := F) (γ := F))
local infixl:65 (priority := high) " - " => (HSub.hSub (α := F) (β := F) (γ := F))
local infixl:70 (priority := high) " * " => (HMul.hMul (α := F) (β := F) (γ := F))
local infixl:70 (priority := high) " / " => (HDiv.hDiv (α := F) (β := F) (γ := F))
local infixr:80 (priority := high) " ^ " => (HPow.hPow (α := F) (β := Nat) (γ := F))

set_option maxHeartbeats 64000000 in
/-- Clearing the first integral `μ` of the degree-`5` row against `h⁸⁴`
on the ninth-power face. -/
theorem twelfthDefect_eq_clearedMu810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (17179869184 : F) * h ^ 84 *
        muResidual810
          (depressedL810 h (octicDepressionR810 h a7) b9)
          (depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
          (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
          (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
          (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
            a1)
          (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
            a1 a0)
          (depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
          (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
          (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
          (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
          (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3)
          (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3 b2)
          (depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3 b2 b1) =
    (203408205 : F) * a7 ^ 12
    - (801115392 : F) * h ^ 6 * a7 ^ 10 * b8
    - (199709874 : F) * h ^ 7 * a7 ^ 11 * lambda
    - (1502091360 : F) * h ^ 8 * a7 ^ 10 * a6
    + (801115392 : F) * h ^ 14 * a7 ^ 9 * b7
    + (8240044032 : F) * h ^ 14 * a7 ^ 8 * a6 * b8
    + (2253137040 : F) * h ^ 15 * a7 ^ 9 * a6 * lambda
    + (1573619520 : F) * h ^ 16 * a7 ^ 9 * a5
    + (1287506880 : F) * h ^ 16 * a7 ^ 8 * a6 ^ 2
    - (797423616 : F) * h ^ 22 * a7 ^ 8 * b6
    - (7442620416 : F) * h ^ 22 * a7 ^ 7 * a6 * b7
    - (8505851904 : F) * h ^ 22 * a7 ^ 7 * a5 * b8
    - (29770481664 : F) * h ^ 22 * a7 ^ 6 * a6 ^ 2 * b8
    - (2317512384 : F) * h ^ 23 * a7 ^ 8 * a5 * lambda
    - (9270049536 : F) * h ^ 23 * a7 ^ 7 * a6 ^ 2 * lambda
    - (1661299200 : F) * h ^ 24 * a7 ^ 8 * a4
    - (1329039360 : F) * h ^ 24 * a7 ^ 7 * a6 * a5
    + (12404367360 : F) * h ^ 24 * a7 ^ 6 * a6 ^ 3
    + (787578880 : F) * h ^ 30 * a7 ^ 7 * b5
    + (6615662592 : F) * h ^ 30 * a7 ^ 6 * a6 * b6
    + (7718273024 : F) * h ^ 30 * a7 ^ 6 * a5 * b7
    + (8820883456 : F) * h ^ 30 * a7 ^ 6 * a4 * b8
    + (23154819072 : F) * h ^ 30 * a7 ^ 5 * a6 ^ 2 * b7
    + (52925300736 : F) * h ^ 30 * a7 ^ 5 * a6 * a5 * b8
    + (44104417280 : F) * h ^ 30 * a7 ^ 4 * a6 ^ 3 * b8
    + (2392270848 : F) * h ^ 31 * a7 ^ 7 * a4 * lambda
    + (16745895936 : F) * h ^ 31 * a7 ^ 6 * a6 * a5 * lambda
    + (16745895936 : F) * h ^ 31 * a7 ^ 5 * a6 ^ 3 * lambda
    + (1772052480 : F) * h ^ 32 * a7 ^ 7 * a3
    - (37213102080 : F) * h ^ 32 * a7 ^ 5 * a6 ^ 2 * a5
    - (31010918400 : F) * h ^ 32 * a7 ^ 4 * a6 ^ 4
    - (767033344 : F) * h ^ 38 * a7 ^ 6 * b4
    - (5752750080 : F) * h ^ 38 * a7 ^ 5 * a6 * b5
    - (6903300096 : F) * h ^ 38 * a7 ^ 5 * a5 * b6
    - (8053850112 : F) * h ^ 38 * a7 ^ 5 * a4 * b7
    - (9204400128 : F) * h ^ 38 * a7 ^ 5 * a3 * b8
    - (17258250240 : F) * h ^ 38 * a7 ^ 4 * a6 ^ 2 * b6
    - (40269250560 : F) * h ^ 38 * a7 ^ 4 * a6 * a5 * b7
    - (46022000640 : F) * h ^ 38 * a7 ^ 4 * a6 * a4 * b8
    - (23011000320 : F) * h ^ 38 * a7 ^ 4 * a5 ^ 2 * b8
    - (26846167040 : F) * h ^ 38 * a7 ^ 3 * a6 ^ 3 * b7
    - (92044001280 : F) * h ^ 38 * a7 ^ 3 * a6 ^ 2 * a5 * b8
    - (23011000320 : F) * h ^ 38 * a7 ^ 2 * a6 ^ 4 * b8
    - (2480873472 : F) * h ^ 39 * a7 ^ 6 * a3 * lambda
    - (14885240832 : F) * h ^ 39 * a7 ^ 5 * a6 * a4 * lambda
    - (7442620416 : F) * h ^ 39 * a7 ^ 5 * a5 ^ 2 * lambda
    - (37213102080 : F) * h ^ 39 * a7 ^ 4 * a6 ^ 2 * a5 * lambda
    - (12404367360 : F) * h ^ 39 * a7 ^ 3 * a6 ^ 4 * lambda
    - (1917583360 : F) * h ^ 40 * a7 ^ 6 * a2
    + (1438187520 : F) * h ^ 40 * a7 ^ 5 * a6 * a3
    + (1438187520 : F) * h ^ 40 * a7 ^ 5 * a5 * a4
    + (35954688000 : F) * h ^ 40 * a7 ^ 4 * a6 ^ 2 * a4
    + (35954688000 : F) * h ^ 40 * a7 ^ 4 * a6 * a5 ^ 2
    + (91085209600 : F) * h ^ 40 * a7 ^ 3 * a6 ^ 3 * a5
    + (20134625280 : F) * h ^ 40 * a7 ^ 2 * a6 ^ 5
    + (726663168 : F) * h ^ 46 * a7 ^ 5 * b3
    + (4844421120 : F) * h ^ 46 * a7 ^ 4 * a6 * b4
    + (6055526400 : F) * h ^ 46 * a7 ^ 4 * a5 * b5
    + (7266631680 : F) * h ^ 46 * a7 ^ 4 * a4 * b6
    + (8477736960 : F) * h ^ 46 * a7 ^ 4 * a3 * b7
    + (9688842240 : F) * h ^ 46 * a7 ^ 4 * a2 * b8
    + (12111052800 : F) * h ^ 46 * a7 ^ 3 * a6 ^ 2 * b5
    + (29066526720 : F) * h ^ 46 * a7 ^ 3 * a6 * a5 * b6
    + (33910947840 : F) * h ^ 46 * a7 ^ 3 * a6 * a4 * b7
    + (38755368960 : F) * h ^ 46 * a7 ^ 3 * a6 * a3 * b8
    + (16955473920 : F) * h ^ 46 * a7 ^ 3 * a5 ^ 2 * b7
    + (38755368960 : F) * h ^ 46 * a7 ^ 3 * a5 * a4 * b8
    + (14533263360 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 3 * b6
    + (50866421760 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * a5 * b7
    + (58133053440 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * a4 * b8
    + (58133053440 : F) * h ^ 46 * a7 ^ 2 * a6 * a5 ^ 2 * b8
    + (8477736960 : F) * h ^ 46 * a7 * a6 ^ 4 * b7
    + (38755368960 : F) * h ^ 46 * a7 * a6 ^ 3 * a5 * b8
    + (1937768448 : F) * h ^ 46 * a6 ^ 5 * b8
    + (2588737536 : F) * h ^ 47 * a7 ^ 5 * a2 * lambda
    + (12943687680 : F) * h ^ 47 * a7 ^ 4 * a6 * a3 * lambda
    + (12943687680 : F) * h ^ 47 * a7 ^ 4 * a5 * a4 * lambda
    + (25887375360 : F) * h ^ 47 * a7 ^ 3 * a6 ^ 2 * a4 * lambda
    + (25887375360 : F) * h ^ 47 * a7 ^ 3 * a6 * a5 ^ 2 * lambda
    + (25887375360 : F) * h ^ 47 * a7 ^ 2 * a6 ^ 3 * a5 * lambda
    + (2588737536 : F) * h ^ 47 * a7 * a6 ^ 5 * lambda
    + (2119434240 : F) * h ^ 48 * a7 ^ 5 * a1
    - (3027763200 : F) * h ^ 48 * a7 ^ 4 * a6 * a2
    - (3027763200 : F) * h ^ 48 * a7 ^ 4 * a5 * a3
    - (1513881600 : F) * h ^ 48 * a7 ^ 4 * a4 ^ 2
    - (33305395200 : F) * h ^ 48 * a7 ^ 3 * a6 ^ 2 * a3
    - (66610790400 : F) * h ^ 48 * a7 ^ 3 * a6 * a5 * a4
    - (11101798400 : F) * h ^ 48 * a7 ^ 3 * a5 ^ 3
    - (60555264000 : F) * h ^ 48 * a7 ^ 2 * a6 ^ 3 * a4
    - (90832896000 : F) * h ^ 48 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2
    - (43902566400 : F) * h ^ 48 * a7 * a6 ^ 4 * a5
    - (1917583360 : F) * h ^ 48 * a6 ^ 6
    - (645922816 : F) * h ^ 54 * a7 ^ 4 * b2
    - (3875536896 : F) * h ^ 54 * a7 ^ 3 * a6 * b3
    - (5167382528 : F) * h ^ 54 * a7 ^ 3 * a5 * b4
    - (6459228160 : F) * h ^ 54 * a7 ^ 3 * a4 * b5
    - (7751073792 : F) * h ^ 54 * a7 ^ 3 * a3 * b6
    - (9042919424 : F) * h ^ 54 * a7 ^ 3 * a2 * b7
    - (10334765056 : F) * h ^ 54 * a7 ^ 3 * a1 * b8
    - (7751073792 : F) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * b4
    - (19377684480 : F) * h ^ 54 * a7 ^ 2 * a6 * a5 * b5
    - (23253221376 : F) * h ^ 54 * a7 ^ 2 * a6 * a4 * b6
    - (27128758272 : F) * h ^ 54 * a7 ^ 2 * a6 * a3 * b7
    - (31004295168 : F) * h ^ 54 * a7 ^ 2 * a6 * a2 * b8
    - (11626610688 : F) * h ^ 54 * a7 ^ 2 * a5 ^ 2 * b6
    - (27128758272 : F) * h ^ 54 * a7 ^ 2 * a5 * a4 * b7
    - (31004295168 : F) * h ^ 54 * a7 ^ 2 * a5 * a3 * b8
    - (15502147584 : F) * h ^ 54 * a7 ^ 2 * a4 ^ 2 * b8
    - (6459228160 : F) * h ^ 54 * a7 * a6 ^ 3 * b5
    - (23253221376 : F) * h ^ 54 * a7 * a6 ^ 2 * a5 * b6
    - (27128758272 : F) * h ^ 54 * a7 * a6 ^ 2 * a4 * b7
    - (31004295168 : F) * h ^ 54 * a7 * a6 ^ 2 * a3 * b8
    - (27128758272 : F) * h ^ 54 * a7 * a6 * a5 ^ 2 * b7
    - (62008590336 : F) * h ^ 54 * a7 * a6 * a5 * a4 * b8
    - (10334765056 : F) * h ^ 54 * a7 * a5 ^ 3 * b8
    - (1937768448 : F) * h ^ 54 * a6 ^ 4 * b6
    - (9042919424 : F) * h ^ 54 * a6 ^ 3 * a5 * b7
    - (10334765056 : F) * h ^ 54 * a6 ^ 3 * a4 * b8
    - (15502147584 : F) * h ^ 54 * a6 ^ 2 * a5 ^ 2 * b8
    - (2724986880 : F) * h ^ 55 * a7 ^ 4 * a1 * lambda
    - (10899947520 : F) * h ^ 55 * a7 ^ 3 * a6 * a2 * lambda
    - (10899947520 : F) * h ^ 55 * a7 ^ 3 * a5 * a3 * lambda
    - (5449973760 : F) * h ^ 55 * a7 ^ 3 * a4 ^ 2 * lambda
    - (16349921280 : F) * h ^ 55 * a7 ^ 2 * a6 ^ 2 * a3 * lambda
    - (32699842560 : F) * h ^ 55 * a7 ^ 2 * a6 * a5 * a4 * lambda
    - (5449973760 : F) * h ^ 55 * a7 ^ 2 * a5 ^ 3 * lambda
    - (10899947520 : F) * h ^ 55 * a7 * a6 ^ 3 * a4 * lambda
    - (16349921280 : F) * h ^ 55 * a7 * a6 ^ 2 * a5 ^ 2 * lambda
    - (2724986880 : F) * h ^ 55 * a6 ^ 4 * a5 * lambda
    - (2422210560 : F) * h ^ 56 * a7 ^ 4 * a0
    + (4844421120 : F) * h ^ 56 * a7 ^ 3 * a6 * a1
    + (4844421120 : F) * h ^ 56 * a7 ^ 3 * a5 * a2
    + (4844421120 : F) * h ^ 56 * a7 ^ 3 * a4 * a3
    + (29066526720 : F) * h ^ 56 * a7 ^ 2 * a6 ^ 2 * a2
    + (58133053440 : F) * h ^ 56 * a7 ^ 2 * a6 * a5 * a3
    + (29066526720 : F) * h ^ 56 * a7 ^ 2 * a6 * a4 ^ 2
    + (29066526720 : F) * h ^ 56 * a7 ^ 2 * a5 ^ 2 * a4
    + (33910947840 : F) * h ^ 56 * a7 * a6 ^ 3 * a3
    + (101732843520 : F) * h ^ 56 * a7 * a6 ^ 2 * a5 * a4
    + (33910947840 : F) * h ^ 56 * a7 * a6 * a5 ^ 3
    + (12111052800 : F) * h ^ 56 * a6 ^ 4 * a4
    + (24222105600 : F) * h ^ 56 * a6 ^ 3 * a5 ^ 2
    + (469762048 : F) * h ^ 62 * a7 ^ 3 * b1
    + (2818572288 : F) * h ^ 62 * a7 ^ 2 * a6 * b2
    + (4227858432 : F) * h ^ 62 * a7 ^ 2 * a5 * b3
    + (5637144576 : F) * h ^ 62 * a7 ^ 2 * a4 * b4
    + (7046430720 : F) * h ^ 62 * a7 ^ 2 * a3 * b5
    + (8455716864 : F) * h ^ 62 * a7 ^ 2 * a2 * b6
    + (9865003008 : F) * h ^ 62 * a7 ^ 2 * a1 * b7
    + (11274289152 : F) * h ^ 62 * a7 ^ 2 * a0 * b8
    + (4227858432 : F) * h ^ 62 * a7 * a6 ^ 2 * b3
    + (11274289152 : F) * h ^ 62 * a7 * a6 * a5 * b4
    + (14092861440 : F) * h ^ 62 * a7 * a6 * a4 * b5
    + (16911433728 : F) * h ^ 62 * a7 * a6 * a3 * b6
    + (19730006016 : F) * h ^ 62 * a7 * a6 * a2 * b7
    + (22548578304 : F) * h ^ 62 * a7 * a6 * a1 * b8
    + (7046430720 : F) * h ^ 62 * a7 * a5 ^ 2 * b5
    + (16911433728 : F) * h ^ 62 * a7 * a5 * a4 * b6
    + (19730006016 : F) * h ^ 62 * a7 * a5 * a3 * b7
    + (22548578304 : F) * h ^ 62 * a7 * a5 * a2 * b8
    + (9865003008 : F) * h ^ 62 * a7 * a4 ^ 2 * b7
    + (22548578304 : F) * h ^ 62 * a7 * a4 * a3 * b8
    + (1879048192 : F) * h ^ 62 * a6 ^ 3 * b4
    + (7046430720 : F) * h ^ 62 * a6 ^ 2 * a5 * b5
    + (8455716864 : F) * h ^ 62 * a6 ^ 2 * a4 * b6
    + (9865003008 : F) * h ^ 62 * a6 ^ 2 * a3 * b7
    + (11274289152 : F) * h ^ 62 * a6 ^ 2 * a2 * b8
    + (8455716864 : F) * h ^ 62 * a6 * a5 ^ 2 * b6
    + (19730006016 : F) * h ^ 62 * a6 * a5 * a4 * b7
    + (22548578304 : F) * h ^ 62 * a6 * a5 * a3 * b8
    + (11274289152 : F) * h ^ 62 * a6 * a4 ^ 2 * b8
    + (3288334336 : F) * h ^ 62 * a5 ^ 3 * b7
    + (11274289152 : F) * h ^ 62 * a5 ^ 2 * a4 * b8
    + (2906652672 : F) * h ^ 63 * a7 ^ 3 * a0 * lambda
    + (8719958016 : F) * h ^ 63 * a7 ^ 2 * a6 * a1 * lambda
    + (8719958016 : F) * h ^ 63 * a7 ^ 2 * a5 * a2 * lambda
    + (8719958016 : F) * h ^ 63 * a7 ^ 2 * a4 * a3 * lambda
    + (8719958016 : F) * h ^ 63 * a7 * a6 ^ 2 * a2 * lambda
    + (17439916032 : F) * h ^ 63 * a7 * a6 * a5 * a3 * lambda
    + (8719958016 : F) * h ^ 63 * a7 * a6 * a4 ^ 2 * lambda
    + (8719958016 : F) * h ^ 63 * a7 * a5 ^ 2 * a4 * lambda
    + (2906652672 : F) * h ^ 63 * a6 ^ 3 * a3 * lambda
    + (8719958016 : F) * h ^ 63 * a6 ^ 2 * a5 * a4 * lambda
    + (2906652672 : F) * h ^ 63 * a6 * a5 ^ 3 * lambda
    - (7046430720 : F) * h ^ 64 * a7 ^ 2 * a6 * a0
    - (7046430720 : F) * h ^ 64 * a7 ^ 2 * a5 * a1
    - (7046430720 : F) * h ^ 64 * a7 ^ 2 * a4 * a2
    - (3523215360 : F) * h ^ 64 * a7 ^ 2 * a3 ^ 2
    - (22900899840 : F) * h ^ 64 * a7 * a6 ^ 2 * a1
    - (45801799680 : F) * h ^ 64 * a7 * a6 * a5 * a2
    - (45801799680 : F) * h ^ 64 * a7 * a6 * a4 * a3
    - (22900899840 : F) * h ^ 64 * a7 * a5 ^ 2 * a3
    - (22900899840 : F) * h ^ 64 * a7 * a5 * a4 ^ 2
    - (12918456320 : F) * h ^ 64 * a6 ^ 3 * a2
    - (38755368960 : F) * h ^ 64 * a6 ^ 2 * a5 * a3
    - (19377684480 : F) * h ^ 64 * a6 ^ 2 * a4 ^ 2
    - (38755368960 : F) * h ^ 64 * a6 * a5 ^ 2 * a4
    - (3229614080 : F) * h ^ 64 * a5 ^ 4
    - (1610612736 : F) * h ^ 70 * a7 * a6 * b1
    - (3221225472 : F) * h ^ 70 * a7 * a5 * b2
    - (4831838208 : F) * h ^ 70 * a7 * a4 * b3
    - (6442450944 : F) * h ^ 70 * a7 * a3 * b4
    - (8053063680 : F) * h ^ 70 * a7 * a2 * b5
    - (9663676416 : F) * h ^ 70 * a7 * a1 * b6
    - (11274289152 : F) * h ^ 70 * a7 * a0 * b7
    - (1610612736 : F) * h ^ 70 * a6 ^ 2 * b2
    - (4831838208 : F) * h ^ 70 * a6 * a5 * b3
    - (6442450944 : F) * h ^ 70 * a6 * a4 * b4
    - (8053063680 : F) * h ^ 70 * a6 * a3 * b5
    - (9663676416 : F) * h ^ 70 * a6 * a2 * b6
    - (11274289152 : F) * h ^ 70 * a6 * a1 * b7
    - (12884901888 : F) * h ^ 70 * a6 * a0 * b8
    - (3221225472 : F) * h ^ 70 * a5 ^ 2 * b4
    - (8053063680 : F) * h ^ 70 * a5 * a4 * b5
    - (9663676416 : F) * h ^ 70 * a5 * a3 * b6
    - (11274289152 : F) * h ^ 70 * a5 * a2 * b7
    - (12884901888 : F) * h ^ 70 * a5 * a1 * b8
    - (4831838208 : F) * h ^ 70 * a4 ^ 2 * b6
    - (11274289152 : F) * h ^ 70 * a4 * a3 * b7
    - (12884901888 : F) * h ^ 70 * a4 * a2 * b8
    - (6442450944 : F) * h ^ 70 * a3 ^ 2 * b8
    - (6341787648 : F) * h ^ 71 * a7 * a6 * a0 * lambda
    - (6341787648 : F) * h ^ 71 * a7 * a5 * a1 * lambda
    - (6341787648 : F) * h ^ 71 * a7 * a4 * a2 * lambda
    - (3170893824 : F) * h ^ 71 * a7 * a3 ^ 2 * lambda
    - (3170893824 : F) * h ^ 71 * a6 ^ 2 * a1 * lambda
    - (6341787648 : F) * h ^ 71 * a6 * a5 * a2 * lambda
    - (6341787648 : F) * h ^ 71 * a6 * a4 * a3 * lambda
    - (3170893824 : F) * h ^ 71 * a5 ^ 2 * a3 * lambda
    - (3170893824 : F) * h ^ 71 * a5 * a4 ^ 2 * lambda
    + (10066329600 : F) * h ^ 72 * a7 * a5 * a0
    + (10066329600 : F) * h ^ 72 * a7 * a4 * a1
    + (10066329600 : F) * h ^ 72 * a7 * a3 * a2
    + (14092861440 : F) * h ^ 72 * a6 ^ 2 * a0
    + (28185722880 : F) * h ^ 72 * a6 * a5 * a1
    + (28185722880 : F) * h ^ 72 * a6 * a4 * a2
    + (14092861440 : F) * h ^ 72 * a6 * a3 ^ 2
    + (14092861440 : F) * h ^ 72 * a5 ^ 2 * a2
    + (28185722880 : F) * h ^ 72 * a5 * a4 * a3
    + (4697620480 : F) * h ^ 72 * a4 ^ 3
    + (2147483648 : F) * h ^ 78 * a5 * b1
    + (4294967296 : F) * h ^ 78 * a4 * b2
    + (6442450944 : F) * h ^ 78 * a3 * b3
    + (8589934592 : F) * h ^ 78 * a2 * b4
    + (10737418240 : F) * h ^ 78 * a1 * b5
    + (12884901888 : F) * h ^ 78 * a0 * b6
    + (3623878656 : F) * h ^ 79 * a5 * a0 * lambda
    + (3623878656 : F) * h ^ 79 * a4 * a1 * lambda
    + (3623878656 : F) * h ^ 79 * a3 * a2 * lambda
    - (16106127360 : F) * h ^ 80 * a4 * a0
    - (16106127360 : F) * h ^ 80 * a3 * a1
    - (8053063680 : F) * h ^ 80 * a2 ^ 2 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h512 : (512 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h4096 : (4096 : F) ≠ 0 := by norm_num
  have h16384 : (16384 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h32768 : (32768 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  have hh63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  have hh84 : h ^ 84 ≠ 0 := pow_ne_zero 84 hh
  have hL :
      depressedL810 h (octicDepressionR810 h a7) b9 = -lambda / 4 :=
    depressedL810_eq_of_ninthPower h a7 b9 lambda hh hN
  have hA :
      depressedA810 h (octicDepressionR810 h a7) a7 a6 =
        (16 * a6 * h ^ 8 - 7 * a7 ^ 2) / (16 * h ^ 14) :=
    depressedA810_eq_cleared h a7 a6 hh
  have hB :
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
        (32 * a5 * h ^ 16 - 24 * a6 * a7 * h ^ 8 + 7 * a7 ^ 3) /
          (32 * h ^ 21) :=
    depressedB810_eq_cleared h a7 a6 a5 hh
  have hC :
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
        (2048 * a4 * h ^ 24 - 1280 * a5 * a7 * h ^ 16 +
            480 * a6 * a7 ^ 2 * h ^ 8 - 105 * a7 ^ 4) /
          (2048 * h ^ 28) :=
    depressedC810_eq_cleared h a7 a6 a5 a4 hh
  have hD0 :
      depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
        (1024 * a3 * h ^ 32 - 512 * a4 * a7 * h ^ 24 +
            160 * a5 * a7 ^ 2 * h ^ 16 - 40 * a6 * a7 ^ 3 * h ^ 8 +
            7 * a7 ^ 5) /
          (1024 * h ^ 35) :=
    depressedD810_eq_cleared h a7 a6 a5 a4 a3 hh
  have hE0 :
      depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 =
        (65536 * a2 * h ^ 40 - 24576 * a3 * a7 * h ^ 32 +
            6144 * a4 * a7 ^ 2 * h ^ 24 - 1280 * a5 * a7 ^ 3 * h ^ 16 +
            240 * a6 * a7 ^ 4 * h ^ 8 - 35 * a7 ^ 6) /
          (65536 * h ^ 42) :=
    depressedE810_eq_cleared h a7 a6 a5 a4 a3 a2 hh
  have hF0 :
      depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 =
        (131072 * a1 * h ^ 48 - 32768 * a2 * a7 * h ^ 40 +
            6144 * a3 * a7 ^ 2 * h ^ 32 - 1024 * a4 * a7 ^ 3 * h ^ 24 +
            160 * a5 * a7 ^ 4 * h ^ 16 - 24 * a6 * a7 ^ 5 * h ^ 8 +
            3 * a7 ^ 7) /
          (131072 * h ^ 49) :=
    depressedF810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 hh
  have hG0 :
      depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
          a0 =
        (16777216 * a0 * h ^ 56 - 2097152 * a1 * a7 * h ^ 48 +
            262144 * a2 * a7 ^ 2 * h ^ 40 - 32768 * a3 * a7 ^ 3 * h ^ 32 +
            4096 * a4 * a7 ^ 4 * h ^ 24 - 512 * a5 * a7 ^ 5 * h ^ 16 +
            64 * a6 * a7 ^ 6 * h ^ 8 - 7 * a7 ^ 8) /
          (16777216 * h ^ 56) :=
    depressedG810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 a0 hh
  have hP :
      depressedP810 h (octicDepressionR810 h a7) b9 b8 =
        (-45 * a7 ^ 2 + 18 * lambda * a7 * h ^ 7 + 64 * b8 * h ^ 6) /
          (64 * h ^ 14) :=
    depressedP810_eq_cleared_ninthPower h a7 b9 b8 lambda hh hN
  have hQ :
      depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 =
        (64 * b7 * h ^ 14 - 64 * a7 * b8 * h ^ 6 -
            9 * lambda * a7 ^ 2 * h ^ 7 + 30 * a7 ^ 3) /
          (64 * h ^ 21) :=
    depressedQ810_eq_cleared h a7 b9 b8 b7 lambda hh hN
  have hR :
      depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 =
        (-315 * a7 ^ 4 + 84 * lambda * a7 ^ 3 * h ^ 7 +
            896 * a7 ^ 2 * b8 * h ^ 6 - 1792 * a7 * b7 * h ^ 14 +
            2048 * b6 * h ^ 22) /
          (2048 * h ^ 28) :=
    depressedR810_eq_cleared h a7 b9 b8 b7 b6 lambda hh hN
  have hS :
      depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
        (252 * a7 ^ 5 - 63 * lambda * a7 ^ 4 * h ^ 7 -
            896 * a7 ^ 3 * b8 * h ^ 6 + 2688 * a7 ^ 2 * b7 * h ^ 14 -
            6144 * a7 * b6 * h ^ 22 + 8192 * b5 * h ^ 30) /
          (8192 * h ^ 35) :=
    depressedS810_eq_cleared h a7 b9 b8 b7 b6 b5 lambda hh hN
  have hT0 :
      depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 =
        (-525 * a7 ^ 6 + 126 * lambda * a7 ^ 5 * h ^ 7 +
            2240 * a7 ^ 4 * b8 * h ^ 6 - 8960 * a7 ^ 3 * b7 * h ^ 14 +
            30720 * a7 ^ 2 * b6 * h ^ 22 - 81920 * a7 * b5 * h ^ 30 +
            131072 * b4 * h ^ 38) /
          (131072 * h ^ 42) :=
    depressedT810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hU0 :
      depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 =
        (90 * a7 ^ 7 - 21 * lambda * a7 ^ 6 * h ^ 7 -
            448 * a7 ^ 5 * b8 * h ^ 6 + 2240 * a7 ^ 4 * b7 * h ^ 14 -
            10240 * a7 ^ 3 * b6 * h ^ 22 + 40960 * a7 ^ 2 * b5 * h ^ 30 -
            131072 * a7 * b4 * h ^ 38 + 262144 * b3 * h ^ 46) /
          (262144 * h ^ 49) :=
    depressedU810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  have hV0 :
      depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 =
        (-315 * a7 ^ 8 + 72 * lambda * a7 ^ 7 * h ^ 7 +
            1792 * a7 ^ 6 * b8 * h ^ 6 - 10752 * a7 ^ 5 * b7 * h ^ 14 +
            61440 * a7 ^ 4 * b6 * h ^ 22 - 327680 * a7 ^ 3 * b5 * h ^ 30 +
            1572864 * a7 ^ 2 * b4 * h ^ 38 -
            6291456 * a7 * b3 * h ^ 46 + 16777216 * b2 * h ^ 54) /
          (16777216 * h ^ 56) :=
    depressedV810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  have hW0 :
      depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 =
        (40 * a7 ^ 9 - 9 * lambda * a7 ^ 8 * h ^ 7 -
            256 * a7 ^ 7 * b8 * h ^ 6 + 1792 * a7 ^ 6 * b7 * h ^ 14 -
            12288 * a7 ^ 5 * b6 * h ^ 22 + 81920 * a7 ^ 4 * b5 * h ^ 30 -
            524288 * a7 ^ 3 * b4 * h ^ 38 +
            3145728 * a7 ^ 2 * b3 * h ^ 46 -
            16777216 * a7 * b2 * h ^ 54 + 67108864 * b1 * h ^ 62) /
          (67108864 * h ^ 63) :=
    depressedW810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda hh hN
  rw [hL, hA, hB, hC, hD0, hE0, hF0, hG0, hP, hQ, hR, hS, hT0, hU0, hV0, hW0,
    speedMuResidual810Scaled84_eq h hh]
  simp only [speedMuResidual810Scaled84]
  ring


end Depression810TwelfthClearing

end Max11DegreeRoutes
end
