import Grok810ScaleZeroTenthDefectSpeedTPart01Scratch

/-! # Scale-zero tenth defect for the normalized `(8,10)`, `H = 0` leaf

The ninth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first nine octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, `h³⁵`, `h⁴²`, `h⁴⁹`, `h⁵⁶`, `h⁶³`, and `h⁷⁰`.  This file consumes
the next unused Keller coefficient of the same monic octic-decic
depression: the degree-`6` Jacobian row is
`7 Q G' + 6 R F' + 5 S E' + 4 T D' + 3 U C' + 2 V B' + W A'
- F R' - 2 E S' - 3 D T' - 4 C U' - 5 B V' - 6 A W' = 0`.  The
corresponding eleventh cleared polynomial defect of weight seventy-seven
is likewise a ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`77` defect itself.  Root-evaluation from a scale-two
face is unavailable, because a nonzero constant has no finite root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`5` residual of
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

section Depression810EleventhClearing

variable {F : Type*} [Field F] [CharZero F]

-- Specialize arithmetic elaboration to the existing field carrier.
local infixl:65 (priority := high) " + " => (HAdd.hAdd (α := F) (β := F) (γ := F))
local infixl:65 (priority := high) " - " => (HSub.hSub (α := F) (β := F) (γ := F))
local infixl:70 (priority := high) " * " => (HMul.hMul (α := F) (β := F) (γ := F))
local infixl:70 (priority := high) " / " => (HDiv.hDiv (α := F) (β := F) (γ := F))
local infixr:80 (priority := high) " ^ " => (HPow.hPow (α := F) (β := Nat) (γ := F))
local prefix:75 (priority := high) "-" => (Neg.neg (α := F))

set_option maxHeartbeats 64000000 in
/-- SPEED (recipe R2, `scripts/coord/LEAN_SPEED_REPORT.md` §7): the weight-`77`
clearing of `kappaResidual810` carried out on the *atoms* rather than on the fully
substituted source polynomials.  `kappaResidual810` is weighted homogeneous, so
substituting `X_i = n_i / (d_i h^(e_i))` makes `1099511627776 * h^77 * kappaResidual810`
a polynomial in `h, n_*` — 51 monomials. -/
def speedKappaResidual810Scaled77 (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    (44919 : F) * h ^ 7 * nL * nA ^ 5
    - (28980 : F) * h ^ 7 * nL * nA ^ 3 * nC
    - (1391040 : F) * h ^ 7 * nL * nA ^ 2 * nB ^ 2
    + (15120 : F) * h ^ 7 * nL * nA ^ 2 * nE
    + (967680 : F) * h ^ 7 * nL * nA * nB * nD
    + (3780 : F) * h ^ 7 * nL * nA * nC ^ 2
    - (1008 : F) * h ^ 7 * nL * nA * nG
    + (120960 : F) * h ^ 7 * nL * nB ^ 2 * nC
    - (64512 : F) * h ^ 7 * nL * nB * nF
    - (2016 : F) * h ^ 7 * nL * nC * nE
    - (129024 : F) * h ^ 7 * nL * nD ^ 2
    + (499100 : F) * nA ^ 4 * nB
    - (45080 : F) * nA ^ 4 * nQ
    - (103040 : F) * nA ^ 3 * nB * nP
    - (257600 : F) * nA ^ 3 * nD
    + (5600 : F) * nA ^ 3 * nS
    - (193200 : F) * nA ^ 2 * nB * nC
    + (40320 : F) * nA ^ 2 * nB * nR
    + (23520 : F) * nA ^ 2 * nC * nQ
    + (53760 : F) * nA ^ 2 * nD * nP
    + (33600 : F) * nA ^ 2 * nF
    - (2688 : F) * nA ^ 2 * nU
    - (2060800 : F) * nA * nB ^ 3
    + (752640 : F) * nA * nB ^ 2 * nQ
    + (26880 : F) * nA * nB * nC * nP
    + (67200 : F) * nA * nB * nE
    - (7168 : F) * nA * nB * nT
    + (67200 : F) * nA * nC * nD
    - (2240 : F) * nA * nC * nS
    - (21504 : F) * nA * nD * nR
    - (12544 : F) * nA * nE * nQ
    - (7168 : F) * nA * nF * nP
    + (128 : F) * nA * nW
    + (143360 : F) * nB ^ 3 * nP
    + (1075200 : F) * nB ^ 2 * nD
    - (35840 : F) * nB ^ 2 * nS
    + (8400 : F) * nB * nC ^ 2
    - (5376 : F) * nB * nC * nR
    - (401408 : F) * nB * nD * nQ
    - (7168 : F) * nB * nE * nP
    - (2240 : F) * nB * nG
    + (512 : F) * nB * nV
    - (1568 : F) * nC ^ 2 * nQ
    - (7168 : F) * nC * nD * nP
    - (4480 : F) * nC * nF
    + (768 : F) * nC * nU
    - (17920 : F) * nD * nE
    + (4096 : F) * nD * nT
    + (1280 : F) * nE * nS
    + (3072 : F) * nF * nR
    + (896 : F) * nG * nQ

set_option maxHeartbeats 64000000 in
/-- The atom-level clearing: one `field_simp` over 17 atomic variables in
place of the single enormous `field_simp` on the substituted rational function. -/
theorem speedKappaResidual810Scaled77_eq (h : F) (hh : h ≠ 0) (nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) :
    (1099511627776 : F) * h ^ 77 *
        kappaResidual810
          (nL / 4)
          (nA / (16 * h ^ 14))
          (nB / (32 * h ^ 21))
          (nC / (2048 * h ^ 28))
          (nD / (1024 * h ^ 35))
          (nE / (65536 * h ^ 42))
          (nF / (131072 * h ^ 49))
          (nG / (16777216 * h ^ 56))
          (nP / (64 * h ^ 14))
          (nQ / (64 * h ^ 21))
          (nR / (2048 * h ^ 28))
          (nS / (8192 * h ^ 35))
          (nT / (131072 * h ^ 42))
          (nU / (262144 * h ^ 49))
          (nV / (16777216 * h ^ 56))
          (nW / (67108864 * h ^ 63)) =
      speedKappaResidual810Scaled77 h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW := by
  have hd2 : (2 : F) ≠ 0 := by norm_num
  have hd4 : (4 : F) ≠ 0 := by norm_num
  have hd16 : (16 : F) ≠ 0 := by norm_num
  have hd32 : (32 : F) ≠ 0 := by norm_num
  have hd64 : (64 : F) ≠ 0 := by norm_num
  have hd1024 : (1024 : F) ≠ 0 := by norm_num
  have hd2048 : (2048 : F) ≠ 0 := by norm_num
  have hd8192 : (8192 : F) ≠ 0 := by norm_num
  have hd65536 : (65536 : F) ≠ 0 := by norm_num
  have hd131072 : (131072 : F) ≠ 0 := by norm_num
  have hd262144 : (262144 : F) ≠ 0 := by norm_num
  have hd16777216 : (16777216 : F) ≠ 0 := by norm_num
  have hd67108864 : (67108864 : F) ≠ 0 := by norm_num
  have hp14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hp21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hp28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hp35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hp42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hp49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  have hp56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  have hp63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  simp only [alphaResidual810, betaResidual810, deltaResidual810, epsilonResidual810, etaResidual810, gammaResidual810, kappaResidual810, zetaResidual810, speedKappaResidual810Scaled77]
  field_simp
  ring

set_option maxHeartbeats 64000000 in
/-- Clearing the first integral `κ` of the degree-`6` row against `h⁷⁷`
on the ninth-power face. -/
theorem eleventhDefect_eq_clearedKappa810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (1099511627776 : F) * h ^ 77 *
        kappaResidual810
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
  - (21651457100 : F) * a7 ^ 11
    + (85873948160 : F) * h ^ 6 * a7 ^ 9 * b8
    + (21434942529 : F) * h ^ 7 * a7 ^ 10 * lambda
    + (134178044000 : F) * h ^ 8 * a7 ^ 9 * a6
    - (785133240320 : F) * h ^ 14 * a7 ^ 7 * a6 * b8
    - (85873948160 : F) * h ^ 14 * a7 ^ 8 * b7
    - (217368431280 : F) * h ^ 15 * a7 ^ 8 * a6 * lambda
    - (138011702400 : F) * h ^ 16 * a7 ^ 8 * a5
    + (2398225170432 : F) * h ^ 22 * a7 ^ 5 * a6 ^ 2 * b8
    + (799408390144 : F) * h ^ 22 * a7 ^ 6 * a5 * b8
    + (699482341376 : F) * h ^ 22 * a7 ^ 6 * a6 * b7
    + (85650898944 : F) * h ^ 22 * a7 ^ 7 * b6
    + (772865533440 : F) * h ^ 23 * a7 ^ 6 * a6 ^ 2 * lambda
    + (220818723840 : F) * h ^ 23 * a7 ^ 7 * a5 * lambda
    - (1249075609600 : F) * h ^ 24 * a7 ^ 5 * a6 ^ 3
    - (124907560960 : F) * h ^ 24 * a7 ^ 6 * a6 * a5
    + (142751498240 : F) * h ^ 24 * a7 ^ 7 * a4
    - (2721390264320 : F) * h ^ 30 * a7 ^ 3 * a6 ^ 3 * b8
    - (4082085396480 : F) * h ^ 30 * a7 ^ 4 * a6 * a5 * b8
    - (1785912360960 : F) * h ^ 30 * a7 ^ 4 * a6 ^ 2 * b7
    - (816417079296 : F) * h ^ 30 * a7 ^ 5 * a4 * b8
    - (714364944384 : F) * h ^ 30 * a7 ^ 5 * a5 * b7
    - (612312809472 : F) * h ^ 30 * a7 ^ 5 * a6 * b6
    - (85043445760 : F) * h ^ 30 * a7 ^ 6 * b5
    - (1124168048640 : F) * h ^ 31 * a7 ^ 4 * a6 ^ 3 * lambda
    - (1349001658368 : F) * h ^ 31 * a7 ^ 5 * a6 * a5 * lambda
    - (224833609728 : F) * h ^ 31 * a7 ^ 6 * a4 * lambda
    + (2126086144000 : F) * h ^ 32 * a7 ^ 3 * a6 ^ 4
    + (3508042137600 : F) * h ^ 32 * a7 ^ 4 * a6 ^ 2 * a5
    + (127565168640 : F) * h ^ 32 * a7 ^ 5 * a5 ^ 2
    + (255130337280 : F) * h ^ 32 * a7 ^ 5 * a6 * a4
    - (148826030080 : F) * h ^ 32 * a7 ^ 6 * a3
    + (837350850560 : F) * h ^ 38 * a7 * a6 ^ 4 * b8
    + (5024105103360 : F) * h ^ 38 * a7 ^ 2 * a6 ^ 2 * a5 * b8
    + (1465363988480 : F) * h ^ 38 * a7 ^ 2 * a6 ^ 3 * b7
    + (1674701701120 : F) * h ^ 38 * a7 ^ 3 * a5 ^ 2 * b8
    + (3349403402240 : F) * h ^ 38 * a7 ^ 3 * a6 * a4 * b8
    + (2930727976960 : F) * h ^ 38 * a7 ^ 3 * a6 * a5 * b7
    + (1256026275840 : F) * h ^ 38 * a7 ^ 3 * a6 ^ 2 * b6
    + (837350850560 : F) * h ^ 38 * a7 ^ 4 * a3 * b8
    + (732681994240 : F) * h ^ 38 * a7 ^ 4 * a4 * b7
    + (628013137920 : F) * h ^ 38 * a7 ^ 4 * a5 * b6
    + (523344281600 : F) * h ^ 38 * a7 ^ 4 * a6 * b5
    + (83735085056 : F) * h ^ 38 * a7 ^ 5 * b4
    + (574043258880 : F) * h ^ 39 * a7 ^ 2 * a6 ^ 4 * lambda
    + (2296173035520 : F) * h ^ 39 * a7 ^ 3 * a6 ^ 2 * a5 * lambda
    + (574043258880 : F) * h ^ 39 * a7 ^ 4 * a5 ^ 2 * lambda
    + (1148086517760 : F) * h ^ 39 * a7 ^ 4 * a6 * a4 * lambda
    + (229617303552 : F) * h ^ 39 * a7 ^ 5 * a3 * lambda
    - (785016422400 : F) * h ^ 40 * a7 * a6 ^ 5
    - (5495114956800 : F) * h ^ 40 * a7 ^ 2 * a6 ^ 3 * a5
    - (3140065689600 : F) * h ^ 40 * a7 ^ 3 * a6 * a5 ^ 2
    - (3140065689600 : F) * h ^ 40 * a7 ^ 3 * a6 ^ 2 * a4
    - (392508211200 : F) * h ^ 40 * a7 ^ 4 * a5 * a4
    - (392508211200 : F) * h ^ 40 * a7 ^ 4 * a6 * a3
    + (157003284480 : F) * h ^ 40 * a7 ^ 5 * a2
    - (864362168320 : F) * h ^ 46 * a6 ^ 3 * a5 * b8
    - (189079224320 : F) * h ^ 46 * a6 ^ 4 * b7
    - (2593086504960 : F) * h ^ 46 * a7 * a6 * a5 ^ 2 * b8
    - (2593086504960 : F) * h ^ 46 * a7 * a6 ^ 2 * a4 * b8
    - (2268950691840 : F) * h ^ 46 * a7 * a6 ^ 2 * a5 * b7
    - (648271626240 : F) * h ^ 46 * a7 * a6 ^ 3 * b6
    - (2593086504960 : F) * h ^ 46 * a7 ^ 2 * a5 * a4 * b8
    - (1134475345920 : F) * h ^ 46 * a7 ^ 2 * a5 ^ 2 * b7
    - (2593086504960 : F) * h ^ 46 * a7 ^ 2 * a6 * a3 * b8
    - (2268950691840 : F) * h ^ 46 * a7 ^ 2 * a6 * a4 * b7
    - (1944814878720 : F) * h ^ 46 * a7 ^ 2 * a6 * a5 * b6
    - (810339532800 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * b5
    - (864362168320 : F) * h ^ 46 * a7 ^ 3 * a2 * b8
    - (756316897280 : F) * h ^ 46 * a7 ^ 3 * a3 * b7
    - (648271626240 : F) * h ^ 46 * a7 ^ 3 * a4 * b6
    - (540226355200 : F) * h ^ 46 * a7 ^ 3 * a5 * b5
    - (432181084160 : F) * h ^ 46 * a7 ^ 3 * a6 * b4
    - (81033953280 : F) * h ^ 46 * a7 ^ 4 * b3
    - (47100985344 : F) * h ^ 47 * a6 ^ 5 * lambda
    - (942019706880 : F) * h ^ 47 * a7 * a6 ^ 3 * a5 * lambda
    - (1413029560320 : F) * h ^ 47 * a7 ^ 2 * a6 * a5 ^ 2 * lambda
    - (1413029560320 : F) * h ^ 47 * a7 ^ 2 * a6 ^ 2 * a4 * lambda
    - (942019706880 : F) * h ^ 47 * a7 ^ 3 * a5 * a4 * lambda
    - (942019706880 : F) * h ^ 47 * a7 ^ 3 * a6 * a3 * lambda
    - (235504926720 : F) * h ^ 47 * a7 ^ 4 * a2 * lambda
    + (1046688563200 : F) * h ^ 48 * a6 ^ 4 * a5
    + (4456867430400 : F) * h ^ 48 * a7 * a6 ^ 2 * a5 ^ 2
    + (2971244953600 : F) * h ^ 48 * a7 * a6 ^ 3 * a4
    + (877867827200 : F) * h ^ 48 * a7 ^ 2 * a5 ^ 3
    + (5267206963200 : F) * h ^ 48 * a7 ^ 2 * a6 * a5 * a4
    + (2633603481600 : F) * h ^ 48 * a7 ^ 2 * a6 ^ 2 * a3
    + (270113177600 : F) * h ^ 48 * a7 ^ 3 * a4 ^ 2
    + (540226355200 : F) * h ^ 48 * a7 ^ 3 * a5 * a3
    + (540226355200 : F) * h ^ 48 * a7 ^ 3 * a6 * a2
    - (168820736000 : F) * h ^ 48 * a7 ^ 4 * a1
    + (300647710720 : F) * h ^ 54 * a5 ^ 3 * b8
    + (1803886264320 : F) * h ^ 54 * a6 * a5 * a4 * b8
    + (789200240640 : F) * h ^ 54 * a6 * a5 ^ 2 * b7
    + (901943132160 : F) * h ^ 54 * a6 ^ 2 * a3 * b8
    + (789200240640 : F) * h ^ 54 * a6 ^ 2 * a4 * b7
    + (676457349120 : F) * h ^ 54 * a6 ^ 2 * a5 * b6
    + (187904819200 : F) * h ^ 54 * a6 ^ 3 * b5
    + (901943132160 : F) * h ^ 54 * a7 * a4 ^ 2 * b8
    + (1803886264320 : F) * h ^ 54 * a7 * a5 * a3 * b8
    + (1578400481280 : F) * h ^ 54 * a7 * a5 * a4 * b7
    + (676457349120 : F) * h ^ 54 * a7 * a5 ^ 2 * b6
    + (1803886264320 : F) * h ^ 54 * a7 * a6 * a2 * b8
    + (1578400481280 : F) * h ^ 54 * a7 * a6 * a3 * b7
    + (1352914698240 : F) * h ^ 54 * a7 * a6 * a4 * b6
    + (1127428915200 : F) * h ^ 54 * a7 * a6 * a5 * b5
    + (450971566080 : F) * h ^ 54 * a7 * a6 ^ 2 * b4
    + (901943132160 : F) * h ^ 54 * a7 ^ 2 * a1 * b8
    + (789200240640 : F) * h ^ 54 * a7 ^ 2 * a2 * b7
    + (676457349120 : F) * h ^ 54 * a7 ^ 2 * a3 * b6
    + (563714457600 : F) * h ^ 54 * a7 ^ 2 * a4 * b5
    + (450971566080 : F) * h ^ 54 * a7 ^ 2 * a5 * b4
    + (338228674560 : F) * h ^ 54 * a7 ^ 2 * a6 * b3
    + (75161927680 : F) * h ^ 54 * a7 ^ 3 * b2
    + (364652789760 : F) * h ^ 55 * a6 ^ 2 * a5 ^ 2 * lambda
    + (243101859840 : F) * h ^ 55 * a6 ^ 3 * a4 * lambda
    + (243101859840 : F) * h ^ 55 * a7 * a5 ^ 3 * lambda
    + (1458611159040 : F) * h ^ 55 * a7 * a6 * a5 * a4 * lambda
    + (729305579520 : F) * h ^ 55 * a7 * a6 ^ 2 * a3 * lambda
    + (364652789760 : F) * h ^ 55 * a7 ^ 2 * a4 ^ 2 * lambda
    + (729305579520 : F) * h ^ 55 * a7 ^ 2 * a5 * a3 * lambda
    + (729305579520 : F) * h ^ 55 * a7 ^ 2 * a6 * a2 * lambda
    + (243101859840 : F) * h ^ 55 * a7 ^ 3 * a1 * lambda
    - (1080452710400 : F) * h ^ 56 * a6 * a5 ^ 3
    - (3241358131200 : F) * h ^ 56 * a6 ^ 2 * a5 * a4
    - (1080452710400 : F) * h ^ 56 * a6 ^ 3 * a3
    - (1973000601600 : F) * h ^ 56 * a7 * a5 ^ 2 * a4
    - (1973000601600 : F) * h ^ 56 * a7 * a6 * a4 ^ 2
    - (3946001203200 : F) * h ^ 56 * a7 * a6 * a5 * a3
    - (1973000601600 : F) * h ^ 56 * a7 * a6 ^ 2 * a2
    - (704643072000 : F) * h ^ 56 * a7 ^ 2 * a4 * a3
    - (704643072000 : F) * h ^ 56 * a7 ^ 2 * a5 * a2
    - (704643072000 : F) * h ^ 56 * a7 ^ 2 * a6 * a1
    + (187904819200 : F) * h ^ 56 * a7 ^ 3 * a0
    - (962072674304 : F) * h ^ 62 * a4 * a3 * b8
    - (420906795008 : F) * h ^ 62 * a4 ^ 2 * b7
    - (962072674304 : F) * h ^ 62 * a5 * a2 * b8
    - (841813590016 : F) * h ^ 62 * a5 * a3 * b7
    - (721554505728 : F) * h ^ 62 * a5 * a4 * b6
    - (300647710720 : F) * h ^ 62 * a5 ^ 2 * b5
    - (962072674304 : F) * h ^ 62 * a6 * a1 * b8
    - (841813590016 : F) * h ^ 62 * a6 * a2 * b7
    - (721554505728 : F) * h ^ 62 * a6 * a3 * b6
    - (601295421440 : F) * h ^ 62 * a6 * a4 * b5
    - (481036337152 : F) * h ^ 62 * a6 * a5 * b4
    - (180388626432 : F) * h ^ 62 * a6 ^ 2 * b3
    - (962072674304 : F) * h ^ 62 * a7 * a0 * b8
    - (841813590016 : F) * h ^ 62 * a7 * a1 * b7
    - (721554505728 : F) * h ^ 62 * a7 * a2 * b6
    - (601295421440 : F) * h ^ 62 * a7 * a3 * b5
    - (481036337152 : F) * h ^ 62 * a7 * a4 * b4
    - (360777252864 : F) * h ^ 62 * a7 * a5 * b3
    - (240518168576 : F) * h ^ 62 * a7 * a6 * b2
    - (60129542144 : F) * h ^ 62 * a7 ^ 2 * b1
    - (253671505920 : F) * h ^ 63 * a5 ^ 2 * a4 * lambda
    - (253671505920 : F) * h ^ 63 * a6 * a4 ^ 2 * lambda
    - (507343011840 : F) * h ^ 63 * a6 * a5 * a3 * lambda
    - (253671505920 : F) * h ^ 63 * a6 ^ 2 * a2 * lambda
    - (507343011840 : F) * h ^ 63 * a7 * a4 * a3 * lambda
    - (507343011840 : F) * h ^ 63 * a7 * a5 * a2 * lambda
    - (507343011840 : F) * h ^ 63 * a7 * a6 * a1 * lambda
    - (253671505920 : F) * h ^ 63 * a7 ^ 2 * a0 * lambda
    + (1127428915200 : F) * h ^ 64 * a5 * a4 ^ 2
    + (1127428915200 : F) * h ^ 64 * a5 ^ 2 * a3
    + (2254857830400 : F) * h ^ 64 * a6 * a4 * a3
    + (2254857830400 : F) * h ^ 64 * a6 * a5 * a2
    + (1127428915200 : F) * h ^ 64 * a6 ^ 2 * a1
    + (450971566080 : F) * h ^ 64 * a7 * a3 ^ 2
    + (901943132160 : F) * h ^ 64 * a7 * a4 * a2
    + (901943132160 : F) * h ^ 64 * a7 * a5 * a1
    + (901943132160 : F) * h ^ 64 * a7 * a6 * a0
    + (962072674304 : F) * h ^ 70 * a0 * b7
    + (824633720832 : F) * h ^ 70 * a1 * b6
    + (687194767360 : F) * h ^ 70 * a2 * b5
    + (549755813888 : F) * h ^ 70 * a3 * b4
    + (412316860416 : F) * h ^ 70 * a4 * b3
    + (274877906944 : F) * h ^ 70 * a5 * b2
    + (137438953472 : F) * h ^ 70 * a6 * b1
    + (135291469824 : F) * h ^ 71 * a3 ^ 2 * lambda
    + (270582939648 : F) * h ^ 71 * a4 * a2 * lambda
    + (270582939648 : F) * h ^ 71 * a5 * a1 * lambda
    + (270582939648 : F) * h ^ 71 * a6 * a0 * lambda
    - (1202590842880 : F) * h ^ 72 * a3 * a2
    - (1202590842880 : F) * h ^ 72 * a4 * a1
    - (1202590842880 : F) * h ^ 72 * a5 * a0 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
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
  have h1099511627776 : (1099511627776 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  have hh63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  have hh77 : h ^ 77 ≠ 0 := pow_ne_zero 77 hh
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
    speedKappaResidual810Scaled77_eq h hh]
  simp only [speedKappaResidual810Scaled77]
  ring

end Depression810EleventhClearing

end Max11DegreeRoutes
