import Fable610ScaleTwoKappaIntegralBridgeCompatPart101Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 400000000 in
/-- SPEED (recipe R2, `scripts/coord/LEAN_SPEED_REPORT.md` §7): the weight-`55`
clearing of `bridgeKappaResidual610` carried out on the *atoms* rather than on the fully
substituted source polynomials.  `bridgeKappaResidual610` is weighted homogeneous, so
substituting `X_i = n_i / (d_i h^(e_i))` makes `3761479876608 * h^55 * bridgeKappaResidual610`
a polynomial in `h, n_*` — 43 monomials. -/
def speedBridgeKappaResidual610Scaled55 (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    (1045143 : F) * h ^ 5 * nL * nA ^ 5
    - (5452920 : F) * h ^ 5 * nL * nA ^ 3 * nC
    - (4847040 : F) * h ^ 5 * nL * nA ^ 2 * nB ^ 2
    + (213840 : F) * h ^ 5 * nL * nA ^ 2 * nE
    + (13685760 : F) * h ^ 5 * nL * nA * nB * nD
    + (5773680 : F) * h ^ 5 * nL * nA * nC ^ 2
    + (3421440 : F) * h ^ 5 * nL * nB ^ 2 * nC
    - (233280 : F) * h ^ 5 * nL * nC * nE
    - (7464960 : F) * h ^ 5 * nL * nD ^ 2
    + (3870900 : F) * nA ^ 4 * nB
    - (4241160 : F) * nA ^ 4 * nQ
    - (9694080 : F) * nA ^ 3 * nB * nP
    - (8078400 : F) * nA ^ 3 * nD
    + (2138400 : F) * nA ^ 3 * nS
    - (12117600 : F) * nA ^ 2 * nB * nC
    + (855360 : F) * nA ^ 2 * nB * nR
    + (17962560 : F) * nA ^ 2 * nC * nQ
    + (20528640 : F) * nA ^ 2 * nD * nP
    - (466560 : F) * nA ^ 2 * nU
    - (2393600 : F) * nA * nB ^ 3
    + (10644480 : F) * nA * nB ^ 2 * nQ
    + (20528640 : F) * nA * nB * nC * nP
    + (316800 : F) * nA * nB * nE
    - (414720 : F) * nA * nB * nT
    + (17107200 : F) * nA * nC * nD
    - (6998400 : F) * nA * nC * nS
    - (1866240 : F) * nA * nD * nR
    - (725760 : F) * nA * nE * nQ
    + (10368 : F) * nA * nW
    + (2027520 : F) * nB ^ 3 * nP
    + (5068800 : F) * nB ^ 2 * nD
    - (2073600 : F) * nB ^ 2 * nS
    + (4276800 : F) * nB * nC ^ 2
    - (933120 : F) * nB * nC * nR
    - (23224320 : F) * nB * nD * nQ
    - (414720 : F) * nB * nE * nP
    + (124416 : F) * nB * nV
    - (9797760 : F) * nC ^ 2 * nQ
    - (22394880 : F) * nC * nD * nP
    + (1119744 : F) * nC * nU
    - (345600 : F) * nD * nE
    + (995328 : F) * nD * nT
    + (311040 : F) * nE * nS

end BridgeKappaDepression610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 400000000 in
/-- The atom-level clearing: one `field_simp` over 15 atomic variables in
place of the single enormous `field_simp` on the substituted rational function. -/
theorem speedBridgeKappaResidual610Scaled55_eq (h : F) (hh : h ≠ 0) (nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) :
    (3761479876608 : F) * h ^ 55 *
        bridgeKappaResidual610
          (nL / 3)
          (nA / (12 * h ^ 10))
          (nB / (54 * h ^ 15))
          (nC / (144 * h ^ 20))
          (nD / (324 * h ^ 25))
          (nE / (46656 * h ^ 30))
          (nP / (4 * h ^ 10))
          (nQ / (9 * h ^ 15))
          (nR / (432 * h ^ 20))
          (nS / (216 * h ^ 25))
          (nT / (7776 * h ^ 30))
          (nU / (11664 * h ^ 35))
          (nV / (186624 * h ^ 40))
          (nW / (5038848 * h ^ 45)) =
      speedBridgeKappaResidual610Scaled55 h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW := by
  have hd2 : (2 : F) ≠ 0 := by norm_num
  have hd3 : (3 : F) ≠ 0 := by norm_num
  have hd4 : (4 : F) ≠ 0 := by norm_num
  have hd9 : (9 : F) ≠ 0 := by norm_num
  have hd12 : (12 : F) ≠ 0 := by norm_num
  have hd54 : (54 : F) ≠ 0 := by norm_num
  have hd144 : (144 : F) ≠ 0 := by norm_num
  have hd216 : (216 : F) ≠ 0 := by norm_num
  have hd324 : (324 : F) ≠ 0 := by norm_num
  have hd432 : (432 : F) ≠ 0 := by norm_num
  have hd7776 : (7776 : F) ≠ 0 := by norm_num
  have hd11664 : (11664 : F) ≠ 0 := by norm_num
  have hd46656 : (46656 : F) ≠ 0 := by norm_num
  have hd186624 : (186624 : F) ≠ 0 := by norm_num
  have hd5038848 : (5038848 : F) ≠ 0 := by norm_num
  have hp10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hp15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hp20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hp25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hp30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hp35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hp40 : h ^ 40 ≠ 0 := pow_ne_zero 40 hh
  have hp45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  simp only [alphaResidual610, betaResidual610, bridgeKappaResidual610, bridgeThetaResidual610, deltaResidual610, epsilonResidual610, etaResidual610, gammaResidual610, zetaResidual610, speedBridgeKappaResidual610Scaled55]
  field_simp
  ring

end BridgeKappaDepression610

end Max11DegreeRoutes
