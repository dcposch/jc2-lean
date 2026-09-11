import Fable610ScaleTwoKappaIntegralBridgeCompatPart101Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart101Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingMuSpeedPart01Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuDepression610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 400000000 in
/-- The atom-level clearing: one `field_simp` over 15 atomic variables in
place of the single enormous `field_simp` on the substituted rational function. -/
theorem speedBridgeMuResidual610Scaled65_eq (h : F) (hh : h ≠ 0) (nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) :
    (12582912 : F) * h ^ 65 *
        bridgeMuResidual610
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
      speedBridgeMuResidual610Scaled65 h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW := by
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
  simp only [alphaResidual610, betaResidual610, bridgeMuResidual610, bridgeThetaResidual610, deltaResidual610, epsilonResidual610, etaResidual610, gammaResidual610, zetaResidual610, speedBridgeMuResidual610Scaled65]
  field_simp
  ring

end BridgeMuDepression610

end Max11DegreeRoutes
