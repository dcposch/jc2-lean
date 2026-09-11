import LowScale46SourceBridge
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart101Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaDepression610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 400000000 in
/-- SPEED (recipe R2, `scripts/coord/LEAN_SPEED_REPORT.md` §7): the weight-`60`
clearing of `bridgeLambdaResidual610` carried out on the *atoms* rather than on the fully
substituted source polynomials.  `bridgeLambdaResidual610` is weighted homogeneous, so
substituting `X_i = n_i / (d_i h^(e_i))` makes `258280326 * h^60 * bridgeLambdaResidual610`
a polynomial in `h, n_*` — 56 monomials. -/
def speedBridgeLambdaResidual610Scaled60 (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    (13365 / 256 : F) * h ^ 5 * nL * nA ^ 4 * nB
    - (3645 / 32 : F) * h ^ 5 * nL * nA ^ 3 * nD
    - (10935 / 64 : F) * h ^ 5 * nL * nA ^ 2 * nB * nC
    - (135 / 4 : F) * h ^ 5 * nL * nA * nB ^ 3
    + (1215 / 256 : F) * h ^ 5 * nL * nA * nB * nE
    + (32805 / 128 : F) * h ^ 5 * nL * nA * nC * nD
    + (1215 / 16 : F) * h ^ 5 * nL * nB ^ 2 * nD
    + (32805 / 512 : F) * h ^ 5 * nL * nB * nC ^ 2
    - (729 / 128 : F) * h ^ 5 * nL * nD * nE
    - (10395 / 1024 : F) * nA ^ 6
    + (8019 / 256 : F) * nA ^ 5 * nP
    + (66825 / 1024 : F) * nA ^ 4 * nC
    - (3645 / 1024 : F) * nA ^ 4 * nR
    + (2475 / 32 : F) * nA ^ 3 * nB ^ 2
    - (2835 / 16 : F) * nA ^ 3 * nB * nQ
    - (10935 / 64 : F) * nA ^ 3 * nC * nP
    - (675 / 256 : F) * nA ^ 3 * nE
    + (1215 / 512 : F) * nA ^ 3 * nT
    - (1215 / 8 : F) * nA ^ 2 * nB ^ 2 * nP
    - (2025 / 8 : F) * nA ^ 2 * nB * nD
    + (18225 / 256 : F) * nA ^ 2 * nB * nS
    - (54675 / 512 : F) * nA ^ 2 * nC ^ 2
    + (32805 / 2048 : F) * nA ^ 2 * nC * nR
    + (25515 / 64 : F) * nA ^ 2 * nD * nQ
    + (3645 / 512 : F) * nA ^ 2 * nE * nP
    - (2187 / 2048 : F) * nA ^ 2 * nV
    - (2025 / 16 : F) * nA * nB ^ 2 * nC
    + (1215 / 128 : F) * nA * nB ^ 2 * nR
    + (25515 / 64 : F) * nA * nB * nC * nQ
    + (3645 / 8 : F) * nA * nB * nD * nP
    - (729 / 64 : F) * nA * nB * nU
    + (98415 / 512 : F) * nA * nC ^ 2 * nP
    + (6075 / 1024 : F) * nA * nC * nE
    - (2187 / 256 : F) * nA * nC * nT
    + (6075 / 32 : F) * nA * nD ^ 2
    - (10935 / 64 : F) * nA * nD * nS
    - (729 / 1024 : F) * nA * nE * nR
    - (25 / 4 : F) * nB ^ 4
    + (315 / 8 : F) * nB ^ 3 * nQ
    + (3645 / 32 : F) * nB ^ 2 * nC * nP
    + (225 / 128 : F) * nB ^ 2 * nE
    - (81 / 32 : F) * nB ^ 2 * nT
    + (6075 / 32 : F) * nB * nC * nD
    - (10935 / 128 : F) * nB * nC * nS
    - (729 / 32 : F) * nB * nD * nR
    - (567 / 64 : F) * nB * nE * nQ
    + (81 / 512 : F) * nB * nW
    + (54675 / 2048 : F) * nC ^ 3
    - (19683 / 2048 : F) * nC ^ 2 * nR
    - (15309 / 32 : F) * nC * nD * nQ
    - (2187 / 256 : F) * nC * nE * nP
    + (6561 / 2048 : F) * nC * nV
    - (2187 / 8 : F) * nD ^ 2 * nP
    + (2187 / 64 : F) * nD * nU
    - (135 / 2048 : F) * nE ^ 2
    + (243 / 512 : F) * nE * nT

end BridgeLambdaDepression610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaDepression610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 400000000 in
/-- The atom-level clearing: one `field_simp` over 15 atomic variables in
place of the single enormous `field_simp` on the substituted rational function. -/
theorem speedBridgeLambdaResidual610Scaled60_eq (h : F) (hh : h ≠ 0) (nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) :
    (258280326 : F) * h ^ 60 *
        bridgeLambdaResidual610
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
      speedBridgeLambdaResidual610Scaled60 h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW := by
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
  simp only [alphaResidual610, betaResidual610, bridgeLambdaResidual610, bridgeThetaResidual610, deltaResidual610, epsilonResidual610, etaResidual610, gammaResidual610, zetaResidual610, speedBridgeLambdaResidual610Scaled60]
  field_simp
  ring

end BridgeLambdaDepression610

end Max11DegreeRoutes
