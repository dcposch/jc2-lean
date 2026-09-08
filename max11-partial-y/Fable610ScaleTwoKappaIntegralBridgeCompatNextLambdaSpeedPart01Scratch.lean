import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart01Scratch

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
