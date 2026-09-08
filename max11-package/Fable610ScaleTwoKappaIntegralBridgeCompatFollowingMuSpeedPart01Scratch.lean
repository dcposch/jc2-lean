import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart01Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuDepression610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 400000000 in
/-- SPEED (recipe R2, `scripts/coord/LEAN_SPEED_REPORT.md` §7): the weight-`65`
clearing of `bridgeMuResidual610` carried out on the *atoms* rather than on the fully
substituted source polynomials.  `bridgeMuResidual610` is weighted homogeneous, so
substituting `X_i = n_i / (d_i h^(e_i))` makes `12582912 * h^65 * bridgeMuResidual610`
a polynomial in `h, n_*` — 68 monomials. -/
def speedBridgeMuResidual610Scaled65 (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    - (7 / 81 : F) * h ^ 5 * nL * nA ^ 6
    + (140 / 243 : F) * h ^ 5 * nL * nA ^ 4 * nC
    + (4480 / 6561 : F) * h ^ 5 * nL * nA ^ 3 * nB ^ 2
    - (160 / 6561 : F) * h ^ 5 * nL * nA ^ 3 * nE
    - (5120 / 2187 : F) * h ^ 5 * nL * nA ^ 2 * nB * nD
    - (80 / 81 : F) * h ^ 5 * nL * nA ^ 2 * nC ^ 2
    - (2560 / 2187 : F) * h ^ 5 * nL * nA * nB ^ 2 * nC
    + (128 / 2187 : F) * h ^ 5 * nL * nA * nC * nE
    + (4096 / 2187 : F) * h ^ 5 * nL * nA * nD ^ 2
    - (10240 / 177147 : F) * h ^ 5 * nL * nB ^ 4
    + (1024 / 59049 : F) * h ^ 5 * nL * nB ^ 2 * nE
    + (4096 / 2187 : F) * h ^ 5 * nL * nB * nC * nD
    + (64 / 243 : F) * h ^ 5 * nL * nC ^ 3
    - (128 / 177147 : F) * h ^ 5 * nL * nE ^ 2
    - (280 / 729 : F) * nA ^ 5 * nB
    + (784 / 2187 : F) * nA ^ 5 * nQ
    + (2240 / 2187 : F) * nA ^ 4 * nB * nP
    + (5600 / 6561 : F) * nA ^ 4 * nD
    - (400 / 2187 : F) * nA ^ 4 * nS
    + (11200 / 6561 : F) * nA ^ 3 * nB * nC
    - (640 / 6561 : F) * nA ^ 3 * nB * nR
    - (4480 / 2187 : F) * nA ^ 3 * nC * nQ
    - (5120 / 2187 : F) * nA ^ 3 * nD * nP
    + (256 / 6561 : F) * nA ^ 3 * nU
    + (89600 / 177147 : F) * nA ^ 2 * nB ^ 3
    - (35840 / 19683 : F) * nA ^ 2 * nB ^ 2 * nQ
    - (2560 / 729 : F) * nA ^ 2 * nB * nC * nP
    - (3200 / 59049 : F) * nA ^ 2 * nB * nE
    + (1024 / 19683 : F) * nA ^ 2 * nB * nT
    - (6400 / 2187 : F) * nA ^ 2 * nC * nD
    + (640 / 729 : F) * nA ^ 2 * nC * nS
    + (512 / 2187 : F) * nA ^ 2 * nD * nR
    + (1792 / 19683 : F) * nA ^ 2 * nE * nQ
    - (128 / 177147 : F) * nA ^ 2 * nW
    - (40960 / 59049 : F) * nA * nB ^ 3 * nP
    - (102400 / 59049 : F) * nA * nB ^ 2 * nD
    + (10240 / 19683 : F) * nA * nB ^ 2 * nS
    - (3200 / 2187 : F) * nA * nB * nC ^ 2
    + (512 / 2187 : F) * nA * nB * nC * nR
    + (114688 / 19683 : F) * nA * nB * nD * nQ
    + (2048 / 19683 : F) * nA * nB * nE * nP
    - (1024 / 59049 : F) * nA * nB * nV
    + (1792 / 729 : F) * nA * nC ^ 2 * nQ
    + (4096 / 729 : F) * nA * nC * nD * nP
    - (1024 / 6561 : F) * nA * nC * nU
    + (5120 / 59049 : F) * nA * nD * nE
    - (8192 / 59049 : F) * nA * nD * nT
    - (2560 / 59049 : F) * nA * nE * nS
    - (51200 / 177147 : F) * nB ^ 3 * nC
    + (4096 / 177147 : F) * nB ^ 3 * nR
    + (28672 / 19683 : F) * nB ^ 2 * nC * nQ
    + (32768 / 19683 : F) * nB ^ 2 * nD * nP
    - (8192 / 177147 : F) * nB ^ 2 * nU
    + (1024 / 729 : F) * nB * nC ^ 2 * nP
    + (2560 / 59049 : F) * nB * nC * nE
    - (4096 / 59049 : F) * nB * nC * nT
    + (81920 / 59049 : F) * nB * nD ^ 2
    - (81920 / 59049 : F) * nB * nD * nS
    - (1024 / 177147 : F) * nB * nE * nR
    + (2560 / 2187 : F) * nC ^ 2 * nD
    - (1280 / 2187 : F) * nC ^ 2 * nS
    - (2048 / 6561 : F) * nC * nD * nR
    - (7168 / 59049 : F) * nC * nE * nQ
    + (512 / 177147 : F) * nC * nW
    - (229376 / 59049 : F) * nD ^ 2 * nQ
    - (8192 / 59049 : F) * nD * nE * nP
    + (4096 / 59049 : F) * nD * nV
    + (2048 / 177147 : F) * nE * nU

end BridgeMuDepression610

end Max11DegreeRoutes
