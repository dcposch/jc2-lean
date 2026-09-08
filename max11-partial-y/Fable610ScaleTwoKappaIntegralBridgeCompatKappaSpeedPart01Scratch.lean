import Fable610ScaleTwoKappaIntegralBridgeCompatPart03Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart04Scratch

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
