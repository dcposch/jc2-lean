import Grok810ScaleZeroConeExhaustionScratch

/-! # Seven-integral packet for the normalized `(8,10)`, `H = 0` leaf

Lane L0 of `Grok810ScaleZeroQuarticCoordinateTowerPlanScratch.md`.
The parent residual `normalized810ScaleZero_coneExhaustionResidual`
already exports constant `ξ`, `μ`, `ο` and a degree-one primitive.
This file pulls back the three unused first integrals `κ`, `ν`, `π`
(weights 11, 13, 16) as degree-zero polynomials in the letters, by the
same substitution that produced `degreeZeroXiPolynomial810`,
`degreeZeroMuPolynomial810`, and `degreeZeroOmicronPolynomial810`:
`alphaResidual810 → 0` and the triangular load residuals → the ground
loads.  CAS `scripts/derive_810_scale_zero_seven_integrals.py` asserts
isobaricity of all seven objects under weights
`A,B,C0,D0,E0,F0,G0,l,beta,gamma,delta,epsilon,zeta,eta,theta =
2,3,4,5,6,7,8,1,3,4,5,6,7,8,9`.

The source-facing packet extends the parent conjuncts (`t ≠ 0`, `j ≠ 0`,
`j/t ≠ 0`, `H = (C t)²`, `derivative ρ = C (j/t)`, `natDegree 0` for
`ξ,μ,ο`) by `natDegree 0` for `κ,ν,π`.  Cone negations are dropped
(Stage A does not need them).  No `sorry`, no new axioms, no finite-root
shortcut.  The theorems `normalized810ScaleZero_impossible` and
`planeKeller810ScaleZeroExclusion_closed` are not claimed.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-! ## Polynomial pullbacks of `κ`, `ν`, `π` -/

section SevenIntegralPolynomials810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000 in
/-- Polynomial pullback of `kappaResidual810` after triangular
substitution.  CAS: isobaric of weight 11, 44 terms. -/
def degreeZeroKappaPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(385 / 8192 : k) • (A ^ 4 * B)
  + (35 / 512 : k) • (A ^ 3 * D0)
  + (105 / 512 : k) • (A ^ 2 * B * C0)
  - (15 / 128 : k) • (A ^ 2 * F0)
  + (35 / 512 : k) • (A * B ^ 3)
  - (15 / 64 : k) • (A * B * E0)
  - (15 / 64 : k) • (A * C0 * D0)
  - (15 / 128 : k) • (B ^ 2 * D0)
  - (15 / 128 : k) • (B * C0 ^ 2)
  + (5 / 16 : k) • (B * G0)
  + (5 / 16 : k) • (C0 * F0)
  + (5 / 16 : k) • (D0 * E0)
  - (1449 / 262144 * l : k) • A ^ 5
  + (315 / 8192 * l : k) • (A ^ 3 * C0)
  + (945 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  - (63 / 1024 * l : k) • (A ^ 2 * E0)
  - (63 / 512 * l : k) • (A * B * D0)
  - (63 / 1024 * l : k) • (A * C0 ^ 2)
  + (9 / 64 * l : k) • (A * G0)
  - (63 / 1024 * l : k) • (B ^ 2 * C0)
  + (9 / 64 * l : k) • (B * F0)
  + (9 / 64 * l : k) • (C0 * E0)
  + (9 / 128 * l : k) • D0 ^ 2
  - (357 / 32768 * beta : k) • A ^ 4
  + (63 / 1024 * beta : k) • (A ^ 2 * C0)
  + (63 / 1024 * beta : k) • (A * B ^ 2)
  - (7 / 64 * beta : k) • (A * E0)
  - (7 / 64 * beta : k) • (B * D0)
  - (7 / 128 * beta : k) • C0 ^ 2
  + (7 / 8 * beta : k) • G0
  + (15 / 128 * gamma : k) • (A ^ 2 * B)
  - (3 / 16 * gamma : k) • (A * D0)
  - (3 / 16 * gamma : k) • (B * C0)
  + (3 / 4 * gamma : k) • F0
  + (55 / 1024 * delta : k) • A ^ 3
  - (15 / 64 * delta : k) • (A * C0)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E0
  - (1 / 4 * epsilon : k) • (A * B)
  + (1 / 2 * epsilon : k) • D0
  - (15 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C0
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 8000000 in
/-- Field-level integrated `κ`. -/
def degreeZeroKappaIntegrated810
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 beta gamma delta epsilon zeta eta theta : F) : F :=
  -(385 / 8192 : F) * (A ^ 4 * B)
  + (35 / 512 : F) * (A ^ 3 * D0)
  + (105 / 512 : F) * (A ^ 2 * B * C0)
  - (15 / 128 : F) * (A ^ 2 * F0)
  + (35 / 512 : F) * (A * B ^ 3)
  - (15 / 64 : F) * (A * B * E0)
  - (15 / 64 : F) * (A * C0 * D0)
  - (15 / 128 : F) * (B ^ 2 * D0)
  - (15 / 128 : F) * (B * C0 ^ 2)
  + (5 / 16 : F) * (B * G0)
  + (5 / 16 : F) * (C0 * F0)
  + (5 / 16 : F) * (D0 * E0)
  - (1449 / 262144 : F) * L * A ^ 5
  + (315 / 8192 : F) * L * (A ^ 3 * C0)
  + (945 / 16384 : F) * L * (A ^ 2 * B ^ 2)
  - (63 / 1024 : F) * L * (A ^ 2 * E0)
  - (63 / 512 : F) * L * (A * B * D0)
  - (63 / 1024 : F) * L * (A * C0 ^ 2)
  + (9 / 64 : F) * L * (A * G0)
  - (63 / 1024 : F) * L * (B ^ 2 * C0)
  + (9 / 64 : F) * L * (B * F0)
  + (9 / 64 : F) * L * (C0 * E0)
  + (9 / 128 : F) * L * D0 ^ 2
  - (357 / 32768 : F) * beta * A ^ 4
  + (63 / 1024 : F) * beta * (A ^ 2 * C0)
  + (63 / 1024 : F) * beta * (A * B ^ 2)
  - (7 / 64 : F) * beta * (A * E0)
  - (7 / 64 : F) * beta * (B * D0)
  - (7 / 128 : F) * beta * C0 ^ 2
  + (7 / 8 : F) * beta * G0
  + (15 / 128 : F) * gamma * (A ^ 2 * B)
  - (3 / 16 : F) * gamma * (A * D0)
  - (3 / 16 : F) * gamma * (B * C0)
  + (3 / 4 : F) * gamma * F0
  + (55 / 1024 : F) * delta * A ^ 3
  - (15 / 64 : F) * delta * (A * C0)
  - (15 / 128 : F) * delta * B ^ 2
  + (5 / 8 : F) * delta * E0
  - (1 / 4 : F) * epsilon * (A * B)
  + (1 / 2 : F) * epsilon * D0
  - (15 / 128 : F) * zeta * A ^ 2
  + (3 / 8 : F) * zeta * C0
  + (1 / 4 : F) * eta * B
  + (1 / 8 : F) * theta * A

/- nu polynomial (CAS, loads substituted) -/

set_option maxHeartbeats 8000000 in
/-- Polynomial pullback of `nuResidual810` after triangular
substitution.  CAS: isobaric of weight 13, 73 terms. -/
def degreeZeroNuPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (1925 / 65536 : k) • (A ^ 5 * B)
  - (315 / 8192 : k) • (A ^ 4 * D0)
  - (665 / 4096 : k) • (A ^ 3 * B * C0)
  + (55 / 1024 : k) • (A ^ 3 * F0)
  - (175 / 2048 : k) • (A ^ 2 * B ^ 3)
  + (45 / 256 : k) • (A ^ 2 * B * E0)
  + (45 / 256 : k) • (A ^ 2 * C0 * D0)
  + (195 / 1024 : k) • (A * B ^ 2 * D0)
  + (195 / 1024 : k) • (A * B * C0 ^ 2)
  - (25 / 128 : k) • (A * B * G0)
  - (25 / 128 : k) • (A * C0 * F0)
  - (25 / 128 : k) • (A * D0 * E0)
  + (35 / 512 : k) • (B ^ 3 * C0)
  - (15 / 128 : k) • (B ^ 2 * F0)
  - (15 / 64 : k) • (B * C0 * E0)
  - (15 / 128 : k) • (B * D0 ^ 2)
  - (15 / 128 : k) • (C0 ^ 2 * D0)
  + (5 / 16 : k) • (D0 * G0)
  + (5 / 16 : k) • (E0 * F0)
  + (12075 / 4194304 * l : k) • A ^ 6
  - (5985 / 262144 * l : k) • (A ^ 4 * C0)
  - (1575 / 32768 * l : k) • (A ^ 3 * B ^ 2)
  + (63 / 2048 * l : k) • (A ^ 3 * E0)
  + (819 / 8192 * l : k) • (A ^ 2 * B * D0)
  + (819 / 16384 * l : k) • (A ^ 2 * C0 ^ 2)
  - (45 / 1024 * l : k) • (A ^ 2 * G0)
  + (441 / 4096 * l : k) • (A * B ^ 2 * C0)
  - (27 / 256 * l : k) • (A * B * F0)
  - (27 / 256 * l : k) • (A * C0 * E0)
  - (27 / 512 * l : k) • (A * D0 ^ 2)
  + (315 / 32768 * l : k) • B ^ 4
  - (63 / 1024 * l : k) • (B ^ 2 * E0)
  - (63 / 512 * l : k) • (B * C0 * D0)
  - (21 / 1024 * l : k) • C0 ^ 3
  + (9 / 64 * l : k) • (C0 * G0)
  + (9 / 64 * l : k) • (D0 * F0)
  + (9 / 128 * l : k) • E0 ^ 2
  + (357 / 65536 * beta : k) • A ^ 5
  - (147 / 4096 * beta : k) • (A ^ 3 * C0)
  - (945 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (49 / 1024 * beta : k) • (A ^ 2 * E0)
  + (7 / 64 * beta : k) • (A * B * D0)
  + (7 / 128 * beta : k) • (A * C0 ^ 2)
  + (63 / 1024 * beta : k) • (B ^ 2 * C0)
  - (7 / 64 * beta : k) • (B * F0)
  - (7 / 64 * beta : k) • (C0 * E0)
  - (7 / 128 * beta : k) • D0 ^ 2
  - (75 / 1024 * gamma : k) • (A ^ 3 * B)
  + (3 / 32 * gamma : k) • (A ^ 2 * D0)
  + (27 / 128 * gamma : k) • (A * B * C0)
  - (3 / 32 * gamma : k) • (A * F0)
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 16 * gamma : k) • (B * E0)
  - (3 / 16 * gamma : k) • (C0 * D0)
  - (825 / 32768 * delta : k) • A ^ 4
  + (135 / 1024 * delta : k) • (A ^ 2 * C0)
  + (75 / 512 * delta : k) • (A * B ^ 2)
  - (5 / 32 * delta : k) • (A * E0)
  - (15 / 64 * delta : k) • (B * D0)
  - (15 / 128 * delta : k) • C0 ^ 2
  + (5 / 8 * delta : k) • G0
  + (5 / 32 * epsilon : k) • (A ^ 2 * B)
  - (3 / 16 * epsilon : k) • (A * D0)
  - (1 / 4 * epsilon : k) • (B * C0)
  + (1 / 2 * epsilon : k) • F0
  + (25 / 512 * zeta : k) • A ^ 3
  - (3 / 16 * zeta : k) • (A * C0)
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E0
  - (5 / 32 * eta : k) • (A * B)
  + (1 / 4 * eta : k) • D0
  - (5 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C0

set_option maxHeartbeats 8000000 in
/-- Field-level integrated `ν`. -/
def degreeZeroNuIntegrated810
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 beta gamma delta epsilon zeta eta theta : F) : F :=
  (1925 / 65536 : F) * (A ^ 5 * B)
  - (315 / 8192 : F) * (A ^ 4 * D0)
  - (665 / 4096 : F) * (A ^ 3 * B * C0)
  + (55 / 1024 : F) * (A ^ 3 * F0)
  - (175 / 2048 : F) * (A ^ 2 * B ^ 3)
  + (45 / 256 : F) * (A ^ 2 * B * E0)
  + (45 / 256 : F) * (A ^ 2 * C0 * D0)
  + (195 / 1024 : F) * (A * B ^ 2 * D0)
  + (195 / 1024 : F) * (A * B * C0 ^ 2)
  - (25 / 128 : F) * (A * B * G0)
  - (25 / 128 : F) * (A * C0 * F0)
  - (25 / 128 : F) * (A * D0 * E0)
  + (35 / 512 : F) * (B ^ 3 * C0)
  - (15 / 128 : F) * (B ^ 2 * F0)
  - (15 / 64 : F) * (B * C0 * E0)
  - (15 / 128 : F) * (B * D0 ^ 2)
  - (15 / 128 : F) * (C0 ^ 2 * D0)
  + (5 / 16 : F) * (D0 * G0)
  + (5 / 16 : F) * (E0 * F0)
  + (12075 / 4194304 : F) * L * A ^ 6
  - (5985 / 262144 : F) * L * (A ^ 4 * C0)
  - (1575 / 32768 : F) * L * (A ^ 3 * B ^ 2)
  + (63 / 2048 : F) * L * (A ^ 3 * E0)
  + (819 / 8192 : F) * L * (A ^ 2 * B * D0)
  + (819 / 16384 : F) * L * (A ^ 2 * C0 ^ 2)
  - (45 / 1024 : F) * L * (A ^ 2 * G0)
  + (441 / 4096 : F) * L * (A * B ^ 2 * C0)
  - (27 / 256 : F) * L * (A * B * F0)
  - (27 / 256 : F) * L * (A * C0 * E0)
  - (27 / 512 : F) * L * (A * D0 ^ 2)
  + (315 / 32768 : F) * L * B ^ 4
  - (63 / 1024 : F) * L * (B ^ 2 * E0)
  - (63 / 512 : F) * L * (B * C0 * D0)
  - (21 / 1024 : F) * L * C0 ^ 3
  + (9 / 64 : F) * L * (C0 * G0)
  + (9 / 64 : F) * L * (D0 * F0)
  + (9 / 128 : F) * L * E0 ^ 2
  + (357 / 65536 : F) * beta * A ^ 5
  - (147 / 4096 : F) * beta * (A ^ 3 * C0)
  - (945 / 16384 : F) * beta * (A ^ 2 * B ^ 2)
  + (49 / 1024 : F) * beta * (A ^ 2 * E0)
  + (7 / 64 : F) * beta * (A * B * D0)
  + (7 / 128 : F) * beta * (A * C0 ^ 2)
  + (63 / 1024 : F) * beta * (B ^ 2 * C0)
  - (7 / 64 : F) * beta * (B * F0)
  - (7 / 64 : F) * beta * (C0 * E0)
  - (7 / 128 : F) * beta * D0 ^ 2
  - (75 / 1024 : F) * gamma * (A ^ 3 * B)
  + (3 / 32 : F) * gamma * (A ^ 2 * D0)
  + (27 / 128 : F) * gamma * (A * B * C0)
  - (3 / 32 : F) * gamma * (A * F0)
  + (5 / 128 : F) * gamma * B ^ 3
  - (3 / 16 : F) * gamma * (B * E0)
  - (3 / 16 : F) * gamma * (C0 * D0)
  - (825 / 32768 : F) * delta * A ^ 4
  + (135 / 1024 : F) * delta * (A ^ 2 * C0)
  + (75 / 512 : F) * delta * (A * B ^ 2)
  - (5 / 32 : F) * delta * (A * E0)
  - (15 / 64 : F) * delta * (B * D0)
  - (15 / 128 : F) * delta * C0 ^ 2
  + (5 / 8 : F) * delta * G0
  + (5 / 32 : F) * epsilon * (A ^ 2 * B)
  - (3 / 16 : F) * epsilon * (A * D0)
  - (1 / 4 : F) * epsilon * (B * C0)
  + (1 / 2 : F) * epsilon * F0
  + (25 / 512 : F) * zeta * A ^ 3
  - (3 / 16 : F) * zeta * (A * C0)
  - (15 / 128 : F) * zeta * B ^ 2
  + (3 / 8 : F) * zeta * E0
  - (5 / 32 : F) * eta * (A * B)
  + (1 / 4 : F) * eta * D0
  - (5 / 128 : F) * theta * A ^ 2
  + (1 / 8 : F) * theta * C0

/- pi groups, denominators cleared -/

set_option maxHeartbeats 8000000 in
/-- Polynomial groups of `π`, denominators cleared. -/
def piBetaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  -(1785 / 32768 : k) • (A ^ 5 * B)
  + (147 / 2048 : k) • (A ^ 4 * D0)
  + (1239 / 4096 : k) • (A ^ 3 * B * C0)
  - (77 / 1024 : k) • (A ^ 3 * F0)
  + (315 / 2048 : k) • (A ^ 2 * B ^ 3)
  - (161 / 512 : k) • (A ^ 2 * B * E0)
  - (175 / 512 : k) • (A ^ 2 * C0 * D0)
  - (175 / 512 : k) • (A * B ^ 2 * D0)
  - (91 / 256 : k) • (A * B * C0 ^ 2)
  + (21 / 64 : k) • (A * C0 * F0)
  + (7 / 16 : k) • (A * D0 * E0)
  - (63 / 512 : k) • (B ^ 3 * C0)
  + (21 / 128 : k) • (B ^ 2 * F0)
  + (7 / 16 : k) • (B * C0 * E0)
  + (7 / 32 : k) • (B * D0 ^ 2)
  + (7 / 32 : k) • (C0 ^ 2 * D0)
  - (7 / 8 : k) • (E0 * F0)

set_option maxHeartbeats 8000000 in
def piGammaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  -(75 / 4096 : k) • A ^ 6
  + (75 / 512 : k) • (A ^ 4 * C0)
  + (75 / 256 : k) • (A ^ 3 * B ^ 2)
  - (3 / 16 : k) • (A ^ 3 * E0)
  - (39 / 64 : k) • (A ^ 2 * B * D0)
  - (21 / 64 : k) • (A ^ 2 * C0 ^ 2)
  - (21 / 32 : k) • (A * B ^ 2 * C0)
  + (3 / 8 : k) • (A * B * F0)
  + (3 / 4 : k) • (A * C0 * E0)
  + (3 / 8 : k) • (A * D0 ^ 2)
  - (15 / 256 : k) • B ^ 4
  + (3 / 8 : k) • (B ^ 2 * E0)
  + (3 / 4 : k) • (B * C0 * D0)
  + (1 / 8 : k) • C0 ^ 3
  - (3 / 4 : k) • (D0 * F0)
  - (3 / 4 : k) • E0 ^ 2

set_option maxHeartbeats 8000000 in
def piDeltaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  (825 / 4096 : k) • (A ^ 4 * B)
  - (135 / 512 : k) • (A ^ 3 * D0)
  - (435 / 512 : k) • (A ^ 2 * B * C0)
  + (25 / 128 : k) • (A ^ 2 * F0)
  - (75 / 256 : k) • (A * B ^ 3)
  + (25 / 32 : k) • (A * B * E0)
  + (15 / 16 : k) • (A * C0 * D0)
  + (15 / 32 : k) • (B ^ 2 * D0)
  + (15 / 32 : k) • (B * C0 ^ 2)
  - (5 / 8 : k) • (C0 * F0)
  - (5 / 4 : k) • (D0 * E0)

set_option maxHeartbeats 8000000 in
def piEpsilonGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  (3 / 64 : k) • A ^ 5
  - (5 / 16 : k) • (A ^ 3 * C0)
  - (15 / 32 : k) • (A ^ 2 * B ^ 2)
  + (3 / 8 : k) • (A ^ 2 * E0)
  + (7 / 8 : k) • (A * B * D0)
  + (1 / 2 : k) • (A * C0 ^ 2)
  + (1 / 2 : k) • (B ^ 2 * C0)
  - (1 / 2 : k) • (B * F0)
  - (1 : k) • (C0 * E0)
  - (1 / 2 : k) • D0 ^ 2

set_option maxHeartbeats 8000000 in
def piZetaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) : k[X] :=
  -(75 / 256 : k) • (A ^ 3 * B)
  + (3 / 8 : k) • (A ^ 2 * D0)
  + (27 / 32 : k) • (A * B * C0)
  - (3 / 8 : k) • (A * F0)
  + (5 / 32 : k) • B ^ 3
  - (3 / 4 : k) • (B * E0)
  - (3 / 4 : k) • (C0 * D0)

set_option maxHeartbeats 8000000 in
def piEtaGroupPolynomial810
    (A B C0 D0 E0 G0 : k[X]) : k[X] :=
  -(15 / 256 : k) • A ^ 4
  + (5 / 16 : k) • (A ^ 2 * C0)
  + (5 / 16 : k) • (A * B ^ 2)
  - (1 / 2 : k) • (A * E0)
  - (1 / 2 : k) • (B * D0)
  - (1 / 4 : k) • C0 ^ 2
  + (2 : k) • G0

set_option maxHeartbeats 8000000 in
def piThetaGroupPolynomial810
    (A B C0 D0 F0 : k[X]) : k[X] :=
  (5 / 32 : k) • (A ^ 2 * B)
  - (1 / 4 : k) • (A * D0)
  - (1 / 4 : k) • (B * C0)
  + (1 : k) • F0

set_option maxHeartbeats 16000000 in
def piBaseGroupPolynomial810
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (5775 / 1048576 : k) • A ^ 8
  - (1925 / 32768 : k) • (A ^ 6 * C0)
  - (5775 / 32768 : k) • (A ^ 5 * B ^ 2)
  + (315 / 4096 : k) • (A ^ 5 * E0)
  + (1645 / 4096 : k) • (A ^ 4 * B * D0)
  + (1715 / 8192 : k) • (A ^ 4 * C0 ^ 2)
  - (75 / 1024 : k) • (A ^ 4 * G0)
  + (1715 / 2048 : k) • (A ^ 3 * B ^ 2 * C0)
  - (25 / 64 : k) • (A ^ 3 * B * F0)
  - (125 / 256 : k) • (A ^ 3 * C0 * E0)
  - (125 / 512 : k) • (A ^ 3 * D0 ^ 2)
  + (875 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (375 / 512 : k) • (A ^ 2 * B ^ 2 * E0)
  - (195 / 128 : k) • (A ^ 2 * B * C0 * D0)
  - (135 / 512 : k) • (A ^ 2 * C0 ^ 3)
  + (25 / 64 : k) • (A ^ 2 * C0 * G0)
  + (65 / 128 : k) • (A ^ 2 * D0 * F0)
  + (5 / 16 : k) • (A ^ 2 * E0 ^ 2)
  - (265 / 512 : k) • (A * B ^ 3 * D0)
  - (405 / 512 : k) • (A * B ^ 2 * C0 ^ 2)
  + (25 / 64 : k) • (A * B ^ 2 * G0)
  + (35 / 32 : k) • (A * B * C0 * F0)
  + (85 / 64 : k) • (A * B * D0 * E0)
  + (45 / 64 : k) • (A * C0 ^ 2 * E0)
  + (45 / 64 : k) • (A * C0 * D0 ^ 2)
  - (5 / 8 : k) • (A * E0 * G0)
  - (5 / 16 : k) • (A * F0 ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C0)
  + (25 / 128 : k) • (B ^ 3 * F0)
  + (45 / 64 : k) • (B ^ 2 * C0 * E0)
  + (45 / 128 : k) • (B ^ 2 * D0 ^ 2)
  + (45 / 64 : k) • (B * C0 ^ 2 * D0)
  - (5 / 8 : k) • (B * D0 * G0)
  - (15 / 16 : k) • (B * E0 * F0)
  + (15 / 256 : k) • C0 ^ 4
  - (5 / 16 : k) • (C0 ^ 2 * G0)
  - (15 / 16 : k) • (C0 * D0 * F0)
  - (5 / 8 : k) • (C0 * E0 ^ 2)
  - (5 / 8 : k) • (D0 ^ 2 * E0)
  + (5 / 4 : k) • G0 ^ 2
  - (36225 / 1048576 * l : k) • (A ^ 6 * B)
  + (5985 / 131072 * l : k) • (A ^ 5 * D0)
  + (31185 / 131072 * l : k) • (A ^ 4 * B * C0)
  - (1701 / 32768 * l : k) • (A ^ 4 * F0)
  + (2625 / 16384 * l : k) • (A ^ 3 * B ^ 3)
  - (1071 / 4096 * l : k) • (A ^ 3 * B * E0)
  - (567 / 2048 * l : k) • (A ^ 3 * C0 * D0)
  - (1701 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D0)
  - (441 / 1024 * l : k) • (A ^ 2 * B * C0 ^ 2)
  + (45 / 256 * l : k) • (A ^ 2 * B * G0)
  + (279 / 1024 * l : k) • (A ^ 2 * C0 * F0)
  + (171 / 512 * l : k) • (A ^ 2 * D0 * E0)
  - (1197 / 4096 * l : k) • (A * B ^ 3 * C0)
  + (279 / 1024 * l : k) • (A * B ^ 2 * F0)
  + (45 / 64 * l : k) • (A * B * C0 * E0)
  + (45 / 128 * l : k) • (A * B * D0 ^ 2)
  + (189 / 512 * l : k) • (A * C0 ^ 2 * D0)
  - (9 / 32 * l : k) • (A * D0 * G0)
  - (27 / 64 * l : k) • (A * E0 * F0)
  - (63 / 4096 * l : k) • B ^ 5
  + (63 / 512 * l : k) • (B ^ 3 * E0)
  + (189 / 512 * l : k) • (B ^ 2 * C0 * D0)
  + (63 / 512 * l : k) • (B * C0 ^ 3)
  - (9 / 32 * l : k) • (B * C0 * G0)
  - (27 / 64 * l : k) • (B * D0 * F0)
  - (9 / 32 * l : k) • (B * E0 ^ 2)
  - (27 / 128 * l : k) • (C0 ^ 2 * F0)
  - (9 / 16 * l : k) • (C0 * D0 * E0)
  - (3 / 32 * l : k) • D0 ^ 3
  + (9 / 8 * l : k) • (F0 * G0)

/-- Polynomial representative of the grouped degree-one integral. -/
def degreeZeroPiPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  piBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0 +
    beta • piBetaGroupPolynomial810 A B C0 D0 E0 F0 +
    gamma • piGammaGroupPolynomial810 A B C0 D0 E0 F0 +
    delta • piDeltaGroupPolynomial810 A B C0 D0 E0 F0 +
    epsilon • piEpsilonGroupPolynomial810 A B C0 D0 E0 F0 +
    zeta • piZetaGroupPolynomial810 A B C0 D0 E0 F0 +
    eta • piEtaGroupPolynomial810 A B C0 D0 E0 G0 +
    theta • piThetaGroupPolynomial810 A B C0 D0 F0

/-- Field-level integrated `π`. -/
def degreeZeroPiIntegrated810
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 beta gamma delta epsilon zeta eta theta : F) : F :=
  piBaseGroup810 L A B C0 D0 E0 F0 G0 +
    beta * piBetaGroup810 A B C0 D0 E0 F0 +
    gamma * piGammaGroup810 A B C0 D0 E0 F0 +
    delta * piDeltaGroup810 A B C0 D0 E0 F0 +
    epsilon * piEpsilonGroup810 A B C0 D0 E0 F0 +
    zeta * piZetaGroup810 A B C0 D0 E0 F0 +
    eta * piEtaGroup810 A B C0 D0 E0 G0 +
    theta * piThetaGroup810 A B C0 D0 F0


set_option maxHeartbeats 64000000 in
theorem kappaResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    kappaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroKappaIntegrated810 L A B C0 D0 E0 F0 G0 beta gamma delta
        epsilon zeta eta theta := by
  have hW :
      W0 =
        theta +
          ((9 / 8 : F) * L * G0 +
            alphaResidual810 A P * F0 +
            (7 / 8 : F) * betaResidual810 L A B Q * E0 +
            (3 / 4 : F) * gammaResidual810 L A B C0 P R * D0 +
            (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * C0 +
            (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * B +
            (3 / 8 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 *
              A +
            (5 / 16 : F) * A * F0 + (5 / 16 : F) * B * E0 +
            (5 / 16 : F) * C0 * D0 - (5 / 128 : F) * B ^ 3 -
            (15 / 64 : F) * A * B * C0 - (15 / 128 : F) * A ^ 2 * D0 +
            (35 / 512 : F) * A ^ 3 * B +
            (9 / 64 : F) * L * A * E0 + (9 / 64 : F) * L * B * D0 +
            (9 / 128 : F) * L * C0 ^ 2 - (63 / 1024 : F) * L * A ^ 2 * C0 -
            (63 / 1024 : F) * L * A * B ^ 2 +
            (315 / 32768 : F) * L * A ^ 4 -
            (7 / 128 : F) * betaResidual810 L A B Q * B ^ 2 -
            (7 / 64 : F) * betaResidual810 L A B Q * A * C0 +
            (21 / 1024 : F) * betaResidual810 L A B Q * A ^ 3 -
            (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * B -
            (15 / 128 : F) * deltaResidual810 L A B C0 D0 P Q S0 *
              A ^ 2) := by
    have h := htheta
    simp only [thetaResidual810] at h
    linear_combination h
  simp only [kappaResidual810, degreeZeroKappaIntegrated810, hW, hbeta,
    hgamma, hdelta, hepsilon, hzeta, heta, alphaResidual810]
  ring

set_option maxHeartbeats 64000000 in
theorem nuResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    nuResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroNuIntegrated810 L A B C0 D0 E0 F0 G0 beta gamma delta
        epsilon zeta eta theta := by
  simp only [nuResidual810, degreeZeroNuIntegrated810, hbeta, hgamma,
    hdelta, hepsilon, hzeta, heta, htheta]
  ring

theorem piResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    piResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroPiIntegrated810 L A B C0 D0 E0 F0 G0 beta gamma delta
        epsilon zeta eta theta := by
  simp only [piResidual810, degreeZeroPiIntegrated810, hbeta, hgamma,
    hdelta, hepsilon, hzeta, heta, htheta]

set_option maxHeartbeats 8000000 in
theorem algebraMap_piBetaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (piBetaGroupPolynomial810 A B C0 D0 E0 F0) =
      piBetaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [piBetaGroupPolynomial810, piBetaGroup810, map_add, map_sub, map_neg, map_mul,
    map_pow, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_one]
  ring
set_option maxHeartbeats 16000000 in
theorem algebraMap_piGammaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (piGammaGroupPolynomial810 A B C0 D0 E0 F0) =
      piGammaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [piGammaGroupPolynomial810, piGammaGroup810, map_add, map_sub, map_neg, map_mul,
    map_pow, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_one]
  ring
set_option maxHeartbeats 8000000 in
theorem algebraMap_piDeltaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (piDeltaGroupPolynomial810 A B C0 D0 E0 F0) =
      piDeltaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [piDeltaGroupPolynomial810, piDeltaGroup810, map_add, map_sub, map_neg, map_mul,
    map_pow, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_one]
  ring
set_option maxHeartbeats 8000000 in
theorem algebraMap_piEpsilonGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (piEpsilonGroupPolynomial810 A B C0 D0 E0 F0) =
      piEpsilonGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [piEpsilonGroupPolynomial810, piEpsilonGroup810, map_add, map_sub, map_neg, map_mul,
    map_pow, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_one]
  ring
set_option maxHeartbeats 8000000 in
theorem algebraMap_piZetaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (piZetaGroupPolynomial810 A B C0 D0 E0 F0) =
      piZetaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [piZetaGroupPolynomial810, piZetaGroup810, map_add, map_sub, map_neg, map_mul,
    map_pow, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_one]
  ring
set_option maxHeartbeats 8000000 in
theorem algebraMap_piEtaGroupPolynomial810
    (A B C0 D0 E0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (piEtaGroupPolynomial810 A B C0 D0 E0 G0) =
      piEtaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) G0) := by
  simp only [piEtaGroupPolynomial810, piEtaGroup810, map_add, map_sub, map_neg, map_mul,
    map_pow, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_one]
  ring
set_option maxHeartbeats 8000000 in
theorem algebraMap_piThetaGroupPolynomial810
    (A B C0 D0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (piThetaGroupPolynomial810 A B C0 D0 F0) =
      piThetaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [piThetaGroupPolynomial810, piThetaGroup810, map_add, map_sub, map_neg, map_mul,
    map_pow, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_one]
  ring
set_option maxHeartbeats 64000000 in
theorem algebraMap_piBaseGroupPolynomial810
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (piBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0) =
      piBaseGroup810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0) := by
  simp only [piBaseGroupPolynomial810, piBaseGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem algebraMap_degreeZeroKappaPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroKappaPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0) =
      degreeZeroKappaIntegrated810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroKappaPolynomial810, degreeZeroKappaIntegrated810,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  try ring

set_option maxHeartbeats 32000000 in
theorem algebraMap_degreeZeroNuPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroNuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0) =
      degreeZeroNuIntegrated810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroNuPolynomial810, degreeZeroNuIntegrated810,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  try ring

set_option maxHeartbeats 16000000 in
theorem algebraMap_degreeZeroPiPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroPiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0) =
      degreeZeroPiIntegrated810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroPiPolynomial810, degreeZeroPiIntegrated810,
    map_add, Polynomial.smul_eq_C_mul, map_mul, RatFunc.algebraMap_C,
    algebraMap_piBaseGroupPolynomial810,
    algebraMap_piBetaGroupPolynomial810,
    algebraMap_piGammaGroupPolynomial810,
    algebraMap_piDeltaGroupPolynomial810,
    algebraMap_piEpsilonGroupPolynomial810,
    algebraMap_piZetaGroupPolynomial810,
    algebraMap_piEtaGroupPolynomial810,
    algebraMap_piThetaGroupPolynomial810]


theorem degreeZeroKappaPolynomial810_eq_C_of_ratFuncDeriv
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroKappaPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0)) =
        0) :
    ∃ c : k,
      degreeZeroKappaPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c := by
  let I :=
    degreeZeroKappaPolynomial810 l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa only [I] using hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

theorem degreeZeroNuPolynomial810_eq_C_of_ratFuncDeriv
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroNuPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0)) =
        0) :
    ∃ c : k,
      degreeZeroNuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c := by
  let I :=
    degreeZeroNuPolynomial810 l beta gamma delta epsilon zeta eta theta
      A B C0 D0 E0 F0 G0
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa only [I] using hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

theorem degreeZeroPiPolynomial810_eq_C_of_ratFuncDeriv
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroPiPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0)) =
        0) :
    ∃ c : k,
      degreeZeroPiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c := by
  let I :=
    degreeZeroPiPolynomial810 l beta gamma delta epsilon zeta eta theta
      A B C0 D0 E0 F0 G0
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa only [I] using hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

theorem degreeZeroKappaPolynomial810_natDegree_eq_zero_of_eq_C
    {l beta gamma delta epsilon zeta eta theta : k}
    {A B C0 D0 E0 F0 G0 : k[X]} {c : k}
    (h :
      degreeZeroKappaPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c) :
    (degreeZeroKappaPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree =
      0 := by
  rw [h, natDegree_C]

theorem degreeZeroNuPolynomial810_natDegree_eq_zero_of_eq_C
    {l beta gamma delta epsilon zeta eta theta : k}
    {A B C0 D0 E0 F0 G0 : k[X]} {c : k}
    (h :
      degreeZeroNuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c) :
    (degreeZeroNuPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree =
      0 := by
  rw [h, natDegree_C]

theorem degreeZeroPiPolynomial810_natDegree_eq_zero_of_eq_C
    {l beta gamma delta epsilon zeta eta theta : k}
    {A B C0 D0 E0 F0 G0 : k[X]} {c : k}
    (h :
      degreeZeroPiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c) :
    (degreeZeroPiPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree =
      0 := by
  rw [h, natDegree_C]

end SevenIntegralPolynomials810


/-! ## Source-facing seven-integral packet -/

section SevenIntegralPacket810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 160000000 in
/-- Source-facing packet: the affine-depressed core has integrated `ξ`,
`μ`, `ο`, `κ`, `ν`, and `π` of Newton degree zero, and the grouped
primitive has derivative `C (j / t)`.  Cone negations of the parent
exhaustion residual are dropped. -/
theorem normalized810ScaleZero_sevenIntegralPacket
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroKappaPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroNuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroPiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, A, B, C0p, D0, E0, F0, G0, ht, hj, hjdiv, hHsq, hrowSrc, _hX,
      hcore⟩ :=
    normalized810ScaleZero_exists_primitivePolynomial hsource
  obtain ⟨hA, hB, hC, hD0, hE, hF, hG, hl, hder, hdeg⟩ := hcore
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hDjac : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    obtain ⟨j0, _hj0, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
    have hrow0 :
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j0 :=
      degreeZeroCoefficientJacobianRow_810 hp hq hjac
    have hj0 : j0 = j :=
      Polynomial.C_injective (hrow0.symm.trans (by simpa [p, q] using hrowSrc))
    simpa [hj0, bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  let hRF : RatFunc k := RatFunc.C t
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 q)
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hh : hRF ≠ 0 := by
    intro hzero
    apply ht
    apply RatFunc.C_injective
    simpa only [hRF, map_zero] using hzero
  have hp8' : p.coeff 8 = H ^ 4 := by simpa [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa [q] using hq10
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 8) = hRF ^ 8 := by
    have hpow : (C t ^ 2) ^ 4 = (C t : k[X]) ^ 8 := by
      rw [← pow_mul]
    simp only [hp8', hHsq, hpow, hRF, map_pow, RatFunc.algebraMap_C]
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    have hpow : (C t ^ 2) ^ 5 = (C t : k[X]) ^ 10 := by
      rw [← pow_mul]
    simp only [hq10', hHsq, hpow, hRF, map_pow, RatFunc.algebraMap_C]
  have hpDep := affineDepress_sourceOctic68 p hRF
    (octicDepressionR810 hRF a7) hp hh hpTop
  have hL0 : depressedL68 hRF (octicDepressionR810 hRF a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter hRF a7 hh
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]; rw [hpDep, coeff_depressedOctic68_seven, hL0]
  have hf8 : f.coeff 8 = 1 := by
    dsimp only [f]; rw [hpDep, coeff_depressedOctic68_eight]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n →
      (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, _hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (octicDepressionR810 hRF a7) hh hgTop hg_high_src
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (octicDepressionR810 hRF a7) hh hDjac
  have hdiv : RatFunc.C j / hRF = RatFunc.C (j / t) := by
    simp only [hRF, map_div₀]
  have hjacC : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C (j / t)) := by
    have hbr : differentialJacobian ratFuncDerivation68 f g =
        Polynomial.C (RatFunc.C j / hRF) := by
      simpa only [f, g] using hbracket
    simpa [hdiv] using hbr
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian ratFuncDerivation68 f g).coeff n = 0 := by
    rw [hjacC]
    simp [Polynomial.coeff_C, hn]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [show g.coeff 9 = RatFunc.C l from hl]
    exact ratFuncDerivation68_C l
  have h8 := (differentialJacobian_coeff_8_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 8 (by norm_num))
  have h7 := (differentialJacobian_coeff_7_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 7 (by norm_num))
  have h6 := (differentialJacobian_coeff_6_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 6 (by norm_num))
  have h5 := (differentialJacobian_coeff_5_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 5 (by norm_num))
  have h4 := (differentialJacobian_coeff_4_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 4 (by norm_num))
  have h3 := (differentialJacobian_coeff_3_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 3 (by norm_num))
  have h2 := (differentialJacobian_coeff_2_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 2 (by norm_num))
  obtain ⟨l', beta', gamma', delta', epsilon', zeta', eta', theta', hl',
      hbeta', hgamma', hdelta', hepsilon', hzeta', heta', htheta'⟩ :=
    monicOcticDecic_rhoLoads_exist_ground810 f g (j / t) hf_high hf8 hf7
      hg_high hg10 hLconst hjacC
  let d := ratFuncDerivation68 (k := k)
  have h15 := (differentialJacobian_coeff_15_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 15 (by norm_num))
  have h14 := (differentialJacobian_coeff_14_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 14 (by norm_num))
  have h13 := (differentialJacobian_coeff_13_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 9 (by norm_num))
  have halpha := alphaResidual810_deriv_zero d (f.coeff 6) (g.coeff 8)
    (by linear_combination h15)
  have hbeta0 := betaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (g.coeff 7) hLconst (by linear_combination h14)
  have hgamma0 := gammaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (g.coeff 8) (g.coeff 6) hLconst halpha
    (by linear_combination h13)
  have hdelta0 := deltaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
    (g.coeff 5) hLconst halpha hbeta0 (by linear_combination h12)
  have hepsilon0 := epsilonResidual810_deriv_zero d (g.coeff 9)
    (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha hbeta0
    hgamma0 (by linear_combination h11)
  have hzeta0 := zetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) hLconst
    halpha hbeta0 hgamma0 hdelta0 (by linear_combination h10)
  have heta0 := etaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 2) hLconst halpha hbeta0 hgamma0 hdelta0
    hepsilon0 (by linear_combination h9)
  have htheta0 := thetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 1) hLconst halpha hbeta0 hgamma0
    hdelta0 hepsilon0 hzeta0 (by linear_combination h8)
  have hiota0 := iotaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 0) hLconst halpha hbeta0
    hgamma0 hdelta0 hepsilon0 hzeta0 heta0 (by linear_combination h7)
  have hxi0 := xiResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h6) (by linear_combination h5)
    (by linear_combination h3)
  have hmu0 := muResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h5)
  have hom0 := omicronResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h6) (by linear_combination h5)
    (by linear_combination h4) (by linear_combination h2)
  have hkappa0 := kappaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) hLconst halpha hbeta0
    hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0
    (by linear_combination h8) (by linear_combination h6)
  have hnu0 := nuResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h6) (by linear_combination h4)
  have hpi0 :
      d (piResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1)) =
        0 :=
    piResidual810_deriv_zero_of_monic_differentialJacobian d f g
      (RatFunc.C (j / t)) hf_high hf8 hf7 hg_high hg10 hLconst hjacC
  have hxi_res :
      xiResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroXiIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact xiResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hmu_res :
      muResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroMuIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact muResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hom_res :
      omicronResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroOmicronIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact omicronResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hkappa_res :
      kappaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroKappaIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact kappaResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hnu_res :
      nuResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroNuIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact nuResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hpi_res :
      piResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroPiIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact piResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hxi_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroXiPolynomial810 l' beta' gamma' delta' epsilon' zeta'
            eta' theta' A B C0p D0 E0 F0 G0) =
        xiResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hxi_res]
    exact algebraMap_degreeZeroXiPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hmu_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroMuPolynomial810 l' beta' gamma' delta' epsilon' zeta'
            eta' theta' A B C0p D0 E0 F0 G0) =
        muResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hmu_res]
    exact algebraMap_degreeZeroMuPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hom_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroOmicronPolynomial810 l' beta' gamma' delta' epsilon'
            zeta' eta' theta' A B C0p D0 E0 F0 G0) =
        omicronResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hom_res]
    exact algebraMap_degreeZeroOmicronPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hkappa_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroKappaPolynomial810 l' beta' gamma' delta' epsilon'
            zeta' eta' theta' A B C0p D0 E0 F0 G0) =
        kappaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hkappa_res]
    exact algebraMap_degreeZeroKappaPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hnu_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroNuPolynomial810 l' beta' gamma' delta' epsilon' zeta'
            eta' theta' A B C0p D0 E0 F0 G0) =
        nuResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hnu_res]
    exact algebraMap_degreeZeroNuPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hpi_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroPiPolynomial810 l' beta' gamma' delta' epsilon' zeta'
            eta' theta' A B C0p D0 E0 F0 G0) =
        piResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hpi_res]
    exact algebraMap_degreeZeroPiPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hxi_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroXiPolynomial810 l' beta' gamma' delta' epsilon'
              zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hxi_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hxi0
  have hmu_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroMuPolynomial810 l' beta' gamma' delta' epsilon'
              zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hmu_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hmu0
  have hom_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroOmicronPolynomial810 l' beta' gamma' delta'
              epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hom_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hom0
  have hkappa_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroKappaPolynomial810 l' beta' gamma' delta' epsilon'
              zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hkappa_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hkappa0
  have hnu_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroNuPolynomial810 l' beta' gamma' delta' epsilon'
              zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hnu_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hnu0
  have hpi_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroPiPolynomial810 l' beta' gamma' delta' epsilon'
              zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hpi_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hpi0
  obtain ⟨cXi, hcXi⟩ :=
    degreeZeroXiPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hxi_deriv
  obtain ⟨cMu, hcMu⟩ :=
    degreeZeroMuPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hmu_deriv
  obtain ⟨cOm, hcOm⟩ :=
    degreeZeroOmicronPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma'
      delta' epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hom_deriv
  obtain ⟨cKap, hcKap⟩ :=
    degreeZeroKappaPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma'
      delta' epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hkappa_deriv
  obtain ⟨cNu, hcNu⟩ :=
    degreeZeroNuPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hnu_deriv
  obtain ⟨cPi, hcPi⟩ :=
    degreeZeroPiPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hpi_deriv
  have hrho :
      rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroIntegratedPrimitive810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact rhoResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  let prim : k[X] :=
    degreeZeroPrimitivePolynomial810 l' beta' gamma' delta' epsilon' zeta'
      eta' theta' A B C0p D0 E0 F0 G0
  have hmap_prim :
      algebraMap k[X] (RatFunc k) prim =
        rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hrho]
    exact algebraMap_degreeZeroPrimitivePolynomial810 l' beta' gamma'
      delta' epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hder_prim :
      algebraMap k[X] (RatFunc k) (derivative prim) =
        algebraMap k[X] (RatFunc k) (C (j / t)) := by
    rw [← ratFuncDerivation46_polynomial]
    have hderiv' :
        ratFuncDerivation68 (algebraMap k[X] (RatFunc k) prim) =
          RatFunc.C (j / t) := by
      rw [hmap_prim]
      have hd_rho :
          d (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
              (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
              (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
              (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
              (g.coeff 1)) =
            g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) :=
        rhoResidual810_deriv_eq_row d (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst halpha
          hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
          hkappa0 hmu0 hnu0 hxi0 hom0
      have hrow0 :
          g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) =
            RatFunc.C (j / t) :=
        degreeZeroRow_eq_constant_of_monic_differentialJacobian d f g
          (RatFunc.C (j / t)) hf_high hf8 hf7 hg_high hg10 hLconst hjacC
      have := hd_rho.trans hrow0
      simpa [d] using this
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply,
      RatFunc.algebraMap_C] using hderiv'
  have hpolyder : derivative prim = C (j / t) :=
    (RatFunc.algebraMap_injective k) hder_prim
  exact ⟨t, j, lambda, cleared, l', beta', gamma', delta', epsilon', zeta',
    eta', theta', cXi, cMu, cOm, A, B, C0p, D0, E0, F0, G0, ht, hj, hjdiv,
    hHsq, hpolyder,
    degreeZeroXiPolynomial810_natDegree_eq_zero_of_eq_C hcXi,
    degreeZeroMuPolynomial810_natDegree_eq_zero_of_eq_C hcMu,
    degreeZeroOmicronPolynomial810_natDegree_eq_zero_of_eq_C hcOm,
    degreeZeroKappaPolynomial810_natDegree_eq_zero_of_eq_C hcKap,
    degreeZeroNuPolynomial810_natDegree_eq_zero_of_eq_C hcNu,
    degreeZeroPiPolynomial810_natDegree_eq_zero_of_eq_C hcPi⟩

#print axioms normalized810ScaleZero_sevenIntegralPacket

end SevenIntegralPacket810

end Max11DegreeRoutes
