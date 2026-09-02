import Grok610ScaleZeroConeTerminalScratch

/-! # Scale-zero cone kappa/mu/omicron closure for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroConeTerminalScratch` on the constant core
`H = (C t)²`.  That file showed that `λ` is a ground constant on the
affine-depressed core and closed every unique weighted face of `λ`,
reducing `normalized610ScaleZero_impossible` to
`normalized610ScaleZero_coneTerminalResidual`.  The remaining cones are:

* unique-`B` tie `3 deg A = 2 deg B` with the load-free `λ` combination
  `7 A⁶ - 126 A³ B² + 27 B⁴` dropped below top degree;
* ratio-ties of two or more of `{6 deg A, 4 deg B, 3 deg C₀, 2 deg E₀}`
  with dropped load-free combination;
* unique-high `D₀` with another letter nonconstant (`A D₀²` competing
  with `A⁶`);
* unique-high `C₀`/`E₀` that do not strictly lead the four weighted faces.

CAS job `derive_610_scale_zero_cone_kappa_mu.py` (outer degrees `(6,10)`,
leading `H³`, `H⁵` with `H` a nonzero constant) substitutes the triangular
Faber constants into `kappaResidual610`, `muResidual610`, and the
weight-seventy residual `fourteenthResidual610` (`ο`).  After that
substitution, on the unique-`B` tie the companion `κ` face
`A B (7 A³ - 12 B²)` cannot drop together with the `λ` combination
(plug `7 u = 12 v` into the `λ` leading form:
`49 · (7 u² - 126 u v + 27 v²) = -8253 v² ≠ 0`).

The first integrals `κ, μ` and the residual `ο` are ground constants on
the depressed core (their derivatives vanish by the corresponding
Jacobian rows, via the monic sextic/decic differential Jacobian).  The
unique-`B` drop is empty, and every unique maximum among
`{6 deg A, 4 deg B, 3 deg C₀, 2 deg E₀}` with load-free `D₀` monomials
strictly lighter is empty (including unique-high `C₀`/`E₀` that do not
strictly lead in the parent sense whenever another weighted face uniquely
leads).  The leaf is not closed.  Remaining cones are the ratio-ties of
two or more of those four weights with dropped load-free combination, and
unique-high `D₀` with another letter nonconstant.  The unused integrals
`μ` and `ο` are the next comparison on those chambers.  No total-degree
or twice-prime theorem is used.  No `sorry`, no new axioms, no finite-root
shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Field-level first integrals and polynomial pullbacks -/
section KappaMuOmicronPolynomials610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
/-- Field-level integrated `κ` (same coefficients as
`degreeZeroKappaPolynomial610`).  CAS: 40 terms. -/
def degreeZeroKappaIntegrated610
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta delta epsilon zeta eta theta : F) : F :=
  - (35 / 729 : F) * (A ^ 4 * B)
  - (3 / 256 * L : F) * A ^ 5
  + (20 / 243 : F) * (A * B ^ 3)
  + (20 / 81 : F) * (A ^ 2 * B * C0)
  + (9 / 64 * L : F) * (A ^ 2 * B ^ 2)
  + (20 / 243 : F) * (A ^ 3 * D0)
  + (3 / 32 * L : F) * (A ^ 3 * C0)
  + (20 / 243 * alpha : F) * (A ^ 3 * B)
  + (385 / 31104 * beta : F) * A ^ 4
  - (5 / 27 : F) * (B * C0 ^ 2)
  - (5 / 27 : F) * (B ^ 2 * D0)
  - (3 / 16 * L : F) * (B ^ 2 * C0)
  - (4 / 81 * alpha : F) * B ^ 3
  - (10 / 27 : F) * (A * C0 * D0)
  - (3 / 16 * L : F) * (A * C0 ^ 2)
  - (10 / 27 : F) * (A * B * E0)
  - (3 / 8 * L : F) * (A * B * D0)
  - (8 / 27 * alpha : F) * (A * B * C0)
  - (35 / 432 * beta : F) * (A * B ^ 2)
  - (3 / 16 * L : F) * (A ^ 2 * E0)
  - (4 / 27 * alpha : F) * (A ^ 2 * D0)
  - (35 / 432 * beta : F) * (A ^ 2 * C0)
  + (35 / 1296 * delta : F) * A ^ 3
  + (10 / 9 : F) * (D0 * E0)
  + (3 / 8 * L : F) * D0 ^ 2
  + (3 / 4 * L : F) * (C0 * E0)
  + (4 / 9 * alpha : F) * (C0 * D0)
  + (7 / 72 * beta : F) * C0 ^ 2
  + (4 / 9 * alpha : F) * (B * E0)
  + (7 / 36 * beta : F) * (B * D0)
  - (5 / 72 * delta : F) * B ^ 2
  + (7 / 36 * beta : F) * (A * E0)
  - (5 / 36 * delta : F) * (A * C0)
  - (2 / 9 * epsilon : F) * (A * B)
  - (1 / 8 * zeta : F) * A ^ 2
  + (5 / 6 * delta : F) * E0
  + (2 / 3 * epsilon : F) * D0
  + (1 / 2 * zeta : F) * C0
  + (1 / 3 * eta : F) * B
  + (1 / 6 * theta : F) * A

set_option maxHeartbeats 16000000 in
/-- Polynomial pullback of `muResidual610` after the triangular Faber
coordinates are ground constants.  CAS: 61 terms. -/
def degreeZeroMuPolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (5 / 1024 * l : k) • A ^ 6
  + (35 / 1458 : k) • (A ^ 5 * B)
  - (77 / 15552 * beta : k) • A ^ 5
  - (10 / 243 * alpha : k) • (A ^ 4 * B)
  - (11 / 256 * l : k) • (A ^ 4 * C0)
  - (25 / 729 : k) • (A ^ 4 * D0)
  - (35 / 3456 * delta : k) • A ^ 4
  - (3 / 32 * l : k) • (A ^ 3 * B ^ 2)
  - (110 / 729 : k) • (A ^ 3 * B * C0)
  + (35 / 972 * beta : k) • (A ^ 3 * C0)
  + (14 / 243 * alpha : k) • (A ^ 3 * D0)
  + (1 / 16 * l : k) • (A ^ 3 * E0)
  + (1 / 24 * zeta : k) • A ^ 3
  - (20 / 243 : k) • (A ^ 2 * B ^ 3)
  + (35 / 576 * beta : k) • (A ^ 2 * B ^ 2)
  + (16 / 81 * alpha : k) • (A ^ 2 * B * C0)
  + (7 / 32 * l : k) • (A ^ 2 * B * D0)
  + (5 / 27 : k) • (A ^ 2 * B * E0)
  + (1 / 9 * epsilon : k) • (A ^ 2 * B)
  + (7 / 64 * l : k) • (A ^ 2 * C0 ^ 2)
  + (5 / 27 : k) • (A ^ 2 * C0 * D0)
  + (25 / 432 * delta : k) • (A ^ 2 * C0)
  - (7 / 144 * beta : k) • (A ^ 2 * E0)
  - (1 / 24 * theta : k) • A ^ 2
  + (2 / 27 * alpha : k) • (A * B ^ 3)
  + (1 / 4 * l : k) • (A * B ^ 2 * C0)
  + (35 / 162 : k) • (A * B ^ 2 * D0)
  + (5 / 72 * delta : k) • (A * B ^ 2)
  + (35 / 162 : k) • (A * B * C0 ^ 2)
  - (7 / 54 * beta : k) • (A * B * D0)
  - (2 / 9 * alpha : k) • (A * B * E0)
  - (1 / 6 * eta : k) • (A * B)
  - (7 / 108 * beta : k) • (A * C0 ^ 2)
  - (2 / 9 * alpha : k) • (A * C0 * D0)
  - (1 / 4 * l : k) • (A * C0 * E0)
  - (1 / 6 * zeta : k) • (A * C0)
  - (1 / 8 * l : k) • (A * D0 ^ 2)
  - (5 / 27 : k) • (A * D0 * E0)
  - (1 / 9 * epsilon : k) • (A * D0)
  + (3 / 128 * l : k) • B ^ 4
  + (20 / 243 : k) • (B ^ 3 * C0)
  - (35 / 432 * beta : k) • (B ^ 2 * C0)
  - (4 / 27 * alpha : k) • (B ^ 2 * D0)
  - (3 / 16 * l : k) • (B ^ 2 * E0)
  - (1 / 8 * zeta : k) • B ^ 2
  - (4 / 27 * alpha : k) • (B * C0 ^ 2)
  - (3 / 8 * l : k) • (B * C0 * D0)
  - (10 / 27 : k) • (B * C0 * E0)
  - (2 / 9 * epsilon : k) • (B * C0)
  - (5 / 27 : k) • (B * D0 ^ 2)
  - (5 / 36 * delta : k) • (B * D0)
  - (1 / 16 * l : k) • C0 ^ 3
  - (5 / 27 : k) • (C0 ^ 2 * D0)
  - (5 / 72 * delta : k) • C0 ^ 2
  + (7 / 36 * beta : k) • (C0 * E0)
  + (1 / 6 * theta : k) • C0
  + (7 / 72 * beta : k) • D0 ^ 2
  + (4 / 9 * alpha : k) • (D0 * E0)
  + (1 / 3 * eta : k) • D0
  + (3 / 8 * l : k) • E0 ^ 2
  + (1 / 2 * zeta : k) • E0

set_option maxHeartbeats 16000000 in
/-- Field-level integrated `μ` (same coefficients as
`degreeZeroMuPolynomial610`).  CAS: 61 terms. -/
def degreeZeroMuIntegrated610
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta delta epsilon zeta eta theta : F) : F :=
  (5 / 1024 * L : F) * A ^ 6
  + (35 / 1458 : F) * (A ^ 5 * B)
  - (77 / 15552 * beta : F) * A ^ 5
  - (10 / 243 * alpha : F) * (A ^ 4 * B)
  - (11 / 256 * L : F) * (A ^ 4 * C0)
  - (25 / 729 : F) * (A ^ 4 * D0)
  - (35 / 3456 * delta : F) * A ^ 4
  - (3 / 32 * L : F) * (A ^ 3 * B ^ 2)
  - (110 / 729 : F) * (A ^ 3 * B * C0)
  + (35 / 972 * beta : F) * (A ^ 3 * C0)
  + (14 / 243 * alpha : F) * (A ^ 3 * D0)
  + (1 / 16 * L : F) * (A ^ 3 * E0)
  + (1 / 24 * zeta : F) * A ^ 3
  - (20 / 243 : F) * (A ^ 2 * B ^ 3)
  + (35 / 576 * beta : F) * (A ^ 2 * B ^ 2)
  + (16 / 81 * alpha : F) * (A ^ 2 * B * C0)
  + (7 / 32 * L : F) * (A ^ 2 * B * D0)
  + (5 / 27 : F) * (A ^ 2 * B * E0)
  + (1 / 9 * epsilon : F) * (A ^ 2 * B)
  + (7 / 64 * L : F) * (A ^ 2 * C0 ^ 2)
  + (5 / 27 : F) * (A ^ 2 * C0 * D0)
  + (25 / 432 * delta : F) * (A ^ 2 * C0)
  - (7 / 144 * beta : F) * (A ^ 2 * E0)
  - (1 / 24 * theta : F) * A ^ 2
  + (2 / 27 * alpha : F) * (A * B ^ 3)
  + (1 / 4 * L : F) * (A * B ^ 2 * C0)
  + (35 / 162 : F) * (A * B ^ 2 * D0)
  + (5 / 72 * delta : F) * (A * B ^ 2)
  + (35 / 162 : F) * (A * B * C0 ^ 2)
  - (7 / 54 * beta : F) * (A * B * D0)
  - (2 / 9 * alpha : F) * (A * B * E0)
  - (1 / 6 * eta : F) * (A * B)
  - (7 / 108 * beta : F) * (A * C0 ^ 2)
  - (2 / 9 * alpha : F) * (A * C0 * D0)
  - (1 / 4 * L : F) * (A * C0 * E0)
  - (1 / 6 * zeta : F) * (A * C0)
  - (1 / 8 * L : F) * (A * D0 ^ 2)
  - (5 / 27 : F) * (A * D0 * E0)
  - (1 / 9 * epsilon : F) * (A * D0)
  + (3 / 128 * L : F) * B ^ 4
  + (20 / 243 : F) * (B ^ 3 * C0)
  - (35 / 432 * beta : F) * (B ^ 2 * C0)
  - (4 / 27 * alpha : F) * (B ^ 2 * D0)
  - (3 / 16 * L : F) * (B ^ 2 * E0)
  - (1 / 8 * zeta : F) * B ^ 2
  - (4 / 27 * alpha : F) * (B * C0 ^ 2)
  - (3 / 8 * L : F) * (B * C0 * D0)
  - (10 / 27 : F) * (B * C0 * E0)
  - (2 / 9 * epsilon : F) * (B * C0)
  - (5 / 27 : F) * (B * D0 ^ 2)
  - (5 / 36 * delta : F) * (B * D0)
  - (1 / 16 * L : F) * C0 ^ 3
  - (5 / 27 : F) * (C0 ^ 2 * D0)
  - (5 / 72 * delta : F) * C0 ^ 2
  + (7 / 36 * beta : F) * (C0 * E0)
  + (1 / 6 * theta : F) * C0
  + (7 / 72 * beta : F) * D0 ^ 2
  + (4 / 9 * alpha : F) * (D0 * E0)
  + (1 / 3 * eta : F) * D0
  + (3 / 8 * L : F) * E0 ^ 2
  + (1 / 2 * zeta : F) * E0

set_option maxHeartbeats 16000000 in
/-- Polynomial pullback of `rawFourthTailCoefficient610` after the triangular
Faber coordinates are ground constants. -/
def degreeZeroRawFourthTailPolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(65 / 19683 : k)) • A ^ 7 +
    (70 / 2187 : k) • (A ^ 5 * C0) +
    (175 / 2187 : k) • (A ^ 4 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * E0) -
    (140 / 729 : k) • (A ^ 3 * B * D0) -
    (70 / 729 : k) • (A ^ 3 * C0 ^ 2) -
    (70 / 243 : k) • (A ^ 2 * B ^ 2 * C0) +
    (20 / 81 : k) • (A ^ 2 * C0 * E0) +
    (10 / 81 : k) • (A ^ 2 * D0 ^ 2) -
    (35 / 729 : k) • (A * B ^ 4) +
    (20 / 81 : k) • (A * B ^ 2 * E0) +
    (40 / 81 : k) • (A * B * C0 * D0) +
    (20 / 243 : k) • (A * C0 ^ 3) -
    (5 / 27 : k) • (A * E0 ^ 2) +
    (20 / 243 : k) • (B ^ 3 * D0) +
    (10 / 81 : k) • (B ^ 2 * C0 ^ 2) -
    (10 / 27 : k) • (B * D0 * E0) -
    (5 / 27 : k) • (C0 ^ 2 * E0) -
    (5 / 27 : k) • (C0 * D0 ^ 2) +
    (21 / 512 * l : k) • (A ^ 5 * B) -
    (15 / 256 * l : k) • (A ^ 4 * D0) -
    (15 / 64 * l : k) • (A ^ 3 * B * C0) -
    (15 / 128 * l : k) • (A ^ 2 * B ^ 3) +
    (9 / 32 * l : k) • (A ^ 2 * B * E0) +
    (9 / 32 * l : k) • (A ^ 2 * C0 * D0) +
    (9 / 32 * l : k) • (A * B ^ 2 * D0) +
    (9 / 32 * l : k) • (A * B * C0 ^ 2) -
    (3 / 8 * l : k) • (A * D0 * E0) +
    (3 / 32 * l : k) • (B ^ 3 * C0) -
    (3 / 8 * l : k) • (B * C0 * E0) -
    (3 / 16 * l : k) • (B * D0 ^ 2) -
    (3 / 16 * l : k) • (C0 ^ 2 * D0) +
    (44 / 6561 * alpha : k) • A ^ 6 -
    (40 / 729 * alpha : k) • (A ^ 4 * C0) -
    (80 / 729 * alpha : k) • (A ^ 3 * B ^ 2) +
    (20 / 243 * alpha : k) • (A ^ 3 * E0) +
    (20 / 81 * alpha : k) • (A ^ 2 * B * D0) +
    (10 / 81 * alpha : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 * alpha : k) • (A * B ^ 2 * C0) -
    (8 / 27 * alpha : k) • (A * C0 * E0) -
    (4 / 27 * alpha : k) • (A * D0 ^ 2) +
    (5 / 243 * alpha : k) • B ^ 4 -
    (4 / 27 * alpha : k) • (B ^ 2 * E0) -
    (8 / 27 * alpha : k) • (B * C0 * D0) -
    (4 / 81 * alpha : k) • C0 ^ 3 +
    (2 / 9 * alpha : k) • E0 ^ 2 -
    (6545 / 186624 * beta : k) • (A ^ 4 * B) +
    (385 / 7776 * beta : k) • (A ^ 3 * D0) +
    (385 / 2592 * beta : k) • (A ^ 2 * B * C0) +
    (385 / 7776 * beta : k) • (A * B ^ 3) -
    (35 / 216 * beta : k) • (A * B * E0) -
    (35 / 216 * beta : k) • (A * C0 * D0) -
    (35 / 432 * beta : k) • (B ^ 2 * D0) -
    (35 / 432 * beta : k) • (B * C0 ^ 2) +
    (7 / 36 * beta : k) • (D0 * E0) -
    (455 / 7776 * delta : k) • (A ^ 3 * B) +
    (35 / 432 * delta : k) • (A ^ 2 * D0) +
    (35 / 216 * delta : k) • (A * B * C0) +
    (35 / 1296 * delta : k) • B ^ 3 -
    (5 / 36 * delta : k) • (B * E0) -
    (5 / 36 * delta : k) • (C0 * D0) -
    (7 / 243 * epsilon : k) • A ^ 4 +
    (4 / 27 * epsilon : k) • (A ^ 2 * C0) +
    (4 / 27 * epsilon : k) • (A * B ^ 2) -
    (2 / 9 * epsilon : k) • (A * E0) -
    (2 / 9 * epsilon : k) • (B * D0) -
    (1 / 9 * epsilon : k) • C0 ^ 2 +
    (5 / 81 * eta : k) • A ^ 3 -
    (2 / 9 * eta : k) • (A * C0) -
    (1 / 9 * eta : k) • B ^ 2 +
    (1 / 3 * eta : k) • E0 -
    (5 / 36 * theta : k) • (A * B) +
    (1 / 6 * theta : k) • D0 +
    (3 / 16 * zeta : k) • (A ^ 2 * B) -
    (1 / 4 * zeta : k) • (A * D0) -
    (1 / 4 * zeta : k) • (B * C0)

/-- Polynomial pullback of `fourteenthResidual610` (`ο`) after the
triangular Faber coordinates are ground constants.
`ο =` raw fourth tail `+ (B/6) κ + (A/3) λ`. -/
def degreeZeroOmicronPolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroRawFourthTailPolynomial610 l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 +
    (1 / 6 : k) • (B * degreeZeroKappaPolynomial610 l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0) +
    (1 / 3 : k) • (A * degreeZeroLambdaPolynomial610 l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0)

/-- Field-level integrated `ο`. -/
def degreeZeroOmicronIntegrated610
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta delta epsilon zeta eta theta : F) : F :=
  rawFourthTailCoefficient610 L A B C0 D0 E0 alpha beta delta epsilon
      zeta eta theta +
    (1 / 6 : F) * B *
      degreeZeroKappaIntegrated610 L A B C0 D0 E0 alpha beta delta
        epsilon zeta eta theta +
    (1 / 3 : F) * A *
      degreeZeroLambdaIntegrated610 L A B C0 D0 E0 alpha beta delta
        epsilon zeta eta theta

end KappaMuOmicronPolynomials610

/-! ## First-integral identities -/

section FirstIntegralIdentities610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem kappaResidual610_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta gamma delta epsilon zeta eta theta iota :
      F) :
    kappaResidual610 L A B C0 D0 E0
        (integratedP610 A alpha)
        (integratedQ610 L A B beta)
        (integratedR610 L A B C0 alpha gamma)
        (integratedS610 L A B C0 D0 alpha beta delta)
        (integratedT610 L A B C0 D0 E0 alpha beta gamma epsilon)
        (integratedU610 L A B C0 D0 E0 alpha beta gamma delta zeta)
        (integratedV610 L A B C0 D0 E0 alpha beta gamma delta epsilon
          eta)
        (integratedW610 L A B C0 D0 E0 alpha beta gamma delta epsilon
          zeta theta) =
      degreeZeroKappaIntegrated610 L A B C0 D0 E0 alpha beta delta
        epsilon zeta eta theta := by
  obtain ⟨halpha, hbeta, _hgamma, hdelta, hepsilon, hzeta, heta, htheta,
      _hiota⟩ :=
    integratedResiduals610 L A B C0 D0 E0 alpha beta gamma delta epsilon
      zeta eta theta iota
  simp only [kappaResidual610, degreeZeroKappaIntegrated610]
  rw [halpha, hbeta, hdelta, hepsilon, hzeta, heta, htheta]
  ring

set_option maxHeartbeats 32000000 in
theorem algebraMap_degreeZeroKappaPolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0) =
      degreeZeroKappaIntegrated610 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroKappaPolynomial610, degreeZeroKappaIntegrated610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  try ring

set_option maxHeartbeats 64000000 in
theorem muResidual610_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta gamma delta epsilon zeta eta theta iota :
      F) :
    muResidual610 L A B C0 D0 E0
        (integratedP610 A alpha)
        (integratedQ610 L A B beta)
        (integratedR610 L A B C0 alpha gamma)
        (integratedS610 L A B C0 D0 alpha beta delta)
        (integratedT610 L A B C0 D0 E0 alpha beta gamma epsilon)
        (integratedU610 L A B C0 D0 E0 alpha beta gamma delta zeta)
        (integratedV610 L A B C0 D0 E0 alpha beta gamma delta epsilon
          eta)
        (integratedW610 L A B C0 D0 E0 alpha beta gamma delta epsilon
          zeta theta) =
      degreeZeroMuIntegrated610 L A B C0 D0 E0 alpha beta delta
        epsilon zeta eta theta := by
  obtain ⟨halpha, hbeta, _hgamma, hdelta, hepsilon, hzeta, heta, htheta,
      _hiota⟩ :=
    integratedResiduals610 L A B C0 D0 E0 alpha beta gamma delta epsilon
      zeta eta theta iota
  simp only [muResidual610, degreeZeroMuIntegrated610]
  rw [halpha, hbeta, hdelta, hepsilon, hzeta, heta, htheta]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_degreeZeroMuPolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0) =
      degreeZeroMuIntegrated610 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroMuPolynomial610, degreeZeroMuIntegrated610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  try ring

set_option maxHeartbeats 32000000 in
theorem fourteenthResidual610_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta gamma delta epsilon zeta eta theta iota :
      F) :
    fourteenthResidual610 L A B C0 D0 E0
        (integratedP610 A alpha)
        (integratedQ610 L A B beta)
        (integratedR610 L A B C0 alpha gamma)
        (integratedS610 L A B C0 D0 alpha beta delta)
        (integratedT610 L A B C0 D0 E0 alpha beta gamma epsilon)
        (integratedU610 L A B C0 D0 E0 alpha beta gamma delta zeta)
        (integratedV610 L A B C0 D0 E0 alpha beta gamma delta epsilon
          eta)
        (integratedW610 L A B C0 D0 E0 alpha beta gamma delta epsilon
          zeta theta) =
      degreeZeroOmicronIntegrated610 L A B C0 D0 E0 alpha beta delta
        epsilon zeta eta theta := by
  obtain ⟨halpha, hbeta, _hgamma, hdelta, hepsilon, hzeta, heta, htheta,
      _hiota⟩ :=
    integratedResiduals610 L A B C0 D0 E0 alpha beta gamma delta epsilon
      zeta eta theta iota
  have hkappa :=
    kappaResidual610_eq_integrated L A B C0 D0 E0 alpha beta gamma delta
      epsilon zeta eta theta iota
  have hlambda :=
    lambdaResidual610_eq_integrated L A B C0 D0 E0 alpha beta gamma delta
      epsilon zeta eta theta iota
  simp only [fourteenthResidual610, degreeZeroOmicronIntegrated610,
    rawFourthTailCoefficient610]
  rw [halpha, hbeta, hdelta, hepsilon, hzeta, heta, htheta, hkappa,
    hlambda]
  try ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_degreeZeroRawFourthTailPolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroRawFourthTailPolynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0) =
      rawFourthTailCoefficient610 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroRawFourthTailPolynomial610,
    rawFourthTailCoefficient610, rawFourthTailPure610,
    rawFourthTailLBlock610, rawFourthTailAlphaBlock610,
    rawFourthTailBetaBlock610, rawFourthTailDeltaBlock610,
    rawFourthTailEpsilonBlock610, rawFourthTailEtaBlock610,
    rawFourthTailThetaBlock610, rawFourthTailZetaBlock610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  try ring

set_option maxHeartbeats 16000000 in
theorem algebraMap_degreeZeroOmicronPolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0) =
      degreeZeroOmicronIntegrated610 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroOmicronPolynomial610,
    degreeZeroOmicronIntegrated610, map_add, map_mul, map_pow,
    Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀, map_ofNat]
  rw [algebraMap_degreeZeroRawFourthTailPolynomial610,
    algebraMap_degreeZeroKappaPolynomial610,
    algebraMap_degreeZeroLambdaPolynomial610]
  simp [one_mul, mul_assoc, mul_left_comm, mul_comm]
  try ring_nf

/-- A polynomial whose RatFunc image has vanishing derivative is a
ground constant. -/
theorem polynomial_eq_C_of_ratFuncDeriv (I : k[X])
    (hderiv :
      ratFuncDerivation46 (algebraMap k[X] (RatFunc k) I) = 0) :
    ∃ c : k, I = Polynomial.C c := by
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    exact hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

theorem polynomial_natDegree_eq_zero_of_eq_C {I : k[X]} {c : k}
    (h : I = Polynomial.C c) : I.natDegree = 0 := by
  rw [h, natDegree_C]

end FirstIntegralIdentities610

/-! ## Monic Jacobian bridges -/

section MonicBridges610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- A constant depressed differential Jacobian makes `κ` a differential
constant. -/
theorem kappaResidual610_deriv_zero_of_monic_differentialJacobian
    (d : Derivation k F F) (f g : F[X]) (c : F)
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0)
    (hjac : differentialJacobian d f g = Polynomial.C c) :
    d (kappaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
      (g.coeff 1)) = 0 := by
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian d f g).coeff n = 0 := by
    rw [hjac]
    simp [Polynomial.coeff_C, hn]
  have h13 := (differentialJacobian_coeff_13_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 9 (by norm_num))
  have h8 := (differentialJacobian_coeff_8_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 8 (by norm_num))
  have h7 := (differentialJacobian_coeff_7_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 7 (by norm_num))
  have h6 := (differentialJacobian_coeff_6_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 6 (by norm_num))
  have h4 := (differentialJacobian_coeff_4_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 4 (by norm_num))
  have halpha := alphaResidual610_deriv_zero d (f.coeff 4) (g.coeff 8)
    (by linear_combination h13)
  have hbeta := betaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (g.coeff 7) hL (by linear_combination h12)
  have hgamma := gammaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 6) hL halpha
    (by linear_combination h11)
  have hdelta := deltaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
    (g.coeff 5) hL halpha hbeta (by linear_combination h10)
  have hepsilon := epsilonResidual610_deriv_zero d (g.coeff 9)
    (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hL halpha hbeta
    hgamma (by linear_combination h9)
  have hzeta := zetaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) hL halpha hbeta
    hgamma hdelta (by linear_combination h8)
  have heta := etaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2) hL
    halpha hbeta hgamma hdelta hepsilon (by linear_combination h7)
  have htheta := thetaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
    (g.coeff 1) hL halpha hbeta hgamma hdelta hepsilon hzeta
    (by linear_combination h6)
  exact kappaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
    (g.coeff 2) (g.coeff 1) hL halpha hbeta hgamma hdelta hepsilon
    hzeta heta htheta (by linear_combination h6)
    (by linear_combination h4)

/-- A constant depressed differential Jacobian makes `μ` a differential
constant. -/
theorem muResidual610_deriv_zero_of_monic_differentialJacobian
    (d : Derivation k F F) (f g : F[X]) (c : F)
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0)
    (hjac : differentialJacobian d f g = Polynomial.C c) :
    d (muResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
      (g.coeff 1)) = 0 := by
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian d f g).coeff n = 0 := by
    rw [hjac]
    simp [Polynomial.coeff_C, hn]
  have h13 := (differentialJacobian_coeff_13_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 9 (by norm_num))
  have h8 := (differentialJacobian_coeff_8_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 8 (by norm_num))
  have h7 := (differentialJacobian_coeff_7_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 7 (by norm_num))
  have h6 := (differentialJacobian_coeff_6_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 6 (by norm_num))
  have h5 := (differentialJacobian_coeff_5_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 5 (by norm_num))
  have h4 := (differentialJacobian_coeff_4_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 4 (by norm_num))
  have h2 := (differentialJacobian_coeff_2_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 2 (by norm_num))
  have halpha := alphaResidual610_deriv_zero d (f.coeff 4) (g.coeff 8)
    (by linear_combination h13)
  have hbeta := betaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (g.coeff 7) hL (by linear_combination h12)
  have hgamma := gammaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 6) hL halpha
    (by linear_combination h11)
  have hdelta := deltaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
    (g.coeff 5) hL halpha hbeta (by linear_combination h10)
  have hepsilon := epsilonResidual610_deriv_zero d (g.coeff 9)
    (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hL halpha hbeta
    hgamma (by linear_combination h9)
  have hzeta := zetaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) hL halpha hbeta
    hgamma hdelta (by linear_combination h8)
  have heta := etaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2) hL
    halpha hbeta hgamma hdelta hepsilon (by linear_combination h7)
  have htheta := thetaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
    (g.coeff 1) hL halpha hbeta hgamma hdelta hepsilon hzeta
    (by linear_combination h6)
  exact muResidual610_deriv_zero d (g.coeff 9) (f.coeff 4) (f.coeff 3)
    (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
    (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
    (g.coeff 1) (g.coeff 0) hL halpha hbeta hgamma hdelta hepsilon
    hzeta heta htheta (by linear_combination h6)
    (by linear_combination h5) (by linear_combination h4)
    (by linear_combination h2)

end MonicBridges610
/-! ## Source-facing constant first integrals -/

section SourceFirstIntegrals610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 80000000 in
/-- Source-facing packet: the affine-depressed core has integrated `κ`,
`λ`, `μ`, and `ο` polynomials equal to ground constants. -/
theorem normalized610ScaleZero_firstIntegrals_eq_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 ∧
      degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cLam ∧
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cKap ∧
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cMu ∧
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cOmi ∧
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      _hrow, _homicron, hcore⟩ :=
    normalized610ScaleZero_exists_primitivePolynomial hsource
  obtain ⟨hA, hB, hC, hD, hE, hl, hP, hQ, hR, hS, hT, hU, hV, hW, hX,
      hder, hdeg⟩ := hcore
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j', _hj', hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDjac : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j') := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨lambdaN, _a, _g0, _d0, _e, _z, _et, _th, _iot, _ka, _mu, _nu,
      _xi, _omicron0, hN, _hM, _hT, _hU, _hV, _hW, _hX, _hY, _hI, _hZ,
      _hJ, _hnu, _hxi, _homicron⟩ :=
    scaleZero_degreeOneClearedDefect_exists_C_610 hp hq hDjac ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  obtain ⟨aRes, haRes⟩ :=
    scaleZero_lambdaResidual_depressed_eq_C_610 hp hq ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10) hN
      hDjac
  let hRF : RatFunc k := RatFunc.C t
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    dsimp [hRF]
    rw [hp6, hHsq, map_pow, map_pow, RatFunc.algebraMap_C, ← pow_mul]
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    dsimp [hRF]
    rw [hq10, hHsq, map_pow, map_pow, RatFunc.algebraMap_C, ← pow_mul]
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 q)
  have hf4 : f.coeff 4 =
      depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
    dsimp only [f, depressedA610, a5, a4]
    rw [hpDep, coeff_depressedSextic68_four]
  have hf3 : f.coeff 3 =
      depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 := by
    dsimp only [f, depressedB610, a5, a4, a3]
    rw [hpDep, coeff_depressedSextic68_three]
  have hf2 : f.coeff 2 =
      depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 := by
    dsimp only [f, depressedC610, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedSextic68_two]
  have hf1 : f.coeff 1 =
      depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedD610, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedSextic68_one]
  have hf0 : f.coeff 0 =
      depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedE610, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedSextic68_zero]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨_hg10, hg9, hg8, _hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg9L : g.coeff 9 =
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL610, depressedL810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9]
  have hg8P : g.coeff 8 =
      depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP610, depressedP810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg7 : g.coeff 7 =
      depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedQ610, depressedQ810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg6 : g.coeff 6 =
      depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedR610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 : g.coeff 5 =
      depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedS610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 : g.coeff 4 =
      depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
        b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedT610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg3 : g.coeff 3 =
      depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedU610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg2 : g.coeff 2 =
      depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedV610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg1 : g.coeff 1 =
      depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedW610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hmonic :=
    scaleZero_exists_monicDepressedBracket_610 hp hq ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10) hN
      hDjac
  obtain ⟨hf_high, hf6, hf5, hg_high, hg10, hLconst, hjacg⟩ := hmonic
  have hfg :
      kappaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) =
        kappaResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have himgLam :
      algebraMap k[X] (RatFunc k)
          (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0) =
        lambdaResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [algebraMap_degreeZeroLambdaPolynomial610]
    rw [← lambdaResidual610_eq_integrated (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)]
    rw [← hl, ← hP, ← hQ, ← hR, ← hS, ← hT, ← hU, ← hV, ← hW]
    rw [hA, hB, hC, hD, hE]
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have himgKap :
      algebraMap k[X] (RatFunc k)
          (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0) =
        kappaResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [algebraMap_degreeZeroKappaPolynomial610]
    rw [← kappaResidual610_eq_integrated (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)]
    rw [← hl, ← hP, ← hQ, ← hR, ← hS, ← hT, ← hU, ← hV, ← hW]
    rw [hA, hB, hC, hD, hE]
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have himgMu :
      algebraMap k[X] (RatFunc k)
          (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0) =
        muResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [algebraMap_degreeZeroMuPolynomial610]
    rw [← muResidual610_eq_integrated (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)]
    rw [← hl, ← hP, ← hQ, ← hR, ← hS, ← hT, ← hU, ← hV, ← hW]
    rw [hA, hB, hC, hD, hE]
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have himgOmi :
      algebraMap k[X] (RatFunc k)
          (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0) =
        fourteenthResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [algebraMap_degreeZeroOmicronPolynomial610]
    rw [← fourteenthResidual610_eq_integrated (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)]
    rw [← hl, ← hP, ← hQ, ← hR, ← hS, ← hT, ← hU, ← hV, ← hW]
    rw [hA, hB, hC, hD, hE]
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have hderivLam :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0)) =
        0 := by
    rw [himgLam, haRes]
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      ratFuncDerivation68_C aRes
  have hderivKap :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroKappaPolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0)) =
        0 := by
    rw [himgKap, ← hfg]
    have h0 :=
      kappaResidual610_deriv_zero_of_monic_differentialJacobian
        ratFuncDerivation68 f g (RatFunc.C j' / hRF) hf_high hf6 hf5
        hg_high hg10 hLconst (by simpa [f, g, hRF] using hjacg)
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using h0
  have hfgMu :
      muResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) =
        muResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have hderivMu :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta
              eta theta A B C0 D0 E0)) =
        0 := by
    rw [himgMu, ← hfgMu]
    have h0 :=
      muResidual610_deriv_zero_of_monic_differentialJacobian
        ratFuncDerivation68 f g (RatFunc.C j' / hRF) hf_high hf6 hf5
        hg_high hg10 hLconst (by simpa [f, g, hRF] using hjacg)
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using h0
  have hfgOmi :
      fourteenthResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) =
        fourteenthResidual610
          (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
          (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
          (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
          (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
          (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1)
          (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
          (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
          (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
          (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5)
          (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) := by
    rw [hf4, hf3, hf2, hf1, hf0, hg9L, hg8P, hg7, hg6, hg5, hg4, hg3, hg2,
      hg1]
  have hderivOmi :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0)) =
        0 := by
    rw [himgOmi, ← hfgOmi]
    have h0 :=
      fourteenthResidual610_deriv_zero_of_monic_differentialJacobian
        ratFuncDerivation68 f g (RatFunc.C j' / hRF) hf_high hf6 hf5
        hg_high hg10 hLconst (by simpa [f, g, hRF] using hjacg)
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using h0
  obtain ⟨cLam, hcLam⟩ :=
    polynomial_eq_C_of_ratFuncDeriv
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0) hderivLam
  obtain ⟨cKap, hcKap⟩ :=
    polynomial_eq_C_of_ratFuncDeriv
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0) hderivKap
  obtain ⟨cMu, hcMu⟩ :=
    polynomial_eq_C_of_ratFuncDeriv
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0) hderivMu
  obtain ⟨cOmi, hcOmi⟩ :=
    polynomial_eq_C_of_ratFuncDeriv
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0) hderivOmi
  exact ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0, ht, hj,
    hjdiv, hHsq, hder, hdeg, hcLam,
    polynomial_natDegree_eq_zero_of_eq_C hcLam, hcKap,
    polynomial_natDegree_eq_zero_of_eq_C hcKap, hcMu,
    polynomial_natDegree_eq_zero_of_eq_C hcMu, hcOmi,
    polynomial_natDegree_eq_zero_of_eq_C hcOmi⟩

end SourceFirstIntegrals610

/-! ## Unique-`B` tie: `κ` companion cannot drop with `λ` -/

section UniqueBKappa610

variable {k : Type*} [Field k] [CharZero k]

private theorem zero_pow_two_km {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three_km {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four_km {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five_km {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

/-- Load-free two-term `κ` face on the unique-`B` tie, written without
nsmul so leading-coefficient arithmetic is direct. -/
def kappaHighBTieExpanded610 (A B : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B) + (20 / 243 : k) • (A * B ^ 3)

/-- `κ` with the unique-`B` tie face deleted. -/
def degreeZeroKappaNoHighBTieRest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(3 / 256 * l : k)) • A ^ 5 +
    (20 / 81 : k) • (A ^ 2 * B * C0) +
    (9 / 64 * l : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * D0) +
    (3 / 32 * l : k) • (A ^ 3 * C0) +
    (20 / 243 * alpha : k) • (A ^ 3 * B) +
    (385 / 31104 * beta : k) • A ^ 4 -
    (5 / 27 : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * D0) -
    (3 / 16 * l : k) • (B ^ 2 * C0) -
    (4 / 81 * alpha : k) • B ^ 3 -
    (10 / 27 : k) • (A * C0 * D0) -
    (3 / 16 * l : k) • (A * C0 ^ 2) -
    (10 / 27 : k) • (A * B * E0) -
    (3 / 8 * l : k) • (A * B * D0) -
    (8 / 27 * alpha : k) • (A * B * C0) -
    (35 / 432 * beta : k) • (A * B ^ 2) -
    (3 / 16 * l : k) • (A ^ 2 * E0) -
    (4 / 27 * alpha : k) • (A ^ 2 * D0) -
    (35 / 432 * beta : k) • (A ^ 2 * C0) +
    (35 / 1296 * delta : k) • A ^ 3 +
    (10 / 9 : k) • (D0 * E0) +
    (3 / 8 * l : k) • D0 ^ 2 +
    (3 / 4 * l : k) • (C0 * E0) +
    (4 / 9 * alpha : k) • (C0 * D0) +
    (7 / 72 * beta : k) • C0 ^ 2 +
    (4 / 9 * alpha : k) • (B * E0) +
    (7 / 36 * beta : k) • (B * D0) -
    (5 / 72 * delta : k) • B ^ 2 +
    (7 / 36 * beta : k) • (A * E0) -
    (5 / 36 * delta : k) • (A * C0) -
    (2 / 9 * epsilon : k) • (A * B) -
    (1 / 8 * zeta : k) • A ^ 2 +
    (5 / 6 * delta : k) • E0 +
    (2 / 3 * epsilon : k) • D0 +
    (1 / 2 * zeta : k) • C0 +
    (1 / 3 * eta : k) • B +
    (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaPolynomial610_eq_highBTie_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      kappaHighBTieExpanded610 A B +
        degreeZeroKappaNoHighBTieRest610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroKappaPolynomial610, kappaHighBTieExpanded610,
    degreeZeroKappaNoHighBTieRest610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoHighBTieRest610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroKappaNoHighBTieRest610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      4 * A.natDegree + B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  simp only [degreeZeroKappaNoHighBTieRest610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_km, zero_pow_three_km,
    zero_pow_four_km, zero_pow_five_km]
  compute_degree
  have hA1 : A.natDegree + 1 ≤ B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : C0.natDegree + 1 ≤ B.natDegree := Nat.succ_le_of_lt hC
  have hD1 : D0.natDegree + 1 ≤ B.natDegree := Nat.succ_le_of_lt hD
  have hE1 : E0.natDegree + 1 ≤ B.natDegree := Nat.succ_le_of_lt hE
  omega

/-- Leading-coefficient identity: `7 u = 12 v` forces the `λ` combination
`7 u² - 126 u v + 27 v²` to `-8253 v² / 49`. -/
theorem lambda_uv7_of_kappa_factor (u v : k)
    (h : (7 : k) * u = 12 * v) :
    (49 : k) * (7 * u ^ 2 - 126 * u * v + 27 * v ^ 2) =
      -8253 * v ^ 2 := by
  calc
    (49 : k) * (7 * u ^ 2 - 126 * u * v + 27 * v ^ 2)
        = 7 * ((7 * u) * (7 * u) - 882 * u * v + 189 * v ^ 2) := by ring
    _ = 7 * ((12 * v) * (12 * v) - 882 * u * v + 189 * v ^ 2) := by rw [h]
    _ = 7 * (333 * v ^ 2 - 882 * u * v) := by ring
    _ = 2331 * v ^ 2 - 882 * (7 * u) * v := by ring
    _ = 2331 * v ^ 2 - 882 * (12 * v) * v := by rw [h]
    _ = -8253 * v ^ 2 := by ring

theorem lambdaHighBTie_coeff_ne_zero_of_kappa_factor
    {A B : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hkap : (7 : k) * A.leadingCoeff ^ 3 = 12 * B.leadingCoeff ^ 2) :
    (35 / 6561 : k) * A.leadingCoeff ^ 6 -
        (70 / 729 : k) * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
          (5 / 243 : k) * B.leadingCoeff ^ 4 ≠
      0 := by
  set u := A.leadingCoeff ^ 3 with hu
  set v := B.leadingCoeff ^ 2 with hv
  have hvne : v ≠ 0 := pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hB)
  have hform :
      (49 : k) * (7 * u ^ 2 - 126 * u * v + 27 * v ^ 2) =
        -8253 * v ^ 2 :=
    lambda_uv7_of_kappa_factor u v (by simpa [u, v] using hkap)
  have hne : (7 : k) * u ^ 2 - 126 * u * v + 27 * v ^ 2 ≠ 0 := by
    intro hz
    have h49 : (49 : k) * (7 * u ^ 2 - 126 * u * v + 27 * v ^ 2) = 0 := by
      simp [hz]
    rw [hform] at h49
    have h8253 : (-8253 : k) ≠ 0 := by norm_num
    exact hvne ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp h49).resolve_left h8253))
  have hscale :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 -
          (70 / 729 : k) * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
            (5 / 243 : k) * B.leadingCoeff ^ 4 =
        (5 / 6561 : k) * (7 * u ^ 2 - 126 * u * v + 27 * v ^ 2) := by
    simp only [u, v]
    ring
  intro hz
  rw [hscale] at hz
  have h5 : (5 / 6561 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  exact hne ((mul_eq_zero.mp hz).resolve_left h5)

theorem lambdaHighBTieCombined610_natDegree_eq_of_coeff_ne
    {A B : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hcoeff :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 -
          (70 / 729 : k) * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
            (5 / 243 : k) * B.leadingCoeff ^ 4 ≠
        0) :
    (lambdaHighBTieCombined610 A B).natDegree = 4 * B.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hB4 : (B ^ 4).natDegree = 4 * B.natDegree := natDegree_pow B 4
  have hdeg6 : 6 * A.natDegree = 4 * B.natDegree := by omega
  have hA3B2 :
      (A ^ 3 * B ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) (pow_ne_zero 2 hB),
      natDegree_pow, natDegree_pow]
    omega
  have htop :
      (lambdaHighBTieCombined610 A B).coeff (4 * B.natDegree) ≠ 0 := by
    simp only [lambdaHighBTieCombined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 6).coeff (4 * B.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hdeg6, ← hA6, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 3 * B ^ 2).coeff (4 * B.natDegree) =
        A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 := by
      rw [← hA3B2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h3 : (B ^ 4).coeff (4 * B.natDegree) = B.leadingCoeff ^ 4 := by
      rw [← hB4, coeff_natDegree, leadingCoeff_pow]
    simpa [h1, h2, h3] using hcoeff
  have hle :
      (lambdaHighBTieCombined610 A B).natDegree ≤ 4 * B.natDegree := by
    simp only [lambdaHighBTieCombined610]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_smul_le610 _ _).trans (hA6.symm ▸ hdeg6.le)
      · exact (natDegree_smul_le610 _ _).trans hA3B2.le
    · exact (natDegree_smul_le610 _ _).trans hB4.le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

/-- On the unique-`B` tie, a dropped `λ` combination cannot occur together
with a dropped `κ` companion. -/
theorem kappa_highBTie_impossible_of_lambda_drop
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0)
    (hlamDrop :
      (lambdaHighBTieCombined610 A B).natDegree < 4 * B.natDegree)
    (hkapDeg :
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBpos : 0 < B.natDegree := hcone.1.1
  have htie : 3 * A.natDegree = 2 * B.natDegree := hcone.2
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    have hA : A.natDegree < B.natDegree := hcone.1.2.1
    omega
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  by_cases hdrop :
      (7 : k) * A.leadingCoeff ^ 3 - 12 * B.leadingCoeff ^ 2 = 0
  · have hrel : (7 : k) * A.leadingCoeff ^ 3 =
        12 * B.leadingCoeff ^ 2 := by linear_combination hdrop
    have hlamNe :=
      lambdaHighBTie_coeff_ne_zero_of_kappa_factor hAne hBne htie hrel
    have hcombdeg :=
      lambdaHighBTieCombined610_natDegree_eq_of_coeff_ne hAne hBne htie
        hlamNe
    exact (Nat.not_lt.mpr (le_of_eq hcombdeg.symm)) hlamDrop
  · have hA4B :
        (A ^ 4 * B).natDegree = 4 * A.natDegree + B.natDegree := by
      rw [natDegree_mul (pow_ne_zero 4 hAne) hBne, natDegree_pow]
    have hAB3 :
        (A * B ^ 3).natDegree = 4 * A.natDegree + B.natDegree := by
      rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
      omega
    have htop :
        (kappaHighBTieExpanded610 A B).coeff
            (4 * A.natDegree + B.natDegree) ≠
          0 := by
      simp only [kappaHighBTieExpanded610, coeff_add, coeff_smul,
        smul_eq_mul]
      have h1 : (A ^ 4 * B).coeff (4 * A.natDegree + B.natDegree) =
          A.leadingCoeff ^ 4 * B.leadingCoeff := by
        rw [← hA4B, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      have h2 : (A * B ^ 3).coeff (4 * A.natDegree + B.natDegree) =
          A.leadingCoeff * B.leadingCoeff ^ 3 := by
        rw [← hAB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      simp only [h1, h2]
      have h35 : (-(35 / 729 : k)) ≠ 0 := by
        have : (35 / 729 : k) ≠ 0 :=
          div_ne_zero (by norm_num) (by norm_num)
        intro h0
        exact this (neg_eq_zero.mp h0)
      have h20 : (20 / 243 : k) ≠ 0 :=
        div_ne_zero (by norm_num) (by norm_num)
      -- Combined leading form is (-5/729) a b (7 a³ - 12 b²).
      have :
          (-(35 / 729 : k)) * (A.leadingCoeff ^ 4 * B.leadingCoeff) +
              (20 / 243 : k) * (A.leadingCoeff * B.leadingCoeff ^ 3) =
            (-(5 / 729 : k)) * A.leadingCoeff * B.leadingCoeff *
              (7 * A.leadingCoeff ^ 3 - 12 * B.leadingCoeff ^ 2) := by
        ring
      rw [this]
      exact mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by
              have : (5 / 729 : k) ≠ 0 :=
                div_ne_zero (by norm_num) (by norm_num)
              intro h0
              exact this (neg_eq_zero.mp h0))
            (leadingCoeff_ne_zero.mpr hAne))
          (leadingCoeff_ne_zero.mpr hBne))
        hdrop
    have hle :
        (kappaHighBTieExpanded610 A B).natDegree ≤
          4 * A.natDegree + B.natDegree := by
      simp only [kappaHighBTieExpanded610]
      exact (natDegree_add_le _ _).trans
        (max_le ((natDegree_smul_le610 _ _).trans hA4B.le)
          ((natDegree_smul_le610 _ _).trans hAB3.le))
    have hcombdeg :
        (kappaHighBTieExpanded610 A B).natDegree =
          4 * A.natDegree + B.natDegree :=
      natDegree_eq_of_le_of_coeff_ne_zero hle htop
    have hrest :=
      degreeZeroKappaNoHighBTieRest610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C0 D0 E0 hcone
    have hsum :=
      degreeZeroKappaPolynomial610_eq_highBTie_add_rest l alpha beta
        delta epsilon zeta eta theta A B C0 D0 E0
    rw [hsum, natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hkapDeg
    omega

end UniqueBKappa610

/-! ## Weighted unique `λ` faces beyond the parent cones -/

section WeightedLambda610

variable {k : Type*} [Field k] [CharZero k]

/-- Unique weighted `A⁶` face, allowing some letters to outrank `A` in
ordinary degree so long as they stay below `6 deg A` in the four-face
weights, and so long as the load-free `D₀` monomials stay strictly
lighter. -/
def WeightedALeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    4 * B.natDegree < 6 * A.natDegree ∧
    3 * C0.natDegree < 6 * A.natDegree ∧
    2 * E0.natDegree < 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

def WeightedBLeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    3 * C0.natDegree < 4 * B.natDegree ∧
    2 * E0.natDegree < 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 4 * B.natDegree

def WeightedC0LeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    6 * A.natDegree < 3 * C0.natDegree ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    2 * E0.natDegree < 3 * C0.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 3 * C0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 3 * C0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 3 * C0.natDegree

def WeightedE0LeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    6 * A.natDegree < 2 * E0.natDegree ∧
    4 * B.natDegree < 2 * E0.natDegree ∧
    3 * C0.natDegree < 2 * E0.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 2 * E0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 2 * E0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 2 * E0.natDegree

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoA6_natDegree_lt_of_weighted_A
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedALeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoA6Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_km, zero_pow_three_km,
    zero_pow_four_km, zero_pow_five_km]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoB4_natDegree_lt_of_weighted_B
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedBLeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hA, hC, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoB4Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_km, zero_pow_three_km,
    zero_pow_four_km, zero_pow_five_km]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoC03_natDegree_lt_of_weighted_C0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedC0LeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨hCpos, hA, hB, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoC03Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_km, zero_pow_three_km,
    zero_pow_four_km, zero_pow_five_km]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoE02_natDegree_lt_of_weighted_E0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedE0LeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoE02Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_km, zero_pow_three_km,
    zero_pow_four_km, zero_pow_five_km]
  compute_degree
  omega

theorem lambda_A6_impossible_of_weighted_A
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedALeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (35 / 6561 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((35 / 6561 : k) • A ^ 6).natDegree = 6 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoA6_natDegree_lt_of_weighted_A l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

theorem lambda_B4_impossible_of_weighted_B
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedBLeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hc : (5 / 243 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead : ((5 / 243 : k) • B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoB4_natDegree_lt_of_weighted_B l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_B4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, _⟩
  omega

theorem lambda_C03_impossible_of_weighted_C0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedC0LeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨hCpos, _⟩
    simp [hC0] at hCpos
  have hc : (-(5 / 81 : k)) ≠ 0 := by
    have : (5 / 81 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    intro h0
    exact this (neg_eq_zero.mp h0)
  have hlead :
      ((-(5 / 81 : k)) • C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoC03_natDegree_lt_of_weighted_C0 l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_C03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, _⟩
  omega

theorem lambda_E02_impossible_of_weighted_E0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedE0LeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hE : E0 ≠ 0 := by
    intro hE0
    rcases hcone with ⟨hEpos, _⟩
    simp [hE0] at hEpos
  have hc : (5 / 9 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead : ((5 / 9 : k) • E0 ^ 2).natDegree = 2 * E0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoE02_natDegree_lt_of_weighted_E0 l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_E02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, _⟩
  omega

end WeightedLambda610

/-! ## Closed faces and remaining residual -/

section ClosedFaces610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem HighBTieCone610_lambda_drop
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    (lambdaHighBTieCombined610 A B).natDegree < 4 * B.natDegree := by
  by_contra h
  have hge : 4 * B.natDegree ≤
      (lambdaHighBTieCombined610 A B).natDegree := Nat.not_lt.mp h
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    have := hcone.2
    have := hcone.1.1
    omega
  have hBne : B ≠ 0 := by
    intro hB0
    have := hcone.1.1
    simp [hB0] at this
  have htie : 3 * A.natDegree = 2 * B.natDegree := hcone.2
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hB4 : (B ^ 4).natDegree = 4 * B.natDegree := natDegree_pow B 4
  have hA3B2 :
      (A ^ 3 * B ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne),
      natDegree_pow, natDegree_pow]
    omega
  have hle :
      (lambdaHighBTieCombined610 A B).natDegree ≤ 4 * B.natDegree := by
    simp only [lambdaHighBTieCombined610]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · have hdeg6 : 6 * A.natDegree = 4 * B.natDegree := by omega
        exact (natDegree_smul_le610 _ _).trans (hA6.symm ▸ hdeg6.le)
      · exact (natDegree_smul_le610 _ _).trans hA3B2.le
    · exact (natDegree_smul_le610 _ _).trans hB4.le
  have heq : (lambdaHighBTieCombined610 A B).natDegree =
      4 * B.natDegree := le_antisymm hle hge
  exact lambda_highBTie_impossible_of_combined_degree l alpha beta delta
    epsilon zeta eta theta A B C0 D0 E0 hcone heq hdeg

/-- Source-facing packet: `κ, λ, μ, ο` are ground constants, every unique
weighted `λ` face (including those beyond the parent AMaximal / BLeads /
C0Leads / E0Leads cones) is empty, and the unique-`B` tie is empty even
after the `λ` combination drops.  Remaining cones are the ratio-ties of
two or more of `{6 deg A, 4 deg B, 3 deg C₀, 2 deg E₀}` with dropped
load-free combination, and unique-high `D₀` with another letter
nonconstant.  The unused integrals `μ` and `ο` are the next comparison
on those leftover chambers. -/
theorem normalized610ScaleZero_kappaMuFaces_closed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        Polynomial.C (j / t) ∧
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 ∧
      degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cLam ∧
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cKap ∧
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cMu ∧
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cOmi ∧
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      ¬ AMaximalCone610 A B C0 D0 E0 ∧
      ¬ BLeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ C0LeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ E0LeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ HighBTieCone610 A B C0 D0 E0 ∧
      ¬ WeightedALeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedBLeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedC0LeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedE0LeadsCone610 A B C0 D0 E0 ∧
      ¬ ExtremeHighBCone610 A B C0 D0 E0 ∧
      ¬ A6BLeadsHighBCone610 A B C0 D0 E0 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ 0 < B.natDegree ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0,
      ht, hj, hjdiv, hHsq, hder, hdeg, hcLam, hlamDeg, hcKap, hkapDeg,
      hcMu, hmuDeg, hcOmi, homiDeg⟩ :=
    normalized610ScaleZero_firstIntegrals_eq_C hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0, ht,
    hj, hjdiv, hHsq, hder, hdeg, hcLam, hlamDeg, hcKap, hkapDeg, hcMu,
    hmuDeg, hcOmi, homiDeg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro hAmax
    exact lambda_A6_impossible_of_A_maximal l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hAmax hlamDeg
  · intro hBleads
    exact lambda_B4_impossible_of_B_leads l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hBleads hlamDeg
  · intro hCleads
    exact lambda_C03_impossible_of_C0_leads l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hCleads hlamDeg
  · intro hEleads
    exact lambda_E02_impossible_of_E0_leads l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hEleads hlamDeg
  · intro hBtie
    have hdrop :=
      HighBTieCone610_lambda_drop l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 hBtie hlamDeg
    exact kappa_highBTie_impossible_of_lambda_drop l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hBtie hdrop hkapDeg
  · intro hWA
    exact lambda_A6_impossible_of_weighted_A l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hWA hlamDeg
  · intro hWB
    exact lambda_B4_impossible_of_weighted_B l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hWB hlamDeg
  · intro hWC
    exact lambda_C03_impossible_of_weighted_C0 l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hWC hlamDeg
  · intro hWE
    exact lambda_E02_impossible_of_weighted_E0 l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hWE hlamDeg
  · intro hExt
    exact extremeHighB_impossible l alpha beta delta epsilon zeta eta
      theta (j / t) A B C0 D0 E0 hjdiv hExt hder
  · intro hA6B
    exact uniqueHighB_impossible_of_A6B_leads l alpha beta delta epsilon
      zeta eta theta (j / t) A B C0 D0 E0 hjdiv hA6B hder
  · intro hDonly
    exact uniqueNonconstantD0_impossible l alpha beta delta epsilon zeta
      eta theta (j / t) A B C0 D0 E0 hjdiv hDonly.1 hDonly.2.1
      hDonly.2.2.1 hDonly.2.2.2.1 hDonly.2.2.2.2 hder
  · intro hBonly
    exact uniqueNonconstantB_impossible l alpha beta delta epsilon zeta
      eta theta (j / t) A B C0 D0 E0 hjdiv hBonly.1 hBonly.2.1
      hBonly.2.2.1 hBonly.2.2.2.1 hBonly.2.2.2.2 hder
  · intro hconst
    exact degreeZeroPrimitivePolynomial610_false_of_constant_core l alpha
      beta delta epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv
      hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1 hconst.2.2.2.2 hder

/-- Remaining cones after `κ` closes the unique-`B` drop and the broader
unique weighted `λ` faces are empty.  Next unused data: `μ` and `ο` on
the ratio-ties `A`–`C₀`, `A`–`E₀`, `B`–`C₀`, `B`–`E₀`, `C₀`–`E₀` and on
unique-high `D₀` with another letter nonconstant. -/
theorem normalized610ScaleZero_coneKappaMuResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      ¬ HighBTieCone610 A B C0 D0 E0 ∧
      ¬ WeightedALeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedBLeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedC0LeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedE0LeadsCone610 A B C0 D0 E0 := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0,
      ht, hj, hjdiv, hHsq, hder, hdeg, hcLam, hlamDeg, hcKap, hkapDeg,
      hcMu, hmuDeg, hcOmi, homiDeg, _hAmax, _hBleads, _hCleads, _hEleads,
      hBtie, hWA, hWB, hWC, hWE, _hExt, _hA6B, _hDonly, _hBonly,
      _hconst⟩ :=
    normalized610ScaleZero_kappaMuFaces_closed hsource
  exact ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0, ht,
    hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hBtie, hWA,
    hWB, hWC, hWE⟩

end ClosedFaces610


#print axioms degreeZeroMuPolynomial610
#print axioms kappaResidual610_eq_integrated
#print axioms muResidual610_eq_integrated
#print axioms fourteenthResidual610_eq_integrated
#print axioms kappaResidual610_deriv_zero_of_monic_differentialJacobian
#print axioms muResidual610_deriv_zero_of_monic_differentialJacobian
#print axioms normalized610ScaleZero_firstIntegrals_eq_C
#print axioms kappa_highBTie_impossible_of_lambda_drop
#print axioms lambda_A6_impossible_of_weighted_A
#print axioms normalized610ScaleZero_kappaMuFaces_closed
#print axioms normalized610ScaleZero_coneKappaMuResidual

end Max11DegreeRoutes
