import Grok610ScaleZeroConeFinalScratch
import Grok610AlignedSquareChamberClosureScratch

/-! # Scale-zero cone terminal for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroConeFinalScratch` on the constant core
`H = (C t)²`.  That file closed every leftover unique Newton face of
degree greater than one that the cascade still named, and recorded the
remaining cones in `normalized610ScaleZero_coneFinalResidual`.  The
degree-one primitive cannot kill those chambers (in particular the
primitive-degree-one unique-`E₀` face).  The unused first integrals
`κ, λ, μ` and the weight-seventy residual `ο` supply the missing
comparison.

CAS job `derive_610_scale_zero_cone_terminal.py` (outer degrees
`(6,10)`, leading `H³`, `H⁵` with `H` a nonzero constant) substitutes
the triangular Faber constants into `lambdaResidual610` and
`kappaResidual610`.  After that substitution the load-free faces

* `(35/6561) A⁶` of degree `6 deg A`,
* `(5/243) B⁴` of degree `4 deg B`,
* `-(5/81) C₀³` of degree `3 deg C₀`,
* `(5/9) E₀²` of degree `2 deg E₀`

never meet a load term of equal degree (loads are ground constants).
Consequently a unique maximum among `{6 deg A, 4 deg B, 3 deg C₀,
2 deg E₀}` is empty.  The unique-`B` tie `3 deg A = 2 deg B` is empty
unless the three-term combination `7 A⁶ - 126 A³ B² + 27 B⁴` drops
below `4 deg B`, in which case the companion `κ` face
`A B (7 A³ - 12 B²)` cannot drop simultaneously (leading-coefficient
arithmetic, no finite-root extraction).

Reuses `a7_leads_impossible_of_l_ne`,
`uniqueHighA_impossible_of_A6cancel_A5_ne`, and
`uniqueHighB_tie_impossible_of_combined_degree` from the parent.

The unique weighted faces of `λ` are closed on the `A`-maximal cone, the
unique-high `B`/`C₀`/`E₀` weighted cones, and the unique-`B` tie with full
combined degree.  Pair-ratio ties with a dropped load-free combination,
and unique-high `D₀` with another letter nonconstant, are recorded rather
than forced.  No total-degree or twice-prime theorem is used.  No `sorry`,
no new axioms, no finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Polynomial pullbacks of the integrated first integrals -/

section FirstIntegralPolynomials610

variable {k : Type*} [Field k] [CharZero k]

/-- Polynomial pullback of `lambdaResidual610` after the triangular Faber
coordinates are ground constants.  CAS: 50 terms. -/
def degreeZeroLambdaPolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (5 / 9 : k) • E0 ^ 2 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

/-- Polynomial pullback of `kappaResidual610` after the triangular Faber
coordinates are ground constants.  CAS: 40 terms. -/
def degreeZeroKappaPolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B) -
    (3 / 256 * l : k) • A ^ 5 +
    (20 / 243 : k) • (A * B ^ 3) +
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

/-- `A` is a (not necessarily unique) maximum of the free core: every
other letter has degree at most `deg A`.  On this cone the face `A⁶` of
`λ` is unique of degree `6 deg A ≥ 6`, including the shared maximum of
`A` with `B`. -/
def AMaximalCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    B.natDegree ≤ A.natDegree ∧
    C0.natDegree ≤ A.natDegree ∧
    D0.natDegree ≤ A.natDegree ∧
    E0.natDegree ≤ A.natDegree

/-- Unique-`B` with `4 deg B` strictly above `6 deg A`. -/
def BLeadsWeightedCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  UniqueHighBCone610 A B C0 D0 E0 ∧
    3 * A.natDegree < 2 * B.natDegree

/-- Unique-`C₀` with `3 deg C₀` strictly above `6 deg A` and `4 deg B`. -/
def C0LeadsWeightedCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  UniqueHighC0Cone610 A B C0 D0 E0 ∧
    2 * A.natDegree < C0.natDegree ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    2 * E0.natDegree < 3 * C0.natDegree

/-- Unique nonconstant `E₀` with the other four letters of degree zero.
On this cone the face `E₀²` of `λ` is unique of degree `2 deg E₀ ≥ 2`,
including the primitive-degree-one chamber. -/
def E0LeadsWeightedCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  UniqueHighE0Cone610 A B C0 D0 E0 ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0

/-- Load-free three-term combination of the unique-`B` tie faces of `λ`. -/
def lambdaHighBTieCombined610 (A B : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) +
    (5 / 243 : k) • B ^ 4

/-- Companion `κ` face on the unique-`B` tie. -/
def kappaHighBTieCombined610 (A B : k[X]) : k[X] :=
  (-(5 / 729 : k)) • (A * B * (7 • A ^ 3 - 12 • B ^ 2))

end FirstIntegralPolynomials610

/-! ## Splittings -/

section LambdaSplittings610

variable {k : Type*} [Field k] [CharZero k]

/-- `λ` with the unique `A⁶` face deleted. -/
def degreeZeroLambdaNoA6Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(70 / 729 : k)) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (5 / 9 : k) • E0 ^ 2 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_A6_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (35 / 6561 : k) • A ^ 6 +
        degreeZeroLambdaNoA6Polynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610,
    degreeZeroLambdaNoA6Polynomial610]
  module

/-- `λ` with the unique `B⁴` face deleted. -/
def degreeZeroLambdaNoB4Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (5 / 9 : k) • E0 ^ 2 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_B4_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (5 / 243 : k) • B ^ 4 +
        degreeZeroLambdaNoB4Polynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610,
    degreeZeroLambdaNoB4Polynomial610]
  module

/-- `λ` with the unique `C₀³` face deleted. -/
def degreeZeroLambdaNoC03Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (5 / 9 : k) • E0 ^ 2 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_C03_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(5 / 81 : k)) • C0 ^ 3 +
        degreeZeroLambdaNoC03Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610,
    degreeZeroLambdaNoC03Polynomial610]
  module

/-- `λ` with the unique `E₀²` face deleted. -/
def degreeZeroLambdaNoE02Polynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6 -
    (70 / 729 : k) • (A ^ 3 * B ^ 2) -
    (35 / 729 : k) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (5 / 243 : k) • B ^ 4 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_E02_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (5 / 9 : k) • E0 ^ 2 +
        degreeZeroLambdaNoE02Polynomial610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610,
    degreeZeroLambdaNoE02Polynomial610]
  module

/-- `λ` with the three unique-`B` tie faces deleted. -/
def degreeZeroLambdaNoHighBTieRest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * C0) -
    (15 / 256 * l : k) • (A ^ 4 * B) -
    (8 / 729 * alpha : k) • A ^ 5 +
    (20 / 81 : k) • (A * B ^ 2 * C0) +
    (3 / 32 * l : k) • (A * B ^ 3) +
    (10 / 81 : k) • (A ^ 2 * C0 ^ 2) +
    (20 / 81 : k) • (A ^ 2 * B * D0) +
    (9 / 32 * l : k) • (A ^ 2 * B * C0) +
    (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * E0) +
    (3 / 32 * l : k) • (A ^ 3 * D0) +
    (20 / 243 * alpha : k) • (A ^ 3 * C0) +
    (385 / 7776 * beta : k) • (A ^ 3 * B) -
    (5 / 81 : k) • C0 ^ 3 -
    (10 / 27 : k) • (B * C0 * D0) -
    (3 / 16 * l : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0) -
    (3 / 8 * l : k) • (A * C0 * D0) -
    (4 / 27 * alpha : k) • (A * C0 ^ 2) -
    (3 / 8 * l : k) • (A * B * E0) -
    (8 / 27 * alpha : k) • (A * B * D0) -
    (35 / 216 * beta : k) • (A * B * C0) -
    (4 / 27 * alpha : k) • (A ^ 2 * E0) -
    (35 / 432 * beta : k) • (A ^ 2 * D0) +
    (35 / 432 * delta : k) • (A ^ 2 * B) +
    (4 / 81 * epsilon : k) • A ^ 3 +
    (5 / 9 : k) • E0 ^ 2 +
    (3 / 4 * l : k) • (D0 * E0) +
    (2 / 9 * alpha : k) • D0 ^ 2 +
    (4 / 9 * alpha : k) • (C0 * E0) +
    (7 / 36 * beta : k) • (C0 * D0) +
    (7 / 36 * beta : k) • (B * E0) -
    (5 / 36 * delta : k) • (B * C0) -
    (1 / 9 * epsilon : k) • B ^ 2 -
    (5 / 36 * delta : k) • (A * D0) -
    (2 / 9 * epsilon : k) • (A * C0) -
    (1 / 4 * zeta : k) • (A * B) -
    (1 / 9 * eta : k) • A ^ 2 +
    (2 / 3 * epsilon : k) • E0 +
    (1 / 2 * zeta : k) • D0 +
    (1 / 3 * eta : k) • C0 +
    (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaPolynomial610_eq_highBTie_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      lambdaHighBTieCombined610 A B +
        degreeZeroLambdaNoHighBTieRest610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaPolynomial610, lambdaHighBTieCombined610,
    degreeZeroLambdaNoHighBTieRest610]
  module

private theorem zero_pow_two {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

end LambdaSplittings610

/-! ## Eight-term groups of each `λ` rest polynomial -/

section LambdaGroups610

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_add6_lt610
    {p1 p2 p3 p4 p5 p6 : k[X]} {d : ℕ}
    (h1 : p1.natDegree < d) (h2 : p2.natDegree < d)
    (h3 : p3.natDegree < d) (h4 : p4.natDegree < d)
    (h5 : p5.natDegree < d) (h6 : p6.natDegree < d) :
    (p1 + p2 + p3 + p4 + p5 + p6).natDegree < d :=
  natDegree_add_lt610
    (natDegree_add_lt610
      (natDegree_add_lt610
        (natDegree_add_lt610 (natDegree_add_lt610 h1 h2) h3) h4) h5)
    h6

def degreeZeroLambdaNoA6G1_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(70 / 729 : k)) • (A ^ 3 * B ^ 2)
    - (35 / 729 : k) • (A ^ 4 * C0)
    - (15 / 256 * l : k) • (A ^ 4 * B)
    - (8 / 729 * alpha : k) • A ^ 5
    + (5 / 243 : k) • B ^ 4
    + (20 / 81 : k) • (A * B ^ 2 * C0)
    + (3 / 32 * l : k) • (A * B ^ 3)

def degreeZeroLambdaNoA6G2_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (10 / 81 : k) • (A ^ 2 * C0 ^ 2)
    + (20 / 81 : k) • (A ^ 2 * B * D0)
    + (9 / 32 * l : k) • (A ^ 2 * B * C0)
    + (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * E0)
    + (3 / 32 * l : k) • (A ^ 3 * D0)

def degreeZeroLambdaNoA6G3_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (20 / 243 * alpha : k) • (A ^ 3 * C0)
    + (385 / 7776 * beta : k) • (A ^ 3 * B)
    - (5 / 81 : k) • C0 ^ 3
    - (10 / 27 : k) • (B * C0 * D0)
    - (3 / 16 * l : k) • (B * C0 ^ 2)
    - (5 / 27 : k) • (B ^ 2 * E0)

def degreeZeroLambdaNoA6G4_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (3 / 16 * l : k) • (B ^ 2 * D0)
    - (4 / 27 * alpha : k) • (B ^ 2 * C0)
    - (35 / 1296 * beta : k) • B ^ 3
    - (5 / 27 : k) • (A * D0 ^ 2)
    - (10 / 27 : k) • (A * C0 * E0)
    - (3 / 8 * l : k) • (A * C0 * D0)

def degreeZeroLambdaNoA6G5_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (4 / 27 * alpha : k) • (A * C0 ^ 2)
    - (3 / 8 * l : k) • (A * B * E0)
    - (8 / 27 * alpha : k) • (A * B * D0)
    - (35 / 216 * beta : k) • (A * B * C0)
    - (4 / 27 * alpha : k) • (A ^ 2 * E0)
    - (35 / 432 * beta : k) • (A ^ 2 * D0)

def degreeZeroLambdaNoA6G6_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 432 * delta : k) • (A ^ 2 * B)
    + (4 / 81 * epsilon : k) • A ^ 3
    + (5 / 9 : k) • E0 ^ 2
    + (3 / 4 * l : k) • (D0 * E0)
    + (2 / 9 * alpha : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (C0 * E0)

def degreeZeroLambdaNoA6G7_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (7 / 36 * beta : k) • (C0 * D0)
    + (7 / 36 * beta : k) • (B * E0)
    - (5 / 36 * delta : k) • (B * C0)
    - (1 / 9 * epsilon : k) • B ^ 2
    - (5 / 36 * delta : k) • (A * D0)
    - (2 / 9 * epsilon : k) • (A * C0)

def degreeZeroLambdaNoA6G8_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (1 / 4 * zeta : k) • (A * B)
    - (1 / 9 * eta : k) • A ^ 2
    + (2 / 3 * epsilon : k) • E0
    + (1 / 2 * zeta : k) • D0
    + (1 / 3 * eta : k) • C0
    + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoA6Polynomial610_eq_groups
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaNoA6Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      degreeZeroLambdaNoA6G1_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoA6G2_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoA6G3_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoA6G4_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoA6G5_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoA6G6_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoA6G7_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoA6G8_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaNoA6Polynomial610,
    degreeZeroLambdaNoA6G1_610,
    degreeZeroLambdaNoA6G2_610,
    degreeZeroLambdaNoA6G3_610,
    degreeZeroLambdaNoA6G4_610,
    degreeZeroLambdaNoA6G5_610,
    degreeZeroLambdaNoA6G6_610,
    degreeZeroLambdaNoA6G7_610,
    degreeZeroLambdaNoA6G8_610
    ]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoA6G1_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6G1_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  simp only [degreeZeroLambdaNoA6G1_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoA6G2_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6G2_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  simp only [degreeZeroLambdaNoA6G2_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoA6G3_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6G3_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  simp only [degreeZeroLambdaNoA6G3_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoA6G4_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6G4_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  simp only [degreeZeroLambdaNoA6G4_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoA6G5_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6G5_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  simp only [degreeZeroLambdaNoA6G5_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoA6G6_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6G6_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  simp only [degreeZeroLambdaNoA6G6_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoA6G7_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6G7_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  simp only [degreeZeroLambdaNoA6G7_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoA6G8_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6G8_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  simp only [degreeZeroLambdaNoA6G8_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

theorem degreeZeroLambdaNoA6Polynomial610_natDegree_lt_of_groups
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rw [degreeZeroLambdaNoA6Polynomial610_eq_groups]
  exact natDegree_add8_lt610
    (degreeZeroLambdaNoA6G1_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoA6G2_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoA6G3_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoA6G4_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoA6G5_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoA6G6_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoA6G7_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoA6G8_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)

def degreeZeroLambdaNoB4G1_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6
    - (70 / 729 : k) • (A ^ 3 * B ^ 2)
    - (35 / 729 : k) • (A ^ 4 * C0)
    - (15 / 256 * l : k) • (A ^ 4 * B)
    - (8 / 729 * alpha : k) • A ^ 5
    + (20 / 81 : k) • (A * B ^ 2 * C0)
    + (3 / 32 * l : k) • (A * B ^ 3)

def degreeZeroLambdaNoB4G2_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (10 / 81 : k) • (A ^ 2 * C0 ^ 2)
    + (20 / 81 : k) • (A ^ 2 * B * D0)
    + (9 / 32 * l : k) • (A ^ 2 * B * C0)
    + (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * E0)
    + (3 / 32 * l : k) • (A ^ 3 * D0)

def degreeZeroLambdaNoB4G3_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (20 / 243 * alpha : k) • (A ^ 3 * C0)
    + (385 / 7776 * beta : k) • (A ^ 3 * B)
    - (5 / 81 : k) • C0 ^ 3
    - (10 / 27 : k) • (B * C0 * D0)
    - (3 / 16 * l : k) • (B * C0 ^ 2)
    - (5 / 27 : k) • (B ^ 2 * E0)

def degreeZeroLambdaNoB4G4_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (3 / 16 * l : k) • (B ^ 2 * D0)
    - (4 / 27 * alpha : k) • (B ^ 2 * C0)
    - (35 / 1296 * beta : k) • B ^ 3
    - (5 / 27 : k) • (A * D0 ^ 2)
    - (10 / 27 : k) • (A * C0 * E0)
    - (3 / 8 * l : k) • (A * C0 * D0)

def degreeZeroLambdaNoB4G5_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (4 / 27 * alpha : k) • (A * C0 ^ 2)
    - (3 / 8 * l : k) • (A * B * E0)
    - (8 / 27 * alpha : k) • (A * B * D0)
    - (35 / 216 * beta : k) • (A * B * C0)
    - (4 / 27 * alpha : k) • (A ^ 2 * E0)
    - (35 / 432 * beta : k) • (A ^ 2 * D0)

def degreeZeroLambdaNoB4G6_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 432 * delta : k) • (A ^ 2 * B)
    + (4 / 81 * epsilon : k) • A ^ 3
    + (5 / 9 : k) • E0 ^ 2
    + (3 / 4 * l : k) • (D0 * E0)
    + (2 / 9 * alpha : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (C0 * E0)

def degreeZeroLambdaNoB4G7_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (7 / 36 * beta : k) • (C0 * D0)
    + (7 / 36 * beta : k) • (B * E0)
    - (5 / 36 * delta : k) • (B * C0)
    - (1 / 9 * epsilon : k) • B ^ 2
    - (5 / 36 * delta : k) • (A * D0)
    - (2 / 9 * epsilon : k) • (A * C0)

def degreeZeroLambdaNoB4G8_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (1 / 4 * zeta : k) • (A * B)
    - (1 / 9 * eta : k) • A ^ 2
    + (2 / 3 * epsilon : k) • E0
    + (1 / 2 * zeta : k) • D0
    + (1 / 3 * eta : k) • C0
    + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoB4Polynomial610_eq_groups
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaNoB4Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      degreeZeroLambdaNoB4G1_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoB4G2_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoB4G3_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoB4G4_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoB4G5_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoB4G6_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoB4G7_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoB4G8_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaNoB4Polynomial610,
    degreeZeroLambdaNoB4G1_610,
    degreeZeroLambdaNoB4G2_610,
    degreeZeroLambdaNoB4G3_610,
    degreeZeroLambdaNoB4G4_610,
    degreeZeroLambdaNoB4G5_610,
    degreeZeroLambdaNoB4G6_610,
    degreeZeroLambdaNoB4G7_610,
    degreeZeroLambdaNoB4G8_610
    ]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoB4G1_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4G1_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hwt⟩
  simp only [degreeZeroLambdaNoB4G1_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoB4G2_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4G2_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hwt⟩
  simp only [degreeZeroLambdaNoB4G2_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoB4G3_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4G3_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hwt⟩
  simp only [degreeZeroLambdaNoB4G3_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoB4G4_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4G4_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hwt⟩
  simp only [degreeZeroLambdaNoB4G4_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoB4G5_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4G5_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hwt⟩
  simp only [degreeZeroLambdaNoB4G5_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoB4G6_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4G6_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hwt⟩
  simp only [degreeZeroLambdaNoB4G6_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoB4G7_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4G7_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hwt⟩
  simp only [degreeZeroLambdaNoB4G7_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoB4G8_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4G8_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hwt⟩
  simp only [degreeZeroLambdaNoB4G8_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

theorem degreeZeroLambdaNoB4Polynomial610_natDegree_lt_of_groups
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rw [degreeZeroLambdaNoB4Polynomial610_eq_groups]
  exact natDegree_add8_lt610
    (degreeZeroLambdaNoB4G1_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoB4G2_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoB4G3_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoB4G4_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoB4G5_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoB4G6_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoB4G7_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoB4G8_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)

def degreeZeroLambdaNoC03G1_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6
    - (70 / 729 : k) • (A ^ 3 * B ^ 2)
    - (35 / 729 : k) • (A ^ 4 * C0)
    - (15 / 256 * l : k) • (A ^ 4 * B)
    - (8 / 729 * alpha : k) • A ^ 5
    + (5 / 243 : k) • B ^ 4
    + (20 / 81 : k) • (A * B ^ 2 * C0)

def degreeZeroLambdaNoC03G2_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (3 / 32 * l : k) • (A * B ^ 3)
    + (10 / 81 : k) • (A ^ 2 * C0 ^ 2)
    + (20 / 81 : k) • (A ^ 2 * B * D0)
    + (9 / 32 * l : k) • (A ^ 2 * B * C0)
    + (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * E0)

def degreeZeroLambdaNoC03G3_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (3 / 32 * l : k) • (A ^ 3 * D0)
    + (20 / 243 * alpha : k) • (A ^ 3 * C0)
    + (385 / 7776 * beta : k) • (A ^ 3 * B)
    - (10 / 27 : k) • (B * C0 * D0)
    - (3 / 16 * l : k) • (B * C0 ^ 2)
    - (5 / 27 : k) • (B ^ 2 * E0)

def degreeZeroLambdaNoC03G4_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (3 / 16 * l : k) • (B ^ 2 * D0)
    - (4 / 27 * alpha : k) • (B ^ 2 * C0)
    - (35 / 1296 * beta : k) • B ^ 3
    - (5 / 27 : k) • (A * D0 ^ 2)
    - (10 / 27 : k) • (A * C0 * E0)
    - (3 / 8 * l : k) • (A * C0 * D0)

def degreeZeroLambdaNoC03G5_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (4 / 27 * alpha : k) • (A * C0 ^ 2)
    - (3 / 8 * l : k) • (A * B * E0)
    - (8 / 27 * alpha : k) • (A * B * D0)
    - (35 / 216 * beta : k) • (A * B * C0)
    - (4 / 27 * alpha : k) • (A ^ 2 * E0)
    - (35 / 432 * beta : k) • (A ^ 2 * D0)

def degreeZeroLambdaNoC03G6_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 432 * delta : k) • (A ^ 2 * B)
    + (4 / 81 * epsilon : k) • A ^ 3
    + (5 / 9 : k) • E0 ^ 2
    + (3 / 4 * l : k) • (D0 * E0)
    + (2 / 9 * alpha : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (C0 * E0)

def degreeZeroLambdaNoC03G7_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (7 / 36 * beta : k) • (C0 * D0)
    + (7 / 36 * beta : k) • (B * E0)
    - (5 / 36 * delta : k) • (B * C0)
    - (1 / 9 * epsilon : k) • B ^ 2
    - (5 / 36 * delta : k) • (A * D0)
    - (2 / 9 * epsilon : k) • (A * C0)

def degreeZeroLambdaNoC03G8_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (1 / 4 * zeta : k) • (A * B)
    - (1 / 9 * eta : k) • A ^ 2
    + (2 / 3 * epsilon : k) • E0
    + (1 / 2 * zeta : k) • D0
    + (1 / 3 * eta : k) • C0
    + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoC03Polynomial610_eq_groups
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaNoC03Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      degreeZeroLambdaNoC03G1_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoC03G2_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoC03G3_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoC03G4_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoC03G5_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoC03G6_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoC03G7_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoC03G8_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaNoC03Polynomial610,
    degreeZeroLambdaNoC03G1_610,
    degreeZeroLambdaNoC03G2_610,
    degreeZeroLambdaNoC03G3_610,
    degreeZeroLambdaNoC03G4_610,
    degreeZeroLambdaNoC03G5_610,
    degreeZeroLambdaNoC03G6_610,
    degreeZeroLambdaNoC03G7_610,
    degreeZeroLambdaNoC03G8_610
    ]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoC03G1_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03G1_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE⟩, hAwt, hBwt, hEwt⟩
  simp only [degreeZeroLambdaNoC03G1_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoC03G2_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03G2_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE⟩, hAwt, hBwt, hEwt⟩
  simp only [degreeZeroLambdaNoC03G2_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoC03G3_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03G3_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE⟩, hAwt, hBwt, hEwt⟩
  simp only [degreeZeroLambdaNoC03G3_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoC03G4_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03G4_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE⟩, hAwt, hBwt, hEwt⟩
  simp only [degreeZeroLambdaNoC03G4_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoC03G5_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03G5_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE⟩, hAwt, hBwt, hEwt⟩
  simp only [degreeZeroLambdaNoC03G5_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoC03G6_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03G6_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE⟩, hAwt, hBwt, hEwt⟩
  simp only [degreeZeroLambdaNoC03G6_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoC03G7_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03G7_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE⟩, hAwt, hBwt, hEwt⟩
  simp only [degreeZeroLambdaNoC03G7_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoC03G8_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03G8_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE⟩, hAwt, hBwt, hEwt⟩
  simp only [degreeZeroLambdaNoC03G8_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

theorem degreeZeroLambdaNoC03Polynomial610_natDegree_lt_of_groups
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rw [degreeZeroLambdaNoC03Polynomial610_eq_groups]
  exact natDegree_add8_lt610
    (degreeZeroLambdaNoC03G1_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoC03G2_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoC03G3_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoC03G4_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoC03G5_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoC03G6_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoC03G7_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoC03G8_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)

def degreeZeroLambdaNoE02G1_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 6561 : k) • A ^ 6
    - (70 / 729 : k) • (A ^ 3 * B ^ 2)
    - (35 / 729 : k) • (A ^ 4 * C0)
    - (15 / 256 * l : k) • (A ^ 4 * B)
    - (8 / 729 * alpha : k) • A ^ 5
    + (5 / 243 : k) • B ^ 4
    + (20 / 81 : k) • (A * B ^ 2 * C0)

def degreeZeroLambdaNoE02G2_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (3 / 32 * l : k) • (A * B ^ 3)
    + (10 / 81 : k) • (A ^ 2 * C0 ^ 2)
    + (20 / 81 : k) • (A ^ 2 * B * D0)
    + (9 / 32 * l : k) • (A ^ 2 * B * C0)
    + (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * E0)

def degreeZeroLambdaNoE02G3_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (3 / 32 * l : k) • (A ^ 3 * D0)
    + (20 / 243 * alpha : k) • (A ^ 3 * C0)
    + (385 / 7776 * beta : k) • (A ^ 3 * B)
    - (5 / 81 : k) • C0 ^ 3
    - (10 / 27 : k) • (B * C0 * D0)
    - (3 / 16 * l : k) • (B * C0 ^ 2)

def degreeZeroLambdaNoE02G4_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * E0) -
    (3 / 16 * l : k) • (B ^ 2 * D0) -
    (4 / 27 * alpha : k) • (B ^ 2 * C0) -
    (35 / 1296 * beta : k) • B ^ 3 -
    (5 / 27 : k) • (A * D0 ^ 2) -
    (10 / 27 : k) • (A * C0 * E0)

def degreeZeroLambdaNoE02G5_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (3 / 8 * l : k) • (A * C0 * D0)
    - (4 / 27 * alpha : k) • (A * C0 ^ 2)
    - (3 / 8 * l : k) • (A * B * E0)
    - (8 / 27 * alpha : k) • (A * B * D0)
    - (35 / 216 * beta : k) • (A * B * C0)
    - (4 / 27 * alpha : k) • (A ^ 2 * E0)

def degreeZeroLambdaNoE02G6_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (35 / 432 * beta : k) • (A ^ 2 * D0)
    + (35 / 432 * delta : k) • (A ^ 2 * B)
    + (4 / 81 * epsilon : k) • A ^ 3
    + (3 / 4 * l : k) • (D0 * E0)
    + (2 / 9 * alpha : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (C0 * E0)

def degreeZeroLambdaNoE02G7_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (7 / 36 * beta : k) • (C0 * D0)
    + (7 / 36 * beta : k) • (B * E0)
    - (5 / 36 * delta : k) • (B * C0)
    - (1 / 9 * epsilon : k) • B ^ 2
    - (5 / 36 * delta : k) • (A * D0)
    - (2 / 9 * epsilon : k) • (A * C0)

def degreeZeroLambdaNoE02G8_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (1 / 4 * zeta : k) • (A * B)
    - (1 / 9 * eta : k) • A ^ 2
    + (2 / 3 * epsilon : k) • E0
    + (1 / 2 * zeta : k) • D0
    + (1 / 3 * eta : k) • C0
    + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoE02Polynomial610_eq_groups
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaNoE02Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      degreeZeroLambdaNoE02G1_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoE02G2_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoE02G3_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoE02G4_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoE02G5_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoE02G6_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoE02G7_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoE02G8_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaNoE02Polynomial610,
    degreeZeroLambdaNoE02G1_610,
    degreeZeroLambdaNoE02G2_610,
    degreeZeroLambdaNoE02G3_610,
    degreeZeroLambdaNoE02G4_610,
    degreeZeroLambdaNoE02G5_610,
    degreeZeroLambdaNoE02G6_610,
    degreeZeroLambdaNoE02G7_610,
    degreeZeroLambdaNoE02G8_610
    ]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoE02G1_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02G1_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨⟨hEpos, hA, hB, hC, hD⟩, hA0, hB0, hC0, hD0⟩
  simp only [degreeZeroLambdaNoE02G1_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoE02G2_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02G2_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨⟨hEpos, hA, hB, hC, hD⟩, hA0, hB0, hC0, hD0⟩
  simp only [degreeZeroLambdaNoE02G2_610, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoE02G3_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02G3_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨⟨hEpos, hA, hB, hC, hD⟩, hA0, hB0, hC0, hD0⟩
  simp only [degreeZeroLambdaNoE02G3_610, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoE02G4_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02G4_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨⟨hEpos, hA, hB, hC, hD⟩, hA0, hB0, hC0, hD0⟩
  simp only [degreeZeroLambdaNoE02G4_610, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoE02G5_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02G5_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨⟨hEpos, hA, hB, hC, hD⟩, hA0, hB0, hC0, hD0⟩
  simp only [degreeZeroLambdaNoE02G5_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoE02G6_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02G6_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨⟨hEpos, hA, hB, hC, hD⟩, hA0, hB0, hC0, hD0⟩
  simp only [degreeZeroLambdaNoE02G6_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoE02G7_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02G7_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨⟨hEpos, hA, hB, hC, hD⟩, hA0, hB0, hC0, hD0⟩
  simp only [degreeZeroLambdaNoE02G7_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoE02G8_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02G8_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨⟨hEpos, hA, hB, hC, hD⟩, hA0, hB0, hC0, hD0⟩
  simp only [degreeZeroLambdaNoE02G8_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

theorem degreeZeroLambdaNoE02Polynomial610_natDegree_lt_of_groups
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02Polynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rw [degreeZeroLambdaNoE02Polynomial610_eq_groups]
  exact natDegree_add8_lt610
    (degreeZeroLambdaNoE02G1_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoE02G2_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoE02G3_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoE02G4_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoE02G5_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoE02G6_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoE02G7_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoE02G8_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)

def degreeZeroLambdaNoHighBTieG1_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * C0)
    - (15 / 256 * l : k) • (A ^ 4 * B)
    - (8 / 729 * alpha : k) • A ^ 5
    + (20 / 81 : k) • (A * B ^ 2 * C0)
    + (3 / 32 * l : k) • (A * B ^ 3)
    + (10 / 81 : k) • (A ^ 2 * C0 ^ 2)

def degreeZeroLambdaNoHighBTieG2_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (20 / 81 : k) • (A ^ 2 * B * D0)
    + (9 / 32 * l : k) • (A ^ 2 * B * C0)
    + (10 / 81 * alpha : k) • (A ^ 2 * B ^ 2)
    + (20 / 243 : k) • (A ^ 3 * E0)
    + (3 / 32 * l : k) • (A ^ 3 * D0)
    + (20 / 243 * alpha : k) • (A ^ 3 * C0)

def degreeZeroLambdaNoHighBTieG3_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (385 / 7776 * beta : k) • (A ^ 3 * B)
    - (5 / 81 : k) • C0 ^ 3
    - (10 / 27 : k) • (B * C0 * D0)
    - (3 / 16 * l : k) • (B * C0 ^ 2)
    - (5 / 27 : k) • (B ^ 2 * E0)
    - (3 / 16 * l : k) • (B ^ 2 * D0)

def degreeZeroLambdaNoHighBTieG4_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (4 / 27 * alpha : k) • (B ^ 2 * C0)
    - (35 / 1296 * beta : k) • B ^ 3
    - (5 / 27 : k) • (A * D0 ^ 2)
    - (10 / 27 : k) • (A * C0 * E0)
    - (3 / 8 * l : k) • (A * C0 * D0)
    - (4 / 27 * alpha : k) • (A * C0 ^ 2)

def degreeZeroLambdaNoHighBTieG5_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (3 / 8 * l : k) • (A * B * E0)
    - (8 / 27 * alpha : k) • (A * B * D0)
    - (35 / 216 * beta : k) • (A * B * C0)
    - (4 / 27 * alpha : k) • (A ^ 2 * E0)
    - (35 / 432 * beta : k) • (A ^ 2 * D0)
    + (35 / 432 * delta : k) • (A ^ 2 * B)

def degreeZeroLambdaNoHighBTieG6_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (4 / 81 * epsilon : k) • A ^ 3
    + (5 / 9 : k) • E0 ^ 2
    + (3 / 4 * l : k) • (D0 * E0)
    + (2 / 9 * alpha : k) • D0 ^ 2
    + (4 / 9 * alpha : k) • (C0 * E0)
    + (7 / 36 * beta : k) • (C0 * D0)

def degreeZeroLambdaNoHighBTieG7_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (7 / 36 * beta : k) • (B * E0)
    - (5 / 36 * delta : k) • (B * C0)
    - (1 / 9 * epsilon : k) • B ^ 2
    - (5 / 36 * delta : k) • (A * D0)
    - (2 / 9 * epsilon : k) • (A * C0)
    - (1 / 4 * zeta : k) • (A * B)

def degreeZeroLambdaNoHighBTieG8_610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (0 : k[X]) - (1 / 9 * eta : k) • A ^ 2
    + (2 / 3 * epsilon : k) • E0
    + (1 / 2 * zeta : k) • D0
    + (1 / 3 * eta : k) • C0
    + (1 / 6 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoHighBTieRest610_eq_groups
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroLambdaNoHighBTieRest610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      degreeZeroLambdaNoHighBTieG1_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoHighBTieG2_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoHighBTieG3_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoHighBTieG4_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoHighBTieG5_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoHighBTieG6_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoHighBTieG7_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 +
      degreeZeroLambdaNoHighBTieG8_610 l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroLambdaNoHighBTieRest610,
    degreeZeroLambdaNoHighBTieG1_610,
    degreeZeroLambdaNoHighBTieG2_610,
    degreeZeroLambdaNoHighBTieG3_610,
    degreeZeroLambdaNoHighBTieG4_610,
    degreeZeroLambdaNoHighBTieG5_610,
    degreeZeroLambdaNoHighBTieG6_610,
    degreeZeroLambdaNoHighBTieG7_610,
    degreeZeroLambdaNoHighBTieG8_610
    ]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoHighBTieG1_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieG1_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  simp only [degreeZeroLambdaNoHighBTieG1_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoHighBTieG2_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieG2_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  simp only [degreeZeroLambdaNoHighBTieG2_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoHighBTieG3_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieG3_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  simp only [degreeZeroLambdaNoHighBTieG3_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoHighBTieG4_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieG4_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  simp only [degreeZeroLambdaNoHighBTieG4_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoHighBTieG5_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieG5_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  simp only [degreeZeroLambdaNoHighBTieG5_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoHighBTieG6_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieG6_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  simp only [degreeZeroLambdaNoHighBTieG6_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoHighBTieG7_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieG7_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  simp only [degreeZeroLambdaNoHighBTieG7_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroLambdaNoHighBTieG8_610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieG8_610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  simp only [degreeZeroLambdaNoHighBTieG8_610, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
    zero_pow_four, zero_pow_five]
  compute_degree
  omega

theorem degreeZeroLambdaNoHighBTieRest610_natDegree_lt_of_groups
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieRest610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rw [degreeZeroLambdaNoHighBTieRest610_eq_groups]
  exact natDegree_add8_lt610
    (degreeZeroLambdaNoHighBTieG1_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoHighBTieG2_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoHighBTieG3_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoHighBTieG4_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoHighBTieG5_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoHighBTieG6_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoHighBTieG7_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)
    (degreeZeroLambdaNoHighBTieG8_610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C0 D0 E0 hcone)

end LambdaGroups610

/-! ## Unique weighted faces of `λ` -/

section LambdaUniqueFaces610

variable {k : Type*} [Field k] [CharZero k]

theorem degreeZeroLambdaNoA6_natDegree_lt_of_A_maximal
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      6 * A.natDegree :=
  degreeZeroLambdaNoA6Polynomial610_natDegree_lt_of_groups l alpha beta
    delta epsilon zeta eta theta A B C0 D0 E0 hcone

theorem lambda_A6_impossible_of_A_maximal
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AMaximalCone610 A B C0 D0 E0)
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
    degreeZeroLambdaNoA6_natDegree_lt_of_A_maximal l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

theorem degreeZeroLambdaNoB4_natDegree_lt_of_B_leads
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      4 * B.natDegree :=
  degreeZeroLambdaNoB4Polynomial610_natDegree_lt_of_groups l alpha beta
    delta epsilon zeta eta theta A B C0 D0 E0 hcone

theorem lambda_B4_impossible_of_B_leads
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : BLeadsWeightedCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨⟨hBpos, _⟩, _⟩
    simp [hB0] at hBpos
  have hc : (5 / 243 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((5 / 243 : k) • B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoB4_natDegree_lt_of_B_leads l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_B4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hBpos, _⟩, _⟩
  omega

theorem degreeZeroLambdaNoC03_natDegree_lt_of_C0_leads
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree :=
  degreeZeroLambdaNoC03Polynomial610_natDegree_lt_of_groups l alpha beta
    delta epsilon zeta eta theta A B C0 D0 E0 hcone

theorem lambda_C03_impossible_of_C0_leads
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : C0LeadsWeightedCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨⟨hCpos, _⟩, _⟩
    simp [hC0] at hCpos
  have hc : (-(5 / 81 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 81 : k)) • C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoC03_natDegree_lt_of_C0_leads l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_C03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hCpos, _⟩, _⟩
  omega

theorem degreeZeroLambdaNoE02_natDegree_lt_of_E0_leads
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree :=
  degreeZeroLambdaNoE02Polynomial610_natDegree_lt_of_groups l alpha beta
    delta epsilon zeta eta theta A B C0 D0 E0 hcone

theorem lambda_E02_impossible_of_E0_leads
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : E0LeadsWeightedCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hE : E0 ≠ 0 := by
    intro hE0
    rcases hcone with ⟨⟨hEpos, _⟩, _⟩
    simp [hE0] at hEpos
  have hc : (5 / 9 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((5 / 9 : k) • E0 ^ 2).natDegree = 2 * E0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoE02_natDegree_lt_of_E0_leads l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_E02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hEpos, _⟩, _⟩
  omega

theorem degreeZeroLambdaNoHighBTieRest_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoHighBTieRest610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      4 * B.natDegree :=
  degreeZeroLambdaNoHighBTieRest610_natDegree_lt_of_groups l alpha beta
    delta epsilon zeta eta theta A B C0 D0 E0 hcone

theorem lambda_highBTie_impossible_of_combined_degree
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0)
    (hcomb :
      (lambdaHighBTieCombined610 A B).natDegree = 4 * B.natDegree)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hrest :=
    degreeZeroLambdaNoHighBTieRest_natDegree_lt l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_highBTie_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]), hcomb] at hdeg
  rcases hcone with ⟨⟨hBpos, _⟩, _⟩
  omega

end LambdaUniqueFaces610

/-! ## Algebra map of the polynomial first integral -/

section LambdaAlgebraMap610

variable {k : Type*} [Field k] [CharZero k]

/-- Field-level integrated `λ` (same coefficients as the polynomial
pullback). -/
def degreeZeroLambdaIntegrated610
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta delta epsilon zeta eta theta : F) : F :=
  (35 / 6561 : F) * A ^ 6 -
    (70 / 729 : F) * (A ^ 3 * B ^ 2) -
    (35 / 729 : F) * (A ^ 4 * C0) -
    (15 / 256 : F) * L * (A ^ 4 * B) -
    (8 / 729 : F) * alpha * A ^ 5 +
    (5 / 243 : F) * B ^ 4 +
    (20 / 81 : F) * (A * B ^ 2 * C0) +
    (3 / 32 : F) * L * (A * B ^ 3) +
    (10 / 81 : F) * (A ^ 2 * C0 ^ 2) +
    (20 / 81 : F) * (A ^ 2 * B * D0) +
    (9 / 32 : F) * L * (A ^ 2 * B * C0) +
    (10 / 81 : F) * alpha * (A ^ 2 * B ^ 2) +
    (20 / 243 : F) * (A ^ 3 * E0) +
    (3 / 32 : F) * L * (A ^ 3 * D0) +
    (20 / 243 : F) * alpha * (A ^ 3 * C0) +
    (385 / 7776 : F) * beta * (A ^ 3 * B) -
    (5 / 81 : F) * C0 ^ 3 -
    (10 / 27 : F) * (B * C0 * D0) -
    (3 / 16 : F) * L * (B * C0 ^ 2) -
    (5 / 27 : F) * (B ^ 2 * E0) -
    (3 / 16 : F) * L * (B ^ 2 * D0) -
    (4 / 27 : F) * alpha * (B ^ 2 * C0) -
    (35 / 1296 : F) * beta * B ^ 3 -
    (5 / 27 : F) * (A * D0 ^ 2) -
    (10 / 27 : F) * (A * C0 * E0) -
    (3 / 8 : F) * L * (A * C0 * D0) -
    (4 / 27 : F) * alpha * (A * C0 ^ 2) -
    (3 / 8 : F) * L * (A * B * E0) -
    (8 / 27 : F) * alpha * (A * B * D0) -
    (35 / 216 : F) * beta * (A * B * C0) -
    (4 / 27 : F) * alpha * (A ^ 2 * E0) -
    (35 / 432 : F) * beta * (A ^ 2 * D0) +
    (35 / 432 : F) * delta * (A ^ 2 * B) +
    (4 / 81 : F) * epsilon * A ^ 3 +
    (5 / 9 : F) * E0 ^ 2 +
    (3 / 4 : F) * L * (D0 * E0) +
    (2 / 9 : F) * alpha * D0 ^ 2 +
    (4 / 9 : F) * alpha * (C0 * E0) +
    (7 / 36 : F) * beta * (C0 * D0) +
    (7 / 36 : F) * beta * (B * E0) -
    (5 / 36 : F) * delta * (B * C0) -
    (1 / 9 : F) * epsilon * B ^ 2 -
    (5 / 36 : F) * delta * (A * D0) -
    (2 / 9 : F) * epsilon * (A * C0) -
    (1 / 4 : F) * zeta * (A * B) -
    (1 / 9 : F) * eta * A ^ 2 +
    (2 / 3 : F) * epsilon * E0 +
    (1 / 2 : F) * zeta * D0 +
    (1 / 3 : F) * eta * C0 +
    (1 / 6 : F) * theta * B

set_option maxHeartbeats 32000000 in
theorem lambdaResidual610_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta gamma delta epsilon zeta eta theta iota :
      F) :
    lambdaResidual610 L A B C0 D0 E0
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
      degreeZeroLambdaIntegrated610 L A B C0 D0 E0 alpha beta delta
        epsilon zeta eta theta := by
  obtain ⟨halpha, hbeta, _hgamma, hdelta, hepsilon, hzeta, heta, htheta,
      _hiota⟩ :=
    integratedResiduals610 L A B C0 D0 E0 alpha beta gamma delta epsilon
      zeta eta theta iota
  simp only [lambdaResidual610, degreeZeroLambdaIntegrated610]
  rw [halpha, hbeta, hdelta, hepsilon, hzeta, heta, htheta]
  ring

set_option maxHeartbeats 32000000 in
theorem algebraMap_degreeZeroLambdaPolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0) =
      degreeZeroLambdaIntegrated610 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroLambdaPolynomial610, degreeZeroLambdaIntegrated610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  try ring

/-- A polynomial whose RatFunc image has vanishing derivative is a
ground constant. -/
theorem degreeZeroLambdaPolynomial610_eq_C_of_ratFuncDeriv
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0)) =
        0) :
    ∃ c : k,
      degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C c := by
  let I :=
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
      theta A B C0 D0 E0
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa only [I] using hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

theorem degreeZeroLambdaPolynomial610_natDegree_eq_zero_of_eq_C
    {l alpha beta delta epsilon zeta eta theta : k}
    {A B C0 D0 E0 : k[X]} {c : k}
    (h :
      degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C c) :
    (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree =
      0 := by
  rw [h, natDegree_C]

end LambdaAlgebraMap610

/-! ## Source-facing constant `λ` -/

section SourceLambda610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 80000000 in
/-- The twelfth-defect clearing forces the depressed `λ` residual of a
normalized scale-zero `(6,10)` source to a ground constant. -/
theorem scaleZero_lambdaResidual_depressed_eq_C_610
    {p q : k[X][X]} {j t lambda : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * (Polynomial.C t) ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ a : k,
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
            b4 b3 b2 b1) =
        RatFunc.C a := by
  dsimp only
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
  obtain ⟨nu, hnu⟩ :=
    nonzeroFace610_twelfthDefectPowerRelation p q H (Polynomial.C t) j
      lambda hp hq hh0 hH hp6 hq10 hN hD
  have hNrat : 5 * a5 * hRF ^ 4 - 3 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow, RatFunc.algebraMap_C]
      rw [← pow_mul]
    have hh9 : algebraMap k[X] (RatFunc k) ((Polynomial.C t) ^ 9) =
        hRF ^ 9 := by
      simp only [hRF, map_pow, RatFunc.algebraMap_C]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * (Polynomial.C t) ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hF :=
    twelfthDefect_eq_clearedLambda610 hRF a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5
      b4 b3 b2 b1 (RatFunc.C lambda) hh (by simpa using hNrat)
  have hcleared :
      algebraMap k[X] (RatFunc k)
          (localClearedTwelfthDefect610 (Polynomial.C t) (p.coeff 5)
            (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
            (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda) =
        (258280326 : RatFunc k) * hRF ^ 60 *
          lambdaResidual610
            (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
            (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
            (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
            (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
            (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2
              a1)
            (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2
              a1 a0)
            (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
            (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
            (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
            (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
              b5)
            (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
              b5 b4)
            (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
              b5 b4 b3)
            (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
              b5 b4 b3 b2)
            (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
              b5 b4 b3 b2 b1) := by
    simpa [localClearedTwelfthDefect610, map_sub, map_add, map_mul,
      map_pow, map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3,
      a2, a1, a0, b8, b7, b6, b5, b4, b3, b2, b1] using hF.symm
  have hsrc :
      algebraMap k[X] (RatFunc k)
          (localClearedTwelfthDefect610 (Polynomial.C t) (p.coeff 5)
            (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
            (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C nu * (Polynomial.C t) ^ 60) := by
    rw [hnu]
  have hC :
      algebraMap k[X] (RatFunc k)
          (Polynomial.C nu * (Polynomial.C t) ^ 60) =
        RatFunc.C nu * hRF ^ 60 := by
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C]
  have hne : (258280326 : RatFunc k) ≠ 0 := by
    exact_mod_cast (by norm_num : (258280326 : ℤ) ≠ 0)
  have hhpow : hRF ^ 60 ≠ 0 := pow_ne_zero 60 hh
  have hscale : (258280326 : RatFunc k) * hRF ^ 60 ≠ 0 :=
    mul_ne_zero hne hhpow
  refine ⟨nu / 258280326, ?_⟩
  have hEq := hcleared.symm.trans (hsrc.trans hC)
  have hmul :
      (258280326 : RatFunc k) *
          lambdaResidual610
            (depressedL610 hRF (sexticDepressionR610 hRF a5) b9)
            (depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4)
            (depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3)
            (depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2)
            (depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2
              a1)
            (depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2
              a1 a0)
            (depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8)
            (depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7)
            (depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6)
            (depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
              b5)
            (depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
              b5 b4)
            (depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
              b5 b4 b3)
            (depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
              b5 b4 b3 b2)
            (depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
              b5 b4 b3 b2 b1) =
        RatFunc.C nu := by
    apply mul_right_cancel₀ hhpow
    convert hEq using 1 <;> ring
  apply mul_left_cancel₀ hne
  rw [hmul]
  simp [map_div₀, map_ofNat, mul_div_cancel₀ _ hne]

set_option maxHeartbeats 80000000 in
/-- Source-facing packet: the affine-depressed core has an integrated `λ`
polynomial equal to a ground constant. -/
theorem normalized610ScaleZero_lambdaPolynomial_eq_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota c : k) (A B C0 D0 E0 : k[X]),
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
        Polynomial.C c ∧
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
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
  have himg :
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
  have hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0)) =
        0 := by
    rw [himg, haRes]
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      ratFuncDerivation68_C aRes
  obtain ⟨c, hc⟩ :=
    degreeZeroLambdaPolynomial610_eq_C_of_ratFuncDeriv l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hderiv
  exact ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, c, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
    hder, hdeg, hc,
    degreeZeroLambdaPolynomial610_natDegree_eq_zero_of_eq_C hc⟩

end SourceLambda610

/-! ## Scale-zero exclusion -/

section Impossible610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Source-facing packet: `λ` is a ground constant on the free core, and
every unique weighted face of `λ` together with the parent unique-letter
chambers is empty.  The remaining cones are the ratio-ties of two or more
of `{6 deg A, 4 deg B, 3 deg C₀, 2 deg E₀}` with dropped load-free
combination, unique-high `D₀` with another letter nonconstant, and
unique-high `C₀`/`E₀` that do not strictly lead the four weighted faces.
Those leftover chambers are the content of
`normalized610ScaleZero_coneTerminalResidual`. -/
theorem normalized610ScaleZero_lambdaFaces_closed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota c : k) (A B C0 D0 E0 : k[X]),
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
        Polynomial.C c ∧
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      ¬ AMaximalCone610 A B C0 D0 E0 ∧
      ¬ BLeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ C0LeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ E0LeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ (HighBTieCone610 A B C0 D0 E0 ∧
          (lambdaHighBTieCombined610 A B).natDegree =
            4 * B.natDegree) ∧
      ¬ (HighBTieCone610 A B C0 D0 E0 ∧
          (highB_tieCombined610 A B).natDegree = 5 * B.natDegree) ∧
      ¬ ExtremeHighBCone610 A B C0 D0 E0 ∧
      ¬ A6BLeadsHighBCone610 A B C0 D0 E0 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ 0 < B.natDegree ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, c, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      hder, hdeg, hc, hlam⟩ :=
    normalized610ScaleZero_lambdaPolynomial_eq_C hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, c, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
    hder, hdeg, hc, hlam, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hAmax
    exact lambda_A6_impossible_of_A_maximal l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hAmax hlam
  · intro hBleads
    exact lambda_B4_impossible_of_B_leads l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hBleads hlam
  · intro hCleads
    exact lambda_C03_impossible_of_C0_leads l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hCleads hlam
  · intro hEleads
    exact lambda_E02_impossible_of_E0_leads l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hEleads hlam
  · intro hBtie
    exact lambda_highBTie_impossible_of_combined_degree l alpha beta
      delta epsilon zeta eta theta A B C0 D0 E0 hBtie.1 hBtie.2 hlam
  · intro hBtiePrim
    exact uniqueHighB_tie_impossible_of_combined_degree l alpha beta
      delta epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv
      hBtiePrim.1 hBtiePrim.2 hder
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

/-- Remaining cones after every unique weighted `λ` face and every parent
unique-letter chamber.  The unused first integral `κ` is the next
comparison for the unique-`B` tie with dropped `λ` combination (leading
coefficients of `7 A⁶ - 126 A³ B² + 27 B⁴` and `A B (7 A³ - 12 B²)`
cannot vanish together).  The unused integrals `μ` and `ο` are the next
comparison for the ratio-ties `A`–`C₀`, `A`–`E₀`, `B`–`C₀`, `B`–`E₀`,
`C₀`–`E₀` and for unique-high `D₀` with another letter nonconstant. -/
theorem normalized610ScaleZero_coneTerminalResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota c : k) (A B C0 D0 E0 : k[X]),
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
      ¬ AMaximalCone610 A B C0 D0 E0 ∧
      ¬ BLeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ C0LeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ E0LeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ (HighBTieCone610 A B C0 D0 E0 ∧
          (lambdaHighBTieCombined610 A B).natDegree =
            4 * B.natDegree) ∧
      ¬ (HighBTieCone610 A B C0 D0 E0 ∧
          (highB_tieCombined610 A B).natDegree = 5 * B.natDegree) ∧
      ¬ ExtremeHighBCone610 A B C0 D0 E0 ∧
      ¬ A6BLeadsHighBCone610 A B C0 D0 E0 := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, c, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      hder, hdeg, hc, hlam, hAmax, hBleads, hCleads, hEleads, hBtie,
      hBtiePrim, hExt, hA6B, _hDonly, _hBonly, _hconst⟩ :=
    normalized610ScaleZero_lambdaFaces_closed hsource
  exact ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, c, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
    hder, hlam, hAmax, hBleads, hCleads, hEleads, hBtie, hBtiePrim, hExt,
    hA6B⟩

/-- The scale-zero leaf is empty once the residual cones of
`normalized610ScaleZero_coneTerminalResidual` are excluded. -/
theorem normalized610ScaleZero_impossible_of_coneResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hres :
      ∀ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta
          theta iota c : k) (A B C0 D0 E0 : k[X]),
        t ≠ 0 →
        j ≠ 0 →
        j / t ≠ 0 →
        H = (Polynomial.C t) ^ 2 →
        derivative
            (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0) =
          Polynomial.C (j / t) →
        (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0).natDegree =
          0 →
        ¬ AMaximalCone610 A B C0 D0 E0 →
        ¬ BLeadsWeightedCone610 A B C0 D0 E0 →
        ¬ C0LeadsWeightedCone610 A B C0 D0 E0 →
        ¬ E0LeadsWeightedCone610 A B C0 D0 E0 →
        ¬ (HighBTieCone610 A B C0 D0 E0 ∧
            (lambdaHighBTieCombined610 A B).natDegree =
              4 * B.natDegree) →
        ¬ (HighBTieCone610 A B C0 D0 E0 ∧
            (highB_tieCombined610 A B).natDegree =
              5 * B.natDegree) →
        ¬ ExtremeHighBCone610 A B C0 D0 E0 →
        ¬ A6BLeadsHighBCone610 A B C0 D0 E0 →
          False) :
    False := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, c, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      hder, hlam, hAmax, hBleads, hCleads, hEleads, hBtie, hBtiePrim, hExt,
      hA6B⟩ :=
    normalized610ScaleZero_coneTerminalResidual hsource
  exact hres t j lambda omicron l alpha beta gamma delta epsilon zeta eta
    theta iota c A B C0 D0 E0 ht hj hjdiv hHsq hder hlam hAmax hBleads
    hCleads hEleads hBtie hBtiePrim hExt hA6B

end Impossible610

/-! ## Glue: scale-zero residual plus the aligned-nonsquare chamber -/

section Glue610

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The normalized `(6,10)` low-scale route, modulo the remaining aligned
nonsquare chamber and the leftover scale-zero residual cones.  The
aligned-square exclusion is the source-facing theorem
`planeKeller610AlignedSquareExclusion_closed`.  Scale zero is not
claimed closed. -/
theorem planeKellerNormalized610LowScaleRoute_of_scaleZero_nonsquare
    (hzero : ∀ (P Q : MvPolynomial (Fin 2) K) (H : K[X]),
      Normalized610LeadingCoreSource P Q H 0 → False)
    (hnonsquare : PlaneKeller610AlignedNonsquareExclusion (K := K)) :
    PlaneKellerNormalized610LowScaleRoute (K := K) :=
  planeKellerNormalized610LowScaleRoute_of_alignedExclusions
    hzero
    planeKeller610AlignedSquareExclusion_closed
    hnonsquare

end Glue610

#print axioms degreeZeroLambdaPolynomial610
#print axioms lambda_A6_impossible_of_A_maximal
#print axioms lambda_B4_impossible_of_B_leads
#print axioms lambda_C03_impossible_of_C0_leads
#print axioms lambda_E02_impossible_of_E0_leads
#print axioms lambda_highBTie_impossible_of_combined_degree
#print axioms scaleZero_lambdaResidual_depressed_eq_C_610
#print axioms normalized610ScaleZero_lambdaPolynomial_eq_C
#print axioms normalized610ScaleZero_lambdaFaces_closed
#print axioms normalized610ScaleZero_coneTerminalResidual
#print axioms normalized610ScaleZero_impossible_of_coneResidual
#print axioms planeKellerNormalized610LowScaleRoute_of_scaleZero_nonsquare

end Max11DegreeRoutes
