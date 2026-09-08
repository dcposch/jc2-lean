import Grok68VanishingAChargedIntegralScratch

/-! # Order-four companion on the `q=0` vanishing-A chamber

Both research lanes (`xmodel/max11-68-vanishing-a-elimination-count` and
the identity hunt) record that matching through `k=3` leaves an open
chamber of expected dimension `19m+4`.  The next producing input is the
order-four companion, together with its remainder-cancel and load
certificate.

This file lands that producing split: on `Fce_0≠0` one has
`A_(2N-4)=0`.  The matching recurrence at `k=4` then gives
`c_Cc B_(D-4)^♭ - B_D c_(Cc-4)=0` and the companion `e/d` incidence,
so the comparison polynomials drop one further degree.

Here `B_(D-4)^♭` is `B.coeff (D-4)` when `4≤D`, and `0` when `D=3`
(the chart `m=1`, where the index `D-4` is not a natural number).
This is not a closure.  The next unused source row is `A_(2N-5)`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Coefficient helpers -/

/-! ## Order-four discriminant and I4 jets -/

/-! ## Order-four companion -/

def FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionFourthScalar68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let p := 2 * N
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d +
    (3 / 4 * epsilon : k) • B
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  (9 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) ^ 2 *
      ((p - 1 : ℕ) : k) * Fce.coeff 0 *
      ((2 : k) * A.coeff p * A.coeff (p - 4) +
        (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) + A.coeff (p - 2) ^ 2) +
    (6 : k) * ((p - 4 : ℕ) : k) ^ 2 * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
      ((p - 1 : ℕ) : k) * A.coeff (p - 4) * B.coeff D ^ 2 * d.coeff V +
    (6 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
      ((p - 1 : ℕ) : k) * (L0.coeff (2 * p - 5) + W0.coeff (2 * p - 5)) +
    ((p : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) *
      A.coeff p * (L2.coeff (p - 5) + W2.coeff (p - 5)) +
    ((p - 4 : ℕ) : k) * ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) ^ 2 *
      A.coeff (p - 1) * (L2.coeff (p - 4) + W2.coeff (p - 4)) +
    ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
      ((p - 1 : ℕ) : k) * A.coeff (p - 2) *
      (L2.coeff (p - 3) + W2.coeff (p - 3)) +
    ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) ^ 2 * ((p - 2 : ℕ) : k) *
      A.coeff (p - 3) * (L2.coeff (p - 2) + W2.coeff (p - 2)) = 0

/-! ## Remainder cancel -/

/-! ## Order-four load jets and algebra -/

def FiveToSixQZeroBBDJetFour68 (b0 b1 b2 b3 b4 d0 d1 d2 d3 d4 : k) : k :=
  b0 ^ 2 * d4 + 2 * b0 * b1 * d3 + (2 * b0 * b2 + b1 ^ 2) * d2 +
    (2 * b0 * b3 + 2 * b1 * b2) * d1 + (2 * b0 * b4 + 2 * b1 * b3 + b2 ^ 2) * d0

def FiveToSixQZeroBBDerivativeJetFour68
    (P b0 b1 b2 b3 b4 d0 d1 d2 d3 d4 : k) : k :=
  (4 / 7 * P - 4) * b0 ^ 2 * d4 + 2 * (4 / 7 * P - 3) * b0 * b1 * d3 +
    (4 / 7 * P - 2) * (2 * b0 * b2 + b1 ^ 2) * d2 +
    (4 / 7 * P - 1) * (2 * b0 * b3 + 2 * b1 * b2) * d1 +
    (4 / 7 * P) * (2 * b0 * b4 + 2 * b1 * b3 + b2 ^ 2) * d0

def FiveToSixQZeroBCEDerivativeJetFour68
    (P b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 e0 e1 e2 e3 e4 : k) : k :=
  (15 / 14 * P) * (b0 * c4 + b1 * c3 + b2 * c2 + b3 * c1 + b4 * c0) * e0 +
    (15 / 14 * P - 1) * (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0) * e1 +
    (15 / 14 * P - 2) * (b0 * c2 + b1 * c1 + b2 * c0) * e2 +
    (15 / 14 * P - 3) * (b0 * c1 + b1 * c0) * e3 +
    (15 / 14 * P - 4) * b0 * c0 * e4

def FiveToSixQZeroCCDerivativeDJetFour68
    (P c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 : k) : k :=
  (1 / 2 : k) * ((10 / 7 * P - 4) * (2 * c0 * c4 + 2 * c1 * c3 + c2 ^ 2) * d0 +
    (10 / 7 * P - 3) * (2 * c0 * c3 + 2 * c1 * c2) * d1 +
    (10 / 7 * P - 2) * (2 * c0 * c2 + c1 ^ 2) * d2 +
    (10 / 7 * P - 1) * (2 * c0 * c1) * d3 +
    (10 / 7 * P) * c0 ^ 2 * d4)

def FiveToSixQZeroRowZeroLoadJetFour68
    (P a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
      d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 : k) : k :=
  (1 / 2 : k) * a0 * ((P - 4) *
      FiveToSixQZeroBBDJetFour68 b0 b1 b2 b3 b4 d0 d1 d2 d3 d4 +
    FiveToSixQZeroBBDerivativeJetFour68 P b0 b1 b2 b3 b4 d0 d1 d2 d3 d4) +
  (1 / 2 : k) * a1 * ((P - 3) *
      FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3 +
    FiveToSixQZeroBBDerivativeJetThree68 P b0 b1 b2 b3 d0 d1 d2 d3) +
  (1 / 2 : k) * a2 * ((P - 2) *
      FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2 +
    FiveToSixQZeroBBDerivativeJetTwo68 P b0 b1 b2 d0 d1 d2) +
  (1 / 2 : k) * a3 * ((P - 1) *
      FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1 +
    FiveToSixQZeroBBDerivativeJetOne68 P b0 b1 d0 d1) +
  (1 / 2 : k) * a4 * (P * FiveToSixQZeroBBDJetZero68 b0 d0 +
    FiveToSixQZeroBBDerivativeJetZero68 P b0 d0) -
  3 * FiveToSixQZeroBCEDerivativeJetFour68 P
    b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 e0 e1 e2 e3 e4 +
  3 * FiveToSixQZeroCCDerivativeDJetFour68 P
    c0 c1 c2 c3 c4 d0 d1 d2 d3 d4


/-! ## Source-backed load, reduction, and split -/

/-! ## Matching recurrence at `k=4` -/

/-! ## Residual packet -/

/-- Residual after the order-four companion split and matching at `k=4`.
The next unused source coefficient is `A_(2N-5)`.  Not a closure. -/
def FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAOrder4CompanionResidual68
    (gamma epsilon : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAChargedIntegralResidual68
      gamma epsilon A B c d e N S ∧
    A.coeff (p - 4) = 0 ∧
    c.coeff Cc * (if 4 ≤ D then B.coeff (D - 4) else 0) -
      B.coeff D * c.coeff (Cc - 4) = 0 ∧
    B.coeff D * e.coeff (E - 4) + c.coeff Cc * d.coeff (V - 4) = 0 ∧
    (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).natDegree ≤ Cc - 5 ∧
    (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).natDegree ≤ E - 5


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes





