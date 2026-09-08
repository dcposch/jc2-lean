import Grok68VanishingAOrder4CompanionSplitPart10Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 11 of 26, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact polynomial certificate for the fourth load. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_algebra68
    (P a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
      d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 : k)
    (hb0 : b0 ≠ 0)
    (hD0 : a0 * b0 ^ 2 + 3 * c0 ^ 2 = 0)
    (hD1 : a1 * b0 ^ 2 + 2 * a0 * b0 * b1 + 6 * c0 * c1 = 0)
    (hD2 : a2 * b0 ^ 2 + 2 * a1 * b0 * b1 + a0 * (2 * b0 * b2 + b1 ^ 2) +
      3 * (2 * c0 * c2 + c1 ^ 2) = 0)
    (hD3 : a3 * b0 ^ 2 + 2 * a2 * b0 * b1 + a1 * (2 * b0 * b2 + b1 ^ 2) +
      a0 * (2 * b0 * b3 + 2 * b1 * b2) + 6 * (c0 * c3 + c1 * c2) = 0)
    (hD4 : a4 * b0 ^ 2 + 2 * a3 * b0 * b1 + a2 * (2 * b0 * b2 + b1 ^ 2) +
      a1 * (2 * b0 * b3 + 2 * b1 * b2) +
      a0 * (2 * b0 * b4 + 2 * b1 * b3 + b2 ^ 2) +
      6 * (c0 * c4 + c1 * c3) + 3 * c2 ^ 2 = 0)
    (hI40 : b0 * e0 + c0 * d0 = 0)
    (hI41 : b1 * e0 + b0 * e1 + c1 * d0 + c0 * d1 = 0)
    (hI42 : b2 * e0 + b1 * e1 + b0 * e2 + c2 * d0 + c1 * d1 + c0 * d2 = 0)
    (hI43 : b3 * e0 + b2 * e1 + b1 * e2 + b0 * e3 +
      c3 * d0 + c2 * d1 + c1 * d2 + c0 * d3 = 0)
    (hI44 : b4 * e0 + b3 * e1 + b2 * e2 + b1 * e3 + b0 * e4 +
      c4 * d0 + c3 * d1 + c2 * d2 + c1 * d3 + c0 * d4 = 0) :
    6 * (P - 4) ^ 2 * (P - 3) * (P - 2) * (P - 1) * a4 * b0 ^ 2 * d0 +
      6 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        FiveToSixQZeroRowZeroLoadJetFour68 P
          a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
          d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 +
      P * (P - 3) * (P - 2) * (P - 1) * a0 * (6 * (P - 4) *
        FiveToSixQZeroBBDJetFour68 b0 b1 b2 b3 b4 d0 d1 d2 d3 d4) +
      (P - 4) * (P - 2) * (P - 1) ^ 2 * a1 * (6 * (P - 3) *
        FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3) +
      (P - 4) * (P - 3) * (P - 2) * (P - 1) * a2 * (6 * (P - 2) *
        FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2) +
      (P - 4) * (P - 3) ^ 2 * (P - 2) * a3 * (6 * (P - 1) *
        FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1) = 0 := by
  have hmul : b0 ^ 4 * (
      6 * (P - 4) ^ 2 * (P - 3) * (P - 2) * (P - 1) * a4 * b0 ^ 2 * d0 +
        6 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
          FiveToSixQZeroRowZeroLoadJetFour68 P
            a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
            d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 +
        P * (P - 3) * (P - 2) * (P - 1) * a0 * (6 * (P - 4) *
          FiveToSixQZeroBBDJetFour68 b0 b1 b2 b3 b4 d0 d1 d2 d3 d4) +
        (P - 4) * (P - 2) * (P - 1) ^ 2 * a1 * (6 * (P - 3) *
          FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3) +
        (P - 4) * (P - 3) * (P - 2) * (P - 1) * a2 * (6 * (P - 2) *
          FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2) +
        (P - 4) * (P - 3) ^ 2 * (P - 2) * a3 * (6 * (P - 1) *
          FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1)) = 0 := by
    dsimp only [FiveToSixQZeroRowZeroLoadJetFour68,
      FiveToSixQZeroBBDJetZero68, FiveToSixQZeroBBDJetOne68,
      FiveToSixQZeroBBDJetTwo68, FiveToSixQZeroBBDJetThree68,
      FiveToSixQZeroBBDJetFour68,
      FiveToSixQZeroBBDerivativeJetZero68,
      FiveToSixQZeroBBDerivativeJetOne68,
      FiveToSixQZeroBBDerivativeJetTwo68,
      FiveToSixQZeroBBDerivativeJetThree68,
      FiveToSixQZeroBBDerivativeJetFour68,
      FiveToSixQZeroBCEDerivativeJetFour68,
      FiveToSixQZeroCCDerivativeDJetFour68]
    linear_combination
      (3 / 7 : k) * b0 ^ 4 * d0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        (25 * P - 56) * hD4 +
      (3 / 7 : k) * b0 ^ 3 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 * d1 + 14 * b1 * d0) * hD3 +
      (3 / 7 : k) * b0 ^ 2 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 ^ 2 * d2 + 14 * b0 * b1 * d1 +
          28 * b0 * b2 * d0 - 14 * b1 ^ 2 * d0) * hD2 +
      (3 / 7 : k) * b0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 ^ 3 * d3 + 14 * b0 ^ 2 * b1 * d2 +
          28 * b0 ^ 2 * b2 * d1 + 42 * b0 ^ 2 * b3 * d0 -
          14 * b0 * b1 ^ 2 * d1 - 42 * b0 * b1 * b2 * d0 +
          14 * b1 ^ 3 * d0) * hD1 +
      (3 / 7 : k) * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 ^ 4 * d4 + 14 * b0 ^ 3 * b1 * d3 +
          28 * b0 ^ 3 * b2 * d2 + 42 * b0 ^ 3 * b3 * d1 +
          56 * b0 ^ 3 * b4 * d0 - 14 * b0 ^ 2 * b1 ^ 2 * d2 -
          42 * b0 ^ 2 * b1 * b2 * d1 - 56 * b0 ^ 2 * b1 * b3 * d0 -
          28 * b0 ^ 2 * b2 ^ 2 * d0 + 14 * b0 * b1 ^ 3 * d1 +
          56 * b0 * b1 ^ 2 * b2 * d0 - 14 * b1 ^ 4 * d0) * hD0 -
      (9 / 7 : k) * b0 ^ 4 * c0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        (15 * P - 56) * hI44 -
      (9 / 7 : k) * b0 ^ 3 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((15 * P - 42) * b0 * c1 + 14 * b1 * c0) * hI43 -
      (9 / 7 : k) * b0 ^ 2 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((15 * P - 28) * b0 ^ 2 * c2 + 14 * b0 * b1 * c1 +
          28 * b0 * b2 * c0 - 14 * b1 ^ 2 * c0) * hI42 -
      (9 / 7 : k) * b0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((15 * P - 14) * b0 ^ 3 * c3 + 14 * b0 ^ 2 * b1 * c2 +
          28 * b0 ^ 2 * b2 * c1 + 42 * b0 ^ 2 * b3 * c0 -
          14 * b0 * b1 ^ 2 * c1 - 42 * b0 * b1 * b2 * c0 +
          14 * b1 ^ 3 * c0) * hI41 -
      (9 / 7 : k) * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        (15 * P * b0 ^ 4 * c4 + 14 * b0 ^ 3 * b1 * c3 +
          28 * b0 ^ 3 * b2 * c2 + 42 * b0 ^ 3 * b3 * c1 +
          56 * b0 ^ 3 * b4 * c0 - 14 * b0 ^ 2 * b1 ^ 2 * c2 -
          42 * b0 ^ 2 * b1 * b2 * c1 - 56 * b0 ^ 2 * b1 * b3 * c0 -
          28 * b0 ^ 2 * b2 ^ 2 * c0 + 14 * b0 * b1 ^ 3 * c1 +
          56 * b0 * b1 ^ 2 * b2 * c0 - 14 * b1 ^ 4 * c0) * hI40
  have hb04 : b0 ^ 4 ≠ 0 := pow_ne_zero 4 hb0
  exact (mul_eq_zero.mp hmul).resolve_left hb04


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
