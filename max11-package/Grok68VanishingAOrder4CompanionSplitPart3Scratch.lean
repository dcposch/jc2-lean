import Grok68VanishingAOrder4CompanionSplitPart2Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 3 of 26, so that no single
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

/-- Four coefficients below a product of three separate bounds. -/
theorem coeff_mul_mul_four_below_bounds68 (p q r : k[X]) (u v w : ℕ)
    (hu : 4 ≤ u) (hv : 4 ≤ v) (hw : 4 ≤ w)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) (hr : r.natDegree ≤ w) :
    (p * q * r).coeff (u + v + w - 4) =
      p.coeff (u - 4) * q.coeff v * r.coeff w +
        p.coeff (u - 3) * q.coeff (v - 1) * r.coeff w +
        p.coeff (u - 2) * q.coeff (v - 2) * r.coeff w +
        p.coeff (u - 1) * q.coeff (v - 3) * r.coeff w +
        p.coeff u * q.coeff (v - 4) * r.coeff w +
        p.coeff (u - 3) * q.coeff v * r.coeff (w - 1) +
        p.coeff (u - 2) * q.coeff (v - 1) * r.coeff (w - 1) +
        p.coeff (u - 1) * q.coeff (v - 2) * r.coeff (w - 1) +
        p.coeff u * q.coeff (v - 3) * r.coeff (w - 1) +
        p.coeff (u - 2) * q.coeff v * r.coeff (w - 2) +
        p.coeff (u - 1) * q.coeff (v - 1) * r.coeff (w - 2) +
        p.coeff u * q.coeff (v - 2) * r.coeff (w - 2) +
        p.coeff (u - 1) * q.coeff v * r.coeff (w - 3) +
        p.coeff u * q.coeff (v - 1) * r.coeff (w - 3) +
        p.coeff u * q.coeff v * r.coeff (w - 4) := by
  have hpq : (p * q).natDegree ≤ u + v := by compute_degree; omega
  rw [coeff_mul_four_below_bounds68 (p * q) r (u + v) w (by omega) hw hpq hr,
    coeff_mul_four_below_bounds68 p q u v hu hv hp hq,
    coeff_mul_three_below_bounds68 p q u v (by omega) (by omega) hp hq,
    coeff_mul_two_below_bounds68 p q u v (by omega) (by omega) hp hq,
    coeff_mul_one_below_bounds68 p q u v (by omega) (by omega) hp hq,
    coeff_mul_at_bounds68 p q u v hp hq]
  ring


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
