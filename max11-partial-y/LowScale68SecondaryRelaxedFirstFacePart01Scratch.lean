import LowScale68SecondaryResidualExtraction

/-! # Relaxed first `(6,8)` secondary face after `l = 0`

The tracked extraction in `LowScale68SecondaryExtraction` and
`LowScale68SecondaryOneForms` uses the chamber `2g < n` because the Jacobian
load `l A^4` and the `l`-pieces of the integrated coefficients sit on or
above the first secondary face once `2g ≥ n`.  In the complementary
large-gap chamber the quartic invariant forces `l = 0`.  With that
hypothesis the same leading coefficients can be re-extracted under the
weaker old-weight cutoff `2g < 3n`, except the second one-form row, whose
`alpha A^2` load meets the face as soon as `g ≥ n`.

Exact chambers, remaining loads otherwise arbitrary:

* invariants `F₄`, `F₃` and one-forms `F₂`, `F₀`: `2g < 3n`
* one-form `F₁`: `g < n` (or `2g < 3n` after the extra vanishing `alpha = 0`)
* full five-face classification `e = 0 ∧ a*b = 3*d`: needs `F₁`
* four-equation classification without `F₁`, under `2g < 3n`:
  `(e = 0 ∧ a*b = 3*d) ∨ (e = 0 ∧ c = 0 ∧ a*b = d) ∨ (b = c = d = 0)`
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RelaxedSecondaryFace68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Abstract classification under the relaxed radius gap -/

theorem firstSecondaryFace68_gap_ne_six_radius
    (n g : ℕ) (hn : 0 < n) (hrel : 2 * g < 3 * n) :
    (g : k) - 6 * (n : k) ≠ 0 := by
  intro hzero
  have heq : (g : k) = 6 * (n : k) := sub_eq_zero.mp hzero
  have hnat : g = 6 * n := by exact_mod_cast heq
  omega

theorem firstSecondaryFace68_classify_of_two_mul_gap_lt_three_mul_radius
    (n g : ℕ) (a b c d e : k) (ha : a ≠ 0)
    (hn : 0 < n) (hrel : 2 * g < 3 * n)
    (hface : FirstSecondaryFace68 (n : k) (g : k) a b c d e) :
    e = 0 ∧ a * b = 3 * d := by
  exact firstSecondaryFace68_classify (n : k) (g : k) a b c d e ha
    (firstSecondaryFace68_gap_ne_six_radius n g hn hrel) hface

end RelaxedSecondaryFace68
end Max11DegreeRoutes
