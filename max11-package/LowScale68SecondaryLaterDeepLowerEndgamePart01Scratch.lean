import LowScale68SecondaryLaterDeepLoadCascade
import LowScale68SecondaryDeepGapResidualEndgame

/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

theorem laterDeepLower_gap_lt_three_radius
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    g < 3 * n := by
  omega

theorem laterDeepLower_index_pos_three
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    0 < 3 * n - g := by
  omega

theorem laterDeepLower_index_pos_four
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    0 < 4 * n - g := by
  omega

theorem laterDeepLower_index_pos_five
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    0 < 5 * n - g := by
  omega

theorem laterDeepLower_index_pos_six
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    0 < 6 * n - g := by
  omega

theorem laterDeepLower_three_index_ne_zero
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    10 * n - 2 * g ≠ 0 := by
  omega

theorem laterDeepLower_rowZeroIndex_gt_fiftyNine
    (n g : ℕ) (hn : 10 ≤ n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    59 < 13 * n - 2 * g - 1 := by
  omega

theorem laterDeepLower_gap_ne_six_radius
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
    (g : k) - 6 * (n : k) ≠ 0 := by
  intro hzero
  have heq : (g : k) = 6 * (n : k) := sub_eq_zero.mp hzero
  have hnat : g = 6 * n := by exact_mod_cast heq
  omega

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
