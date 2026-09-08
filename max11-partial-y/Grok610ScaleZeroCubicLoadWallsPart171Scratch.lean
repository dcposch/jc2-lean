import Grok610ScaleZeroCubicLoadMultiScratch
import Max11SpeedReflectDegLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000

section CubicLoadWallDets610

variable {k : Type*} [Field k] [CharZero k]

theorem n1n2_beta_column_det610 (a x beta : k) (ha : a ≠ 0)
    (hz1 : x + (7 / 6912 * beta : k) * a ^ 5 = 0)
    (hz2 : -a * x + (35 / 41472 * beta : k) * a ^ 6 = 0) :
    beta = 0 := by
  have hcomb :
      a * (x + (7 / 6912 * beta : k) * a ^ 5) +
        (-a * x + (35 / 41472 * beta : k) * a ^ 6) = 0 := by
    rw [hz1, hz2, mul_zero, add_zero]
  have hlin : (77 / 41472 * beta : k) * a ^ 6 = 0 := by
    convert hcomb using 1
    ring
  have hden : (77 / 41472 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha6 : a ^ 6 ≠ 0 := pow_ne_zero _ ha
  rcases mul_eq_zero.mp hlin with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hden h).elim
    · exact h
  · exact (ha6 h).elim

end CubicLoadWallDets610

end Max11DegreeRoutes
