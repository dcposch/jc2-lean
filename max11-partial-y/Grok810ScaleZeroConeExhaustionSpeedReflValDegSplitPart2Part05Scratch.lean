import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Part04Scratch

/-! # Part 5 of `Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Scratch`.

One declaration split out of `Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Scratch`; statements are byte-identical.
-/

noncomputable section

open scoped Polynomial.Bivariate
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
set_option maxRecDepth 8000000

section ExhaustCombinedDeg810

variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 64000000 in

theorem muA6Face810_natDegree
    {A : k[X]} (hA : A ≠ 0) :
    (muA6Face810 A).natDegree = 6 * A.natDegree := by
  have hc : (385 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muA6Face810]
  rw [natDegree_smul _ hc, natDegree_pow]
set_option maxHeartbeats 64000000 in

theorem muAC02Combined810_coeff (A C0 : k[X]) (n : ℕ) :
    (muAC02Combined810 A C0).coeff n =
      (385 / 65536 : k) * (A ^ 6).coeff n -
        (385 / 8192 : k) * (A ^ 4 * C0).coeff n +
          (105 / 1024 : k) * (A ^ 2 * C0 ^ 2).coeff n -
            (5 / 128 : k) * (C0 ^ 3).coeff n := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muAC02Combined810, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
  ring

end ExhaustCombinedDeg810

end Max11DegreeRoutes
