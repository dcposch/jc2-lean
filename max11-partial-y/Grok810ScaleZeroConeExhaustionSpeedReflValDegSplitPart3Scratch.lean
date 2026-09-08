import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Scratch

/-! # SPEED: theorems of `Grok810ScaleZeroConeExhaustionSpeedReflValDegScratch`, part 3 of 8, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

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

theorem muAC02Inner810_smul_eq (r s : k) :
    (385 / 65536 : k) * r ^ 6 -
        (385 / 8192 : k) * r ^ 4 * s +
          (105 / 1024 : k) * r ^ 2 * s ^ 2 -
            (5 / 128 : k) * s ^ 3 =
      (5 / 65536 : k) * muAC02Inner810 r s := by
  simp only [muAC02Inner810]
  ring
set_option maxHeartbeats 64000000 in


theorem xiAC02Combined810_coeff (A C0 : k[X]) (n : ℕ) :
    (xiAC02Combined810 A C0).coeff n =
      (-(165 / 65536 : k)) * (A ^ 7).coeff n +
        (385 / 16384 : k) * (A ^ 5 * C0).coeff n -
          (35 / 512 : k) * (A ^ 3 * C0 ^ 2).coeff n +
            (15 / 256 : k) * (A * C0 ^ 3).coeff n := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, xiAC02Combined810, coeff_add, coeff_sub, coeff_neg, coeff_smul,
    smul_eq_mul]
  ring
set_option maxHeartbeats 64000000 in


theorem xiAC02Inner810_smul_eq (r s : k) :
    (-(165 / 65536 : k)) * r ^ 7 +
        (385 / 16384 : k) * r ^ 5 * s -
          (35 / 512 : k) * r ^ 3 * s ^ 2 +
            (15 / 256 : k) * r * s ^ 3 =
      (-(5 / 65536 : k)) * xiAC02Inner810 r s := by
  simp only [xiAC02Inner810]
  ring
set_option maxHeartbeats 64000000 in


theorem muAC02_monomial_natDegree_A6 {A : k[X]} :
    (A ^ 6).natDegree = 6 * A.natDegree :=
  natDegree_pow A 6
set_option maxHeartbeats 64000000 in


theorem muAC02_monomial_natDegree_A4C
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (A ^ 4 * C0).natDegree = 6 * A.natDegree := by
  rw [natDegree_mul (pow_ne_zero 4 hA) hC, natDegree_pow, htie]
  omega
set_option maxHeartbeats 64000000 in


theorem muAC02_monomial_natDegree_A2C2
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (A ^ 2 * C0 ^ 2).natDegree = 6 * A.natDegree := by
  rw [natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hC),
    natDegree_pow, natDegree_pow, htie]
  omega
set_option maxHeartbeats 64000000 in


theorem muAC02_monomial_natDegree_C3
    {A C0 : k[X]} (htie : C0.natDegree = 2 * A.natDegree) :
    (C0 ^ 3).natDegree = 6 * A.natDegree := by
  have h1 : (C0 ^ 3).natDegree = 3 * C0.natDegree := natDegree_pow C0 3
  have h2 : 3 * C0.natDegree = 6 * A.natDegree := by omega
  exact h1.trans h2


set_option maxHeartbeats 64000000 in
theorem muAC02Combined810_natDegree_le
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (muAC02Combined810 A C0).natDegree ≤ 6 * A.natDegree := by
  have hA6 := muAC02_monomial_natDegree_A6 (A := A)
  have hA4C := muAC02_monomial_natDegree_A4C hA hC htie
  have hA2C2 := muAC02_monomial_natDegree_A2C2 hA hC htie
  have hC3 := muAC02_monomial_natDegree_C3 (A := A) htie
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  simp only [muAC02Combined810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero]
  refine (natDegree_add_le _ _).trans (max_le (hsmul _ hA6) ?_)
  refine (natDegree_add_le _ _).trans (max_le (hsmul _ hA4C) ?_)
  exact (natDegree_add_le _ _).trans (max_le (hsmul _ hA2C2) (hsmul _ hC3))


set_option maxHeartbeats 64000000 in
theorem muAC02Combined810_coeff_top
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (muAC02Combined810 A C0).coeff (6 * A.natDegree) =
      (5 / 65536 : k) *
        muAC02Inner810 A.leadingCoeff C0.leadingCoeff := by
  have hA6 := muAC02_monomial_natDegree_A6 (A := A)
  have hA4C := muAC02_monomial_natDegree_A4C hA hC htie
  have hA2C2 := muAC02_monomial_natDegree_A2C2 hA hC htie
  have hC3 := muAC02_monomial_natDegree_C3 (A := A) htie
  have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
    rw [← hA6, coeff_natDegree, leadingCoeff_pow]
  have h2 : (A ^ 4 * C0).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 4 * C0.leadingCoeff := by
    rw [← hA4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have h3 : (A ^ 2 * C0 ^ 2).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2 := by
    rw [← hA2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_pow]
  have h4 : (C0 ^ 3).coeff (6 * A.natDegree) = C0.leadingCoeff ^ 3 := by
    rw [← hC3, coeff_natDegree, leadingCoeff_pow]
  rw [muAC02Combined810_coeff, h1, h2, h3, h4]
  simpa [mul_assoc] using muAC02Inner810_smul_eq A.leadingCoeff C0.leadingCoeff
set_option maxHeartbeats 64000000 in


theorem muAC02Combined810_natDegree_eq_of_coeff_ne
    {A C0 : k[X]}
    (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree)
    (hcoeff : muAC02Inner810 A.leadingCoeff C0.leadingCoeff ≠ 0) :
    (muAC02Combined810 A C0).natDegree = 6 * A.natDegree := by
  have h5 : (5 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hle := muAC02Combined810_natDegree_le hA hC htie
  have htop :
      (muAC02Combined810 A C0).coeff (6 * A.natDegree) ≠ 0 := by
    rw [muAC02Combined810_coeff_top hA hC htie]
    exact mul_ne_zero h5 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop
set_option maxHeartbeats 64000000 in


theorem xiAC02_monomial_natDegree_A7 {A : k[X]} :
    (A ^ 7).natDegree = 7 * A.natDegree :=
  natDegree_pow A 7
set_option maxHeartbeats 64000000 in


theorem xiAC02_monomial_natDegree_A5C
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (A ^ 5 * C0).natDegree = 7 * A.natDegree := by
  rw [natDegree_mul (pow_ne_zero 5 hA) hC, natDegree_pow, htie]
  omega
set_option maxHeartbeats 64000000 in


theorem xiAC02_monomial_natDegree_A3C2
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (A ^ 3 * C0 ^ 2).natDegree = 7 * A.natDegree := by
  rw [natDegree_mul (pow_ne_zero 3 hA) (pow_ne_zero 2 hC),
    natDegree_pow, natDegree_pow, htie]
  omega


end ExhaustCombinedDeg810

end Max11DegreeRoutes

end
