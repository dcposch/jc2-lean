import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart3Scratch

/-! # SPEED: theorems of `Grok810ScaleZeroConeExhaustionSpeedReflValDegScratch`, part 4 of 8, so that no single
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

theorem xiAC02_monomial_natDegree_AC3
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (A * C0 ^ 3).natDegree = 7 * A.natDegree := by
  rw [natDegree_mul hA (pow_ne_zero 3 hC), natDegree_pow, htie]
  omega


set_option maxHeartbeats 64000000 in
theorem xiAC02Combined810_natDegree_le
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (xiAC02Combined810 A C0).natDegree ≤ 7 * A.natDegree := by
  have hA7 := xiAC02_monomial_natDegree_A7 (A := A)
  have hA5C := xiAC02_monomial_natDegree_A5C hA hC htie
  have hA3C2 := xiAC02_monomial_natDegree_A3C2 hA hC htie
  have hAC3 := xiAC02_monomial_natDegree_AC3 hA hC htie
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  simp only [xiAC02Combined810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero]
  refine (natDegree_add_le _ _).trans (max_le (hsmul _ hA7) ?_)
  refine (natDegree_add_le _ _).trans (max_le (hsmul _ hA5C) ?_)
  exact (natDegree_add_le _ _).trans (max_le (hsmul _ hA3C2) (hsmul _ hAC3))


set_option maxHeartbeats 64000000 in
theorem xiAC02Combined810_coeff_top
    {A C0 : k[X]} (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree) :
    (xiAC02Combined810 A C0).coeff (7 * A.natDegree) =
      (-(5 / 65536 : k)) *
        xiAC02Inner810 A.leadingCoeff C0.leadingCoeff := by
  have hA7 := xiAC02_monomial_natDegree_A7 (A := A)
  have hA5C := xiAC02_monomial_natDegree_A5C hA hC htie
  have hA3C2 := xiAC02_monomial_natDegree_A3C2 hA hC htie
  have hAC3 := xiAC02_monomial_natDegree_AC3 hA hC htie
  have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
    rw [← hA7, coeff_natDegree, leadingCoeff_pow]
  have h2 : (A ^ 5 * C0).coeff (7 * A.natDegree) =
      A.leadingCoeff ^ 5 * C0.leadingCoeff := by
    rw [← hA5C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have h3 : (A ^ 3 * C0 ^ 2).coeff (7 * A.natDegree) =
      A.leadingCoeff ^ 3 * C0.leadingCoeff ^ 2 := by
    rw [← hA3C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_pow]
  have h4 : (A * C0 ^ 3).coeff (7 * A.natDegree) =
      A.leadingCoeff * C0.leadingCoeff ^ 3 := by
    rw [← hAC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [xiAC02Combined810_coeff, h1, h2, h3, h4]
  simpa [mul_assoc] using xiAC02Inner810_smul_eq A.leadingCoeff C0.leadingCoeff
set_option maxHeartbeats 64000000 in


theorem xiAC02Combined810_natDegree_eq_of_coeff_ne
    {A C0 : k[X]}
    (hA : A ≠ 0) (hC : C0 ≠ 0)
    (htie : C0.natDegree = 2 * A.natDegree)
    (hcoeff : xiAC02Inner810 A.leadingCoeff C0.leadingCoeff ≠ 0) :
    (xiAC02Combined810 A C0).natDegree = 7 * A.natDegree := by
  have h5 : (-(5 / 65536 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hle := xiAC02Combined810_natDegree_le hA hC htie
  have htop :
      (xiAC02Combined810 A C0).coeff (7 * A.natDegree) ≠ 0 := by
    rw [xiAC02Combined810_coeff_top hA hC htie]
    exact mul_ne_zero h5 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop


set_option maxHeartbeats 64000000 in
theorem muAE06Combined810_natDegree_eq_of_coeff_ne
    {A E0 : k[X]}
    (hA : A ≠ 0) (hE : E0 ≠ 0)
    (htie : E0.natDegree = 3 * A.natDegree)
    (hcoeff : muAE06Inner810 A.leadingCoeff E0.leadingCoeff ≠ 0) :
    (muAE06Combined810 A E0).natDegree = 6 * A.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hA3E :
      (A ^ 3 * E0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) hE, natDegree_pow, htie]
    omega
  have hE2 : (E0 ^ 2).natDegree = 6 * A.natDegree := by
    have : (E0 ^ 2).natDegree = 2 * E0.natDegree := natDegree_pow E0 2
    have : 2 * E0.natDegree = 6 * A.natDegree := by omega
    simpa [natDegree_pow] using this
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (muAE06Combined810 A E0).natDegree ≤ 6 * A.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muAE06Combined810]
    exact (natDegree_add_le _ _).trans (max_le (hsmul _ hA6) ((natDegree_add_le _ _).trans (max_le (hsmul _ hA3E) (hsmul _ hE2))))

  have h5 : (5 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hscale :
      (muAE06Combined810 A E0).coeff (6 * A.natDegree) =
        (5 / 65536 : k) *
          muAE06Inner810 A.leadingCoeff E0.leadingCoeff := by
    have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hA6, coeff_natDegree, leadingCoeff_pow]
    have h1' : (A ^ 6).coeff (A.natDegree * 6) = A.leadingCoeff ^ 6 := by
      rw [mul_comm A.natDegree 6]; exact h1
    have h2 : (A ^ 3 * E0).coeff (6 * A.natDegree) =
        A.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [← hA3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2' : (A ^ 3 * E0).coeff (A.natDegree * 6) =
        A.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [mul_comm A.natDegree 6]; exact h2
    have h3 : (E0 ^ 2).coeff (6 * A.natDegree) = E0.leadingCoeff ^ 2 := by
      rw [← hE2, coeff_natDegree, leadingCoeff_pow]
    have h3' : (E0 ^ 2).coeff (A.natDegree * 6) = E0.leadingCoeff ^ 2 := by
      rw [mul_comm A.natDegree 6]; exact h3
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muAE06Combined810, muAE06Inner810, coeff_add, coeff_smul,
      smul_eq_mul, h1, h1', h2, h2', h3, h3']
    ring
  have htop :
      (muAE06Combined810 A E0).coeff (6 * A.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero h5 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop


set_option maxHeartbeats 64000000 in
theorem xiAE06Combined810_natDegree_eq_of_coeff_ne
    {A E0 : k[X]}
    (hA : A ≠ 0) (hE : E0 ≠ 0)
    (htie : E0.natDegree = 3 * A.natDegree)
    (hcoeff : xiAE06Inner810 A.leadingCoeff E0.leadingCoeff ≠ 0) :
    (xiAE06Combined810 A E0).natDegree = 7 * A.natDegree := by
  have hA7 : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow A 7
  have hA4E :
      (A ^ 4 * E0).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hE, natDegree_pow, htie]
    omega
  have hAE2 :
      (A * E0 ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 2 hE), natDegree_pow, htie]
    omega
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (xiAE06Combined810 A E0).natDegree ≤ 7 * A.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, xiAE06Combined810]
    exact (natDegree_add_le _ _).trans (max_le (hsmul _ hA7) ((natDegree_add_le _ _).trans (max_le (hsmul _ hA4E) (hsmul _ hAE2))))

  have h5 : (-(5 / 65536 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hscale :
      (xiAE06Combined810 A E0).coeff (7 * A.natDegree) =
        (-(5 / 65536 : k)) *
          xiAE06Inner810 A.leadingCoeff E0.leadingCoeff := by
    have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
      rw [← hA7, coeff_natDegree, leadingCoeff_pow]
    have h1' : (A ^ 7).coeff (A.natDegree * 7) = A.leadingCoeff ^ 7 := by
      rw [mul_comm A.natDegree 7]; exact h1
    have h2 : (A ^ 4 * E0).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 4 * E0.leadingCoeff := by
      rw [← hA4E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2' : (A ^ 4 * E0).coeff (A.natDegree * 7) =
        A.leadingCoeff ^ 4 * E0.leadingCoeff := by
      rw [mul_comm A.natDegree 7]; exact h2
    have h3 : (A * E0 ^ 2).coeff (7 * A.natDegree) =
        A.leadingCoeff * E0.leadingCoeff ^ 2 := by
      rw [← hAE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3' : (A * E0 ^ 2).coeff (A.natDegree * 7) =
        A.leadingCoeff * E0.leadingCoeff ^ 2 := by
      rw [mul_comm A.natDegree 7]; exact h3
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, xiAE06Combined810, xiAE06Inner810, coeff_add, coeff_sub,
      coeff_smul, smul_eq_mul, h1, h1', h2, h2', h3, h3']
    ring
  have htop :
      (xiAE06Combined810 A E0).coeff (7 * A.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero h5 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop


set_option maxHeartbeats 64000000 in
theorem muBE02Combined810_natDegree_eq_of_coeff_ne
    {B E0 : k[X]}
    (hB : B ≠ 0) (hE : E0 ≠ 0)
    (htie : E0.natDegree = 2 * B.natDegree)
    (hcoeff : muBE02Inner810 B.leadingCoeff E0.leadingCoeff ≠ 0) :
    (muBE02Combined810 B E0).natDegree = 4 * B.natDegree := by
  have hB4 : (B ^ 4).natDegree = 4 * B.natDegree := natDegree_pow B 4
  have hB2E :
      (B ^ 2 * E0).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hB) hE, natDegree_pow, htie]
    omega
  have hE2 : (E0 ^ 2).natDegree = 4 * B.natDegree := by
    have : (E0 ^ 2).natDegree = 2 * E0.natDegree := natDegree_pow E0 2
    have : 2 * E0.natDegree = 4 * B.natDegree := by omega
    simpa [natDegree_pow] using this
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (muBE02Combined810 B E0).natDegree ≤ 4 * B.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muBE02Combined810]
    exact (natDegree_add_le _ _).trans (max_le (hsmul _ hB4) ((natDegree_add_le _ _).trans (max_le (hsmul _ hB2E) (hsmul _ hE2))))

  have h5 : (5 / 2048 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hscale :
      (muBE02Combined810 B E0).coeff (4 * B.natDegree) =
        (5 / 2048 : k) *
          muBE02Inner810 B.leadingCoeff E0.leadingCoeff := by
    have h1 : (B ^ 4).coeff (4 * B.natDegree) = B.leadingCoeff ^ 4 := by
      rw [← hB4, coeff_natDegree, leadingCoeff_pow]
    have h1' : (B ^ 4).coeff (B.natDegree * 4) = B.leadingCoeff ^ 4 := by
      rw [mul_comm B.natDegree 4]; exact h1
    have h2 : (B ^ 2 * E0).coeff (4 * B.natDegree) =
        B.leadingCoeff ^ 2 * E0.leadingCoeff := by
      rw [← hB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2' : (B ^ 2 * E0).coeff (B.natDegree * 4) =
        B.leadingCoeff ^ 2 * E0.leadingCoeff := by
      rw [mul_comm B.natDegree 4]; exact h2
    have h3 : (E0 ^ 2).coeff (4 * B.natDegree) = E0.leadingCoeff ^ 2 := by
      rw [← hE2, coeff_natDegree, leadingCoeff_pow]
    have h3' : (E0 ^ 2).coeff (B.natDegree * 4) = E0.leadingCoeff ^ 2 := by
      rw [mul_comm B.natDegree 4]; exact h3
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muBE02Combined810, muBE02Inner810, coeff_add, coeff_sub,
      coeff_smul, smul_eq_mul, h1, h1', h2, h2', h3, h3']
    ring
  have htop :
      (muBE02Combined810 B E0).coeff (4 * B.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero h5 hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop


set_option maxHeartbeats 64000000 in
theorem omicronBE02Combined810_natDegree_eq_of_coeff_ne
    {B E0 : k[X]}
    (hB : B ≠ 0) (hE : E0 ≠ 0)
    (htie : E0.natDegree = 2 * B.natDegree)
    (hcoeff : omicronBE02Inner810 B.leadingCoeff E0.leadingCoeff ≠ 0) :
    (omicronBE02Combined810 B E0).natDegree = 5 * B.natDegree := by
  have hB5 : (B ^ 5).natDegree = 5 * B.natDegree := natDegree_pow B 5
  have hB3E :
      (B ^ 3 * E0).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hB) hE, natDegree_pow, htie]
    omega
  have hBE2 :
      (B * E0 ^ 2).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hB (pow_ne_zero 2 hE), natDegree_pow, htie]
    omega
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (omicronBE02Combined810 B E0).natDegree ≤ 5 * B.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, omicronBE02Combined810]
    exact (natDegree_add_le _ _).trans (max_le (hsmul _ hB5) ((natDegree_add_le _ _).trans (max_le (hsmul _ hB3E) (hsmul _ hBE2))))

  have hsc : (-(1 / 4096 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hscale :
      (omicronBE02Combined810 B E0).coeff (5 * B.natDegree) =
        (-(1 / 4096 : k)) *
          omicronBE02Inner810 B.leadingCoeff E0.leadingCoeff := by
    have h1 : (B ^ 5).coeff (5 * B.natDegree) = B.leadingCoeff ^ 5 := by
      rw [← hB5, coeff_natDegree, leadingCoeff_pow]
    have h1' : (B ^ 5).coeff (B.natDegree * 5) = B.leadingCoeff ^ 5 := by
      rw [mul_comm B.natDegree 5]; exact h1
    have h2 : (B ^ 3 * E0).coeff (5 * B.natDegree) =
        B.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [← hB3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2' : (B ^ 3 * E0).coeff (B.natDegree * 5) =
        B.leadingCoeff ^ 3 * E0.leadingCoeff := by
      rw [mul_comm B.natDegree 5]; exact h2
    have h3 : (B * E0 ^ 2).coeff (5 * B.natDegree) =
        B.leadingCoeff * E0.leadingCoeff ^ 2 := by
      rw [← hBE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h3' : (B * E0 ^ 2).coeff (B.natDegree * 5) =
        B.leadingCoeff * E0.leadingCoeff ^ 2 := by
      rw [mul_comm B.natDegree 5]; exact h3
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, omicronBE02Combined810, omicronBE02Inner810, coeff_add,
      coeff_sub, coeff_smul, smul_eq_mul, h1, h1', h2, h2', h3, h3']
    ring
  have htop :
      (omicronBE02Combined810 B E0).coeff (5 * B.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero hsc hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop


set_option maxHeartbeats 64000000 in
theorem muAD05Combined810_natDegree_eq_of_coeff_ne
    {A D0 : k[X]}
    (hA : A ≠ 0) (hD : D0 ≠ 0)
    (htie : 5 * A.natDegree = 2 * D0.natDegree)
    (hcoeff : muAD05Inner810 A.leadingCoeff D0.leadingCoeff ≠ 0) :
    (muAD05Combined810 A D0).natDegree = 6 * A.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hAD2 :
      (A * D0 ^ 2).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 2 hD), natDegree_pow]
    omega
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (muAD05Combined810 A D0).natDegree ≤ 6 * A.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muAD05Combined810]
    exact (natDegree_add_le _ _).trans (max_le (hsmul _ hA6) (hsmul _ hAD2))

  have hsc : (1 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hscale :
      (muAD05Combined810 A D0).coeff (6 * A.natDegree) =
        (1 / 65536 : k) *
          muAD05Inner810 A.leadingCoeff D0.leadingCoeff := by
    have h1 : (A ^ 6).coeff (6 * A.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hA6, coeff_natDegree, leadingCoeff_pow]
    have h1' : (A ^ 6).coeff (A.natDegree * 6) = A.leadingCoeff ^ 6 := by
      rw [mul_comm A.natDegree 6]; exact h1
    have h2 : (A * D0 ^ 2).coeff (6 * A.natDegree) =
        A.leadingCoeff * D0.leadingCoeff ^ 2 := by
      rw [← hAD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    have h2' : (A * D0 ^ 2).coeff (A.natDegree * 6) =
        A.leadingCoeff * D0.leadingCoeff ^ 2 := by
      rw [mul_comm A.natDegree 6]; exact h2
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muAD05Combined810, muAD05Inner810, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul, h1, h1', h2, h2']
    ring
  have htop :
      (muAD05Combined810 A D0).coeff (6 * A.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero hsc hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop


set_option maxHeartbeats 64000000 in
theorem xiAD05Combined810_natDegree_eq_of_coeff_ne
    {A D0 : k[X]}
    (hA : A ≠ 0) (hD : D0 ≠ 0)
    (htie : 5 * A.natDegree = 2 * D0.natDegree)
    (hcoeff : xiAD05Inner810 A.leadingCoeff D0.leadingCoeff ≠ 0) :
    (xiAD05Combined810 A D0).natDegree = 7 * A.natDegree := by
  have hA7 : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow A 7
  have hA2D2 :
      (A ^ 2 * D0 ^ 2).natDegree = 7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hD),
      natDegree_pow, natDegree_pow]
    omega
  have hsmul (c : k) {p : k[X]} {n : ℕ} (hp : p.natDegree = n) :
      (c • p).natDegree ≤ n :=
    (natDegree_smul_le810 c p).trans hp.le
  have hle :
      (xiAD05Combined810 A D0).natDegree ≤ 7 * A.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, xiAD05Combined810]
    exact (natDegree_add_le _ _).trans (max_le (hsmul _ hA7) (hsmul _ hA2D2))
  have hsc : (1 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hscale :
      (xiAD05Combined810 A D0).coeff (7 * A.natDegree) =
        (1 / 65536 : k) *
          xiAD05Inner810 A.leadingCoeff D0.leadingCoeff := by
    have h1 : (A ^ 7).coeff (7 * A.natDegree) = A.leadingCoeff ^ 7 := by
      rw [← hA7, coeff_natDegree, leadingCoeff_pow]
    have h1' : (A ^ 7).coeff (A.natDegree * 7) = A.leadingCoeff ^ 7 := by
      rw [mul_comm A.natDegree 7]; exact h1
    have h2 : (A ^ 2 * D0 ^ 2).coeff (7 * A.natDegree) =
        A.leadingCoeff ^ 2 * D0.leadingCoeff ^ 2 := by
      rw [← hA2D2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h2' : (A ^ 2 * D0 ^ 2).coeff (A.natDegree * 7) =
        A.leadingCoeff ^ 2 * D0.leadingCoeff ^ 2 := by
      rw [mul_comm A.natDegree 7]; exact h2
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, xiAD05Combined810, xiAD05Inner810, coeff_add, coeff_smul,
      smul_eq_mul, h1, h1', h2, h2']
    ring
  have htop :
      (xiAD05Combined810 A D0).coeff (7 * A.natDegree) ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero hsc hcoeff
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop


end ExhaustCombinedDeg810

section ExhaustImpossible810

variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 64000000 in

theorem mu_A6_impossible_of_mixedB
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedBCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hlead := muA6Face810_natDegree hA
  have hrest :=
    degreeZeroMuNoA6_natDegree_lt_of_mixedB l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega
set_option maxHeartbeats 64000000 in


theorem mu_A6_impossible_of_A6B
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6BLeadsOmicronCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA6B :
      A6LeadsMuMixedBCone810 A B C0 D0 E0 F0 G0 := by
    rcases hcone with ⟨hApos, hBpos, _, h3, hC, hD, hE, hF, hG⟩
    exact ⟨hApos, hBpos, h3, hC, hD, hE, hF, hG⟩
  exact mu_A6_impossible_of_mixedB l beta gamma delta epsilon zeta eta
    theta A B C0 D0 E0 F0 G0 hA6B hdeg
set_option maxHeartbeats 64000000 in


theorem mu_A6_impossible_of_mixedC0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedC0Cone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hlead := muA6Face810_natDegree hA
  have hrest :=
    degreeZeroMuNoA6_natDegree_lt_of_mixedC0 l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega


end ExhaustImpossible810

end Max11DegreeRoutes

end
