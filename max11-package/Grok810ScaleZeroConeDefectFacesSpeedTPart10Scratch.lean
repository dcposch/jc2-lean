import Grok810ScaleZeroConeDefectFacesSpeedTPart02Scratch
import Grok810ScaleZeroConeDefectFacesSpeedTPart03Scratch
import Grok810ScaleZeroConeDefectFacesSpeedTPart04Scratch
import Grok810ScaleZeroConeDefectFacesSpeedTPart05Scratch
import Grok810ScaleZeroConeDefectFacesSpeedTPart06Scratch
import Grok810ScaleZeroConeDefectFacesSpeedTPart07Scratch
import Grok810ScaleZeroConeDefectFacesSpeedTPart08Scratch
import Grok810ScaleZeroConeDefectFacesSpeedTPart09Scratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Unique weighted faces -/

section DefectUniqueFaces810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem xi_A7_impossible_of_A_maximal
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (-(165 / 65536 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(165 / 65536 : k)) • A ^ 7).natDegree = 7 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroXiNoA7Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroXiPolynomial810_eq_A7_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 64000000 in
theorem omicron_B5_impossible_of_B_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨⟨hBpos, _⟩, _⟩
    simp [hB0] at hBpos
  have hc : (-(21 / 4096 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(21 / 4096 : k)) • B ^ 5).natDegree = 5 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroOmicronNoB5Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroOmicronPolynomial810_eq_B5_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hBpos, _⟩, _⟩
  omega

set_option maxHeartbeats 64000000 in
theorem mu_B4_impossible_of_B_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨⟨hBpos, _⟩, _⟩
    simp [hB0] at hBpos
  have hc : (35 / 2048 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((35 / 2048 : k) • B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoB4Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_B4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hBpos, _⟩, _⟩
  omega

set_option maxHeartbeats 64000000 in
theorem mu_C03_impossible_of_C0_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨⟨hCpos, _⟩, _⟩
    simp [hC0] at hCpos
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 128 : k)) • C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoC03Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_C03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hCpos, _⟩, _⟩
  omega

set_option maxHeartbeats 64000000 in
theorem omicron_D03_impossible_of_D0_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hD : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨⟨hDpos, _⟩, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 128 : k)) • D0 ^ 3).natDegree = 3 * D0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroOmicronNoD03Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroOmicronPolynomial810_eq_D03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hDpos, _⟩, _⟩
  omega

set_option maxHeartbeats 64000000 in
theorem mu_E02_impossible_of_E0_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hE : E0 ≠ 0 := by
    intro hE0
    rcases hcone with ⟨hEpos, _⟩
    simp [hE0] at hEpos
  have hc : (5 / 32 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((5 / 32 : k) • E0 ^ 2).natDegree = 2 * E0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoE02Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_E02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, _⟩
  omega

set_option maxHeartbeats 64000000 in
theorem xi_F02_impossible_of_F0_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hF : F0 ≠ 0 := by
    intro hF0
    rcases hcone with ⟨hFpos, _⟩
    simp [hF0] at hFpos
  have hc : (5 / 32 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((5 / 32 : k) • F0 ^ 2).natDegree = 2 * F0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroXiNoF02Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroXiPolynomial810_eq_F02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hFpos, _⟩
  omega

end DefectUniqueFaces810




end Max11DegreeRoutes
