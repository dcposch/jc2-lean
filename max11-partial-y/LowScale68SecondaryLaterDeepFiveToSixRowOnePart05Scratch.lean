import LowScale68SecondaryLaterDeepFiveToSixRowOnePart04Scratch

/-! # The row-one face in the later-deep five-to-six chamber

This module closes the two spurious families left by the I4/I3/row-zero
classification.  The only surviving top packet is `e = 0`, `a*b = 3*d`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixRowOne68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem firstSecondary_fiveToSix_classification_with_one68
    (N G a b c d e : k)
    (ha : a ≠ 0) (hgap : G - 6 * N ≠ 0)
    (hclass : (e = 0 ∧ a * b = 3 * d) ∨
      (e = 0 ∧ c = 0 ∧ a * b = d) ∨
      (b = 0 ∧ c = 0 ∧ d = 0))
    (hone : firstSecondaryOne68 N G a b c d e = 0)
    (hattain : b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0) :
    e = 0 ∧ a * b = 3 * d := by
  rcases hclass with hmain | hmiddle | hlast
  · exact hmain
  · rcases hmiddle with ⟨he0, hc0, hab⟩
    have hfac : (4 : k) * a ^ 3 * b ^ 2 * (6 * N - G) = 0 := by
      rw [← firstSecondaryOne68_e_c_zero_d_eq_ab_fiveToSix N G a b]
      simpa only [he0, hc0, hab] using hone
    have hgap' : 6 * N - G ≠ 0 := by
      intro hzero
      apply hgap
      linear_combination -hzero
    have hb : b = 0 := by
      have hleft := (mul_eq_zero.mp hfac).resolve_right hgap'
      have hcoef : (4 : k) * a ^ 3 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)
      have hb2 : b ^ 2 = 0 :=
        (mul_eq_zero.mp hleft).resolve_left hcoef
      simpa only [pow_two, mul_self_eq_zero] using hb2
    refine ⟨he0, ?_⟩
    rw [hb, mul_zero] at hab ⊢
    rw [← hab]
    ring
  · rcases hlast with ⟨hb0, hc0, hd0⟩
    have hfac : (27 : k) * e ^ 2 * (G - 6 * N) = 0 := by
      rw [← firstSecondaryOne68_b_c_d_zero_fiveToSix N G a e]
      simpa only [hb0, hc0, hd0] using hone
    have he0 : e = 0 := by
      have hleft := (mul_eq_zero.mp hfac).resolve_right hgap
      have he2 : e ^ 2 = 0 :=
        (mul_eq_zero.mp hleft).resolve_left (by norm_num)
      simpa only [pow_two, mul_self_eq_zero] using he2
    exact False.elim (by
      rcases hattain with hb | hc | hd | he
      · exact hb hb0
      · exact hc hc0
      · exact hd hd0
      · exact he he0)

/-- Secondary attainment sharpens the surviving family to two honest
subbranches: either both `b,d` are nonzero, or both vanish and `c` is the
attained coordinate. -/
theorem firstSecondary_mainFamily_attainment_split68
    (a b c d e : k) (ha : a ≠ 0)
    (hmain : e = 0 ∧ a * b = 3 * d)
    (hattain : b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0) :
    (b ≠ 0 ∧ d ≠ 0) ∨ (b = 0 ∧ d = 0 ∧ c ≠ 0) := by
  rcases hmain with ⟨he0, hab⟩
  by_cases hb : b = 0
  · right
    have hd : d = 0 := by
      have h3d : (3 : k) * d = 0 := by
        rw [← hab, hb, mul_zero]
      exact (mul_eq_zero.mp h3d).resolve_left (by norm_num)
    refine ⟨hb, hd, ?_⟩
    rcases hattain with hb' | hc | hd' | he'
    · exact False.elim (hb' hb)
    · exact hc
    · exact False.elim (hd' hd)
    · exact False.elim (he' he0)
  · left
    refine ⟨hb, ?_⟩
    intro hd
    have hab0 : a * b = 0 := by rw [hab, hd, mul_zero]
    exact hb ((mul_eq_zero.mp hab0).resolve_left ha)

/-- The surviving relation is algebraically saturated at this face: all five
ordinary first-secondary scalar equations vanish identically on it.  Thus a
strictly lower coefficient is genuinely needed for the next reduction. -/
theorem firstSecondary_mainFamily_saturates_face68
    (N G a b c d e : k) (he0 : e = 0) (hab : a * b = 3 * d) :
    firstSecondaryFour68 a b c d e = 0 ∧
    firstSecondaryThree68 a b c d e = 0 ∧
    firstSecondaryTwo68 N G a b c d e = 0 ∧
    firstSecondaryOne68 N G a b c d e = 0 ∧
    firstSecondaryZero68 a b c d e = 0 := by
  subst e
  simp only [firstSecondaryFour68, firstSecondaryThree68,
    firstSecondaryTwo68, firstSecondaryOne68, firstSecondaryZero68,
    mul_zero, zero_mul, add_zero, sub_zero, zero_add]
  constructor
  · linear_combination c * hab
  constructor
  · linear_combination (a * b - d) * hab
  constructor
  · linear_combination (2 * a * c * G - 8 * a * c * N) * hab
  constructor
  · linear_combination (2 * a ^ 2 * b * G - 9 * a ^ 2 * b * N -
      3 * a * d * N) * hab
  · linear_combination (a * c) * hab

end LaterDeepFiveToSixRowOne68
end Max11DegreeRoutes
