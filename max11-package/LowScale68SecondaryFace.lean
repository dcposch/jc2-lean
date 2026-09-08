import LowScale68SecondaryRadius

/-! # The first `(6,8)` secondary cubic-defect face

In the chamber where twice the secondary defect gap is below the old radius,
all constant-load terms and all cubic transverse terms lie below the first
secondary face.  The five displayed forms are the resulting two invariant and
three one-form coefficients.  Their exact algebraic classification leaves
only `e = 0` and `a*b = 3*d`; no ordering on the coefficient field is used.
-/

noncomputable section

namespace Max11DegreeRoutes

section SecondaryFace68

variable {k : Type*} [Field k] [CharZero k]

def firstSecondaryFour68 (a b c d e : k) : k :=
  a * b * c - 3 * b * e - 3 * c * d

def firstSecondaryThree68 (a b c d e : k) : k :=
  a ^ 2 * b ^ 2 - 4 * a * b * d + 6 * c * e + 3 * d ^ 2

def firstSecondaryTwo68 (N G a b c d e : k) : k :=
  2 * a ^ 2 * b * c * G - 8 * a ^ 2 * b * c * N -
    9 * a * b * e * N - 6 * a * c * d * G + 24 * a * c * d * N -
    18 * d * e * G + 99 * d * e * N

def firstSecondaryOne68 (N G a b c d e : k) : k :=
  2 * a ^ 3 * b ^ 2 * G - 9 * a ^ 3 * b ^ 2 * N -
    6 * a ^ 2 * b * d * G + 24 * a ^ 2 * b * d * N +
    18 * a * c * e * G - 90 * a * c * e * N + 9 * a * d ^ 2 * N +
    27 * e ^ 2 * G - 162 * e ^ 2 * N

def firstSecondaryZero68 (a b c d e : k) : k :=
  a ^ 2 * b * c - 3 * a * c * d - 9 * d * e

/-- All five leading equations on the first secondary face. -/
structure FirstSecondaryFace68 (N G a b c d e : k) : Prop where
  four : firstSecondaryFour68 a b c d e = 0
  three : firstSecondaryThree68 a b c d e = 0
  two : firstSecondaryTwo68 N G a b c d e = 0
  one : firstSecondaryOne68 N G a b c d e = 0
  zero : firstSecondaryZero68 a b c d e = 0

set_option maxHeartbeats 1000000 in
/-- Exact algebraic classification of the small-gap secondary face.  The
hypothesis `G ≠ 6*N` is automatic from `2g<n` after casting the positive
integer radius and gap into the coefficient field. -/
theorem firstSecondaryFace68_classify
    (N G a b c d e : k) (ha : a ≠ 0) (hG : G - 6 * N ≠ 0)
    (hface : FirstSecondaryFace68 N G a b c d e) :
    e = 0 ∧ a * b = 3 * d := by
  have heFactor : e * (a * b - 3 * d) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-3 : k) ≠ 0)
    calc
      (-3 : k) * (e * (a * b - 3 * d)) =
          a * firstSecondaryFour68 a b c d e -
            firstSecondaryZero68 a b c d e := by
        simp only [firstSecondaryFour68, firstSecondaryZero68]
        ring
      _ = 0 := by rw [hface.four, hface.zero]; ring
  have he0 : e = 0 := by
    by_contra he
    have hab3 : a * b = 3 * d := sub_eq_zero.mp
      ((mul_eq_zero.mp heFactor).resolve_left he)
    have hce : c * e = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (6 : k) ≠ 0)
      calc
        (6 : k) * (c * e) = firstSecondaryThree68 a b c d e -
            (a * b - d) * (a * b - 3 * d) := by
          simp only [firstSecondaryThree68]
          ring
        _ = 0 := by rw [hface.three, hab3]; ring
    have hc0 : c = 0 := (mul_eq_zero.mp hce).resolve_right he
    have hde : d * e = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-9 : k) ≠ 0)
      calc
        (-9 : k) * (d * e) = firstSecondaryZero68 a b c d e := by
          simp [firstSecondaryZero68, hc0]
          ring
        _ = 0 := hface.zero
    have hd0 : d = 0 := (mul_eq_zero.mp hde).resolve_right he
    have hb0 : b = 0 := by
      have hab0 : a * b = 0 := by simpa [hd0] using hab3
      exact (mul_eq_zero.mp hab0).resolve_left ha
    have heFace : (27 : k) * e ^ 2 * (G - 6 * N) = 0 := by
      calc
        (27 : k) * e ^ 2 * (G - 6 * N) =
            firstSecondaryOne68 N G a b c d e := by
          simp only [firstSecondaryOne68, hb0, hc0, hd0, mul_zero,
            zero_mul, add_zero, sub_zero]
          ring
        _ = 0 := hface.one
    have heSq : e ^ 2 = 0 := by
      have hleft : (27 : k) * e ^ 2 = 0 :=
        (mul_eq_zero.mp heFace).resolve_right hG
      exact (mul_eq_zero.mp hleft).resolve_left (by norm_num)
    exact he (sq_eq_zero_iff.mp heSq)
  refine ⟨he0, ?_⟩
  by_contra hab3
  have hab3sub : a * b - 3 * d ≠ 0 := sub_ne_zero.mpr hab3
  have hcFactor : c * (a * b - 3 * d) = 0 := by
    calc
      c * (a * b - 3 * d) = firstSecondaryFour68 a b c d e := by
        simp only [firstSecondaryFour68, he0, mul_zero, sub_zero]
        ring
      _ = 0 := hface.four
  have hc0 : c = 0 := (mul_eq_zero.mp hcFactor).resolve_right hab3sub
  have hbdFactor : (a * b - d) * (a * b - 3 * d) = 0 := by
    calc
      (a * b - d) * (a * b - 3 * d) =
          firstSecondaryThree68 a b c d e := by
        simp only [firstSecondaryThree68, he0, hc0, mul_zero, add_zero]
        ring
      _ = 0 := hface.three
  have habd : a * b = d := sub_eq_zero.mp
    ((mul_eq_zero.mp hbdFactor).resolve_right hab3sub)
  have hSix : 6 * N - G ≠ 0 := by
    exact sub_ne_zero.mpr (ne_comm.mp (sub_ne_zero.mp hG))
  have hbFace : (4 : k) * a ^ 3 * b ^ 2 * (6 * N - G) = 0 := by
    calc
      (4 : k) * a ^ 3 * b ^ 2 * (6 * N - G) =
          firstSecondaryOne68 N G a b c d e := by
        simp only [firstSecondaryOne68, he0, hc0, mul_zero, zero_mul,
          add_zero, sub_zero]
        rw [← habd]
        ring
      _ = 0 := hface.one
  have habSq : (4 : k) * a ^ 3 * b ^ 2 = 0 :=
    (mul_eq_zero.mp hbFace).resolve_right hSix
  have hbSq : b ^ 2 = 0 := by
    apply (mul_eq_zero.mp habSq).resolve_left
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)
  have hb0 : b = 0 := sq_eq_zero_iff.mp hbSq
  have hd0 : d = 0 := by simpa [hb0] using habd.symm
  exact hab3 (by simp [hb0, hd0])

/-- Integer-radius form used by the polynomial boundary extraction. -/
theorem firstSecondaryFace68_classify_of_two_mul_gap_lt_radius
    (n g : ℕ) (a b c d e : k) (ha : a ≠ 0) (hsmall : 2 * g < n)
    (hface : FirstSecondaryFace68 (n : k) (g : k) a b c d e) :
    e = 0 ∧ a * b = 3 * d := by
  apply firstSecondaryFace68_classify (n : k) (g : k) a b c d e ha
  · intro hzero
    have heq : (g : k) = 6 * (n : k) := sub_eq_zero.mp hzero
    have hnat : g = 6 * n := by exact_mod_cast heq
    omega
  · exact hface

end SecondaryFace68

#print axioms firstSecondaryFace68_classify
#print axioms firstSecondaryFace68_classify_of_two_mul_gap_lt_radius

end Max11DegreeRoutes
