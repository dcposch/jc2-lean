import LowScale68SecondarySmallGap

/-! # Algebra on the residual `(6,8)` secondary face

After `e=0` and `a*b=3*d` on the first face, translate the odd coefficient by
`D=A*B/3+d`.  In the chamber `3g<n`, the next Newton comparison has a middle
face and three endpoint faces.  This module gives the exact field-algebra
solvers for those faces; coefficient extraction and the tropical selection
are handled separately.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualFace68

variable {k : Type*} [Field k] [CharZero k]

/-- The new odd defect after the first-face relation `A*B=3*D`. -/
def secondaryDDefectPolynomial68 (A B D : k[X]) : k[X] :=
  D - (1 / 3 : k) • (A * B)

theorem secondaryDDefectPolynomial68_reconstruct (A B D : k[X]) :
    D = (1 / 3 : k) • (A * B) + secondaryDDefectPolynomial68 A B D := by
  simp only [secondaryDDefectPolynomial68]
  abel

/-- Leading equations when the two new odd defects have a common gap
`g<h<2g`. -/
structure SecondaryResidualBetweenFace68 (a b c d e : k) : Prop where
  four : b * e + c * d = 0
  three : -a * b * d + 3 * c * e = 0

set_option maxHeartbeats 1000000 in
/-- A nontrivial middle residual face forces its quadratic discriminant
relation. -/
theorem secondaryResidualBetweenFace68_classify
    (a b c d e : k) (hb : b ≠ 0) (hc : c ≠ 0)
    (hattained : d ≠ 0 ∨ e ≠ 0)
    (hface : SecondaryResidualBetweenFace68 a b c d e) :
    d ≠ 0 ∧ e ≠ 0 ∧ a * b ^ 2 + 3 * c ^ 2 = 0 := by
  have hd : d ≠ 0 := by
    intro hd0
    have hbe : b * e = 0 := by simpa [hd0] using hface.four
    have he0 : e = 0 := (mul_eq_zero.mp hbe).resolve_left hb
    exact hattained.elim (fun h => h hd0) (fun h => h he0)
  have he : e ≠ 0 := by
    intro he0
    have hcd : c * d = 0 := by simpa [he0] using hface.four
    exact hd ((mul_eq_zero.mp hcd).resolve_left hc)
  have hprod : -(a * b ^ 2 + 3 * c ^ 2) * d = 0 := by
    calc
      -(a * b ^ 2 + 3 * c ^ 2) * d =
          b * (-a * b * d + 3 * c * e) -
            3 * c * (b * e + c * d) := by ring
      _ = 0 := by rw [hface.three, hface.four]; ring
  have hdisc : a * b ^ 2 + 3 * c ^ 2 = 0 := by
    have hneg : -(a * b ^ 2 + 3 * c ^ 2) = 0 :=
      (mul_eq_zero.mp hprod).resolve_right hd
    simpa using neg_eq_zero.mp hneg
  exact ⟨hd, he, hdisc⟩

/-- Leading endpoint with the translated `D` defect at gap `2g` while the
translated constant defect is later. -/
structure SecondaryResidualDAtDoubleFace68 (a b c d : k) : Prop where
  four : -b ^ 3 + 9 * c * d = 0
  three : a * d + b * c = 0
  zero : -a * d + b * c = 0

set_option maxHeartbeats 1000000 in
theorem secondaryResidualDAtDoubleFace68_impossible
    (a b c d : k) (hb : b ≠ 0) (hc : c ≠ 0)
    (hface : SecondaryResidualDAtDoubleFace68 a b c d) : False := by
  have hbc : 2 * (b * c) = 0 := by
    calc
      2 * (b * c) = (a * d + b * c) + (-a * d + b * c) := by ring
      _ = 0 := by rw [hface.three, hface.zero]; ring
  have : b * c = 0 := (mul_eq_zero.mp hbc).resolve_left (by norm_num)
  exact (mul_ne_zero hb hc) this

/-- Leading endpoint with the translated constant defect at gap `2g` while
the translated `D` defect is later. -/
structure SecondaryResidualEAtDoubleFace68 (b c e : k) : Prop where
  four : -b ^ 2 + 9 * e = 0
  three : -b ^ 2 + 3 * e = 0

set_option maxHeartbeats 1000000 in
theorem secondaryResidualEAtDoubleFace68_impossible
    (b c e : k) (hb : b ≠ 0) (hc : c ≠ 0)
    (hface : SecondaryResidualEAtDoubleFace68 b c e) : False := by
  have he6 : 6 * e = 0 := by
    calc
      6 * e = (-b ^ 2 + 9 * e) - (-b ^ 2 + 3 * e) := by ring
      _ = 0 := by rw [hface.four, hface.three]; ring
  have he0 : e = 0 := (mul_eq_zero.mp he6).resolve_left (by norm_num)
  have hb2 : b ^ 2 = 0 := by
    have := hface.three
    rw [he0] at this
    linear_combination -this
  exact hb (sq_eq_zero_iff.mp hb2)

/-- Tied endpoint where both new defects have gap `2g`.  The final equation
is the leading part of the second one-form. -/
structure SecondaryResidualTiedDoubleFace68
    (N G a b c d e : k) : Prop where
  four : -b ^ 3 + 9 * b * e + 9 * c * d = 0
  three : -a * b * d - b ^ 2 * c + 3 * c * e = 0
  zero : -a * b * e - a * c * d + b * c ^ 2 = 0
  one : 3 * a ^ 2 * b * G * d - 10 * a ^ 2 * b * N * d +
    2 * a * b ^ 2 * N * c - 9 * a * G * c * e +
    30 * a * N * c * e + 3 * G * c ^ 3 - 12 * N * c ^ 3 = 0

set_option maxHeartbeats 2000000 in
/-- The tied endpoint forces the impossible numerical relation `G=4N` in
the chamber `3G<N`. -/
theorem secondaryResidualTiedDoubleFace68_forces_gap_eq_four_radius
    (N G a b c d e : k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hface : SecondaryResidualTiedDoubleFace68 N G a b c d e) :
    G = 4 * N := by
  have hab : a * b ^ 2 = 9 * c ^ 2 := by
    have hprod : b * (-a * b ^ 2 + 9 * c ^ 2) = 0 := by
      calc
        b * (-a * b ^ 2 + 9 * c ^ 2) =
            a * (-b ^ 3 + 9 * b * e + 9 * c * d) +
              9 * (-a * b * e - a * c * d + b * c ^ 2) := by ring
        _ = 0 := by rw [hface.four, hface.zero]; ring
    have := (mul_eq_zero.mp hprod).resolve_left hb
    linear_combination -this
  have he : e = b ^ 2 / 6 := by
    apply (eq_div_iff (by norm_num : (6 : k) ≠ 0)).2
    have hscaled : 18 * c ^ 2 * (6 * e - b ^ 2) = 0 := by
      calc
        18 * c ^ 2 * (6 * e - b ^ 2) =
            9 * c * (-a * b * d - b ^ 2 * c + 3 * c * e) +
              a * b * (-b ^ 3 + 9 * b * e + 9 * c * d) -
              (b ^ 2 - 9 * e) * (-a * b ^ 2 + 9 * c ^ 2) := by ring
        _ = 0 := by
          rw [hface.three, hface.four]
          rw [show -a * b ^ 2 + 9 * c ^ 2 = 0 by linear_combination -hab]
          ring
    have h18c2 : 18 * c ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)
    have hdiff := (mul_eq_zero.mp hscaled).resolve_left h18c2
    linear_combination hdiff
  have hd : d = -b ^ 3 / (18 * c) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num : (18 : k) ≠ 0) hc)).2
    have h := hface.four
    rw [he] at h
    field_simp at h
    have hs : b ^ 3 + 18 * c * d = 0 := by
      linear_combination (1 / 3 : k) * h
    linear_combination hs
  have hrel : -a * b ^ 2 + 9 * c ^ 2 = 0 := by linear_combination -hab
  have hfactor : a ^ 2 * b ^ 4 * (G - 4 * N) = 0 := by
    calc
      a ^ 2 * b ^ 4 * (G - 4 * N) =
          (-27 / 8 : k) * c *
            (3 * a ^ 2 * b * G * d - 10 * a ^ 2 * b * N * d +
              2 * a * b ^ 2 * N * c - 9 * a * G * c * e +
              30 * a * N * c * e + 3 * G * c ^ 3 - 12 * N * c ^ 3) +
            ((-7 * a * b ^ 2 * G + 34 * a * b ^ 2 * N +
                18 * G * c ^ 2 - 72 * N * c ^ 2) / 16) *
              (-a * b ^ 2 + 9 * c ^ 2) := by
          rw [he, hd]
          field_simp
          ring
      _ = 0 := by
        rw [hface.one, hrel]
        ring
  have hprefactor : a ^ 2 * b ^ 4 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 4 hb)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hprefactor)

/-- Integer-radius form: the tied endpoint is absent whenever `3g<n`. -/
theorem secondaryResidualTiedDoubleFace68_impossible_of_three_mul_gap_lt_radius
    (n g : ℕ) (a b c d e : k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hsmall : 3 * g < n)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hcast := secondaryResidualTiedDoubleFace68_forces_gap_eq_four_radius
    (n : k) (g : k) a b c d e ha hb hc hface
  have hnat : g = 4 * n := by exact_mod_cast hcast
  omega

end SecondaryResidualFace68

#print axioms secondaryDDefectPolynomial68_reconstruct
#print axioms secondaryResidualBetweenFace68_classify
#print axioms secondaryResidualDAtDoubleFace68_impossible
#print axioms secondaryResidualEAtDoubleFace68_impossible
#print axioms secondaryResidualTiedDoubleFace68_forces_gap_eq_four_radius
#print axioms secondaryResidualTiedDoubleFace68_impossible_of_three_mul_gap_lt_radius

end Max11DegreeRoutes
