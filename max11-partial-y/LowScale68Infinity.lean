import LowScale68ScaleZero

/-! # First weighted-infinity elimination for `(6,8)`

The five lower rows of the integrated sextic/octic system have weighted
grades nine through thirteen.  Their simultaneous top coefficients form the
five scalar polynomials below.  This module proves, by explicit identities,
that their common zero set is the single depressed cubic-core family.

The two ideal-membership certificates were discovered with Singular.  They
are replayed here as ordinary polynomial identities by `ring`; no CAS result
is trusted by the theorem.
-/

noncomputable section

namespace Max11DegreeRoutes

section TopSystem68

variable {F : Type*} [Field F] [CharZero F]

def topRowFour68 (a b c d e : F) : F :=
  5 * a ^ 3 * b - 9 * a ^ 2 * d - 18 * a * b * c - 3 * b ^ 3 +
    27 * b * e + 27 * c * d

def topRowThree68 (a b c d e : F) : F :=
  4 * a ^ 5 - 30 * a ^ 3 * c - 45 * a ^ 2 * b ^ 2 + 54 * a ^ 2 * e +
    108 * a * b * d + 54 * a * c ^ 2 + 54 * b ^ 2 * c - 162 * c * e -
    81 * d ^ 2

def topRowTwo68 (a b c d e : F) : F :=
  5 * a ^ 4 * b + 2 * a ^ 3 * d - 51 * a ^ 2 * b * c - 36 * a * b ^ 3 +
    27 * a * b * e + 27 * a * c * d + 99 * b ^ 2 * d + 99 * b * c ^ 2 -
    297 * d * e

def topRowOne68 (a b c d e : F) : F :=
  10 * a ^ 4 * c + 18 * a ^ 3 * e - 9 * a ^ 2 * b * d -
    72 * a ^ 2 * c ^ 2 - 72 * a * b ^ 2 * c + 54 * a * c * e +
    27 * a * d ^ 2 - 81 * b ^ 2 * e + 243 * b * c * d + 108 * c ^ 3 -
    486 * e ^ 2

def topRowZero68 (a b c d e : F) : F :=
  5 * a ^ 4 * d + 27 * a ^ 2 * b * e - 36 * a ^ 2 * c * d -
    36 * a * b ^ 2 * d + 27 * a * d * e - 81 * b * c * e +
    108 * b * d ^ 2 + 54 * c ^ 2 * d

private def b7m4 (a b c d e : F) : F :=
  (6698 / 117117 : F) * a ^ 3 * b ^ 2 -
    (22040 / 221221 : F) * a ^ 4 * c - (1 / 3 : F) * b ^ 4 +
    (128096 / 221221 : F) * a * b ^ 2 * c +
    (155670 / 221221 : F) * a ^ 2 * c ^ 2 +
    (1460 / 13013 : F) * a ^ 2 * b * d +
    (1104 / 13013 : F) * a ^ 3 * e -
    (30360 / 20111 : F) * c ^ 3 -
    (58425 / 20111 : F) * b * c * d +
    (288 / 143 : F) * a * d ^ 2 + (111 / 65 : F) * b ^ 2 * e +
    (1253556 / 221221 : F) * a * c * e + (1134 / 65 : F) * e ^ 2

private def b7m3 (a b c d e : F) : F :=
  (145 / 10647 : F) * a * b ^ 3 + (2900 / 20111 : F) * a ^ 2 * b * c -
    (12650 / 20111 : F) * b * c ^ 2 - (123 / 1183 : F) * b ^ 2 * d +
    (655 / 1547 : F) * a * c * d + (2010 / 1183 : F) * a * b * e +
    (63 / 13 : F) * d * e

private def b7m2 (a b c d e : F) : F :=
  -(886 / 13013 : F) * a ^ 2 * b ^ 2 -
    (3480 / 221221 : F) * a ^ 3 * c +
    (41484 / 85085 : F) * b ^ 2 * c -
    (5256 / 221221 : F) * a * c ^ 2 -
    (7785 / 13013 : F) * a * b * d -
    (18792 / 13013 : F) * a ^ 2 * e - (189 / 143 : F) * d ^ 2 -
    (170424 / 85085 : F) * c * e

private def b7m1 (a b c d e : F) : F :=
  -(34 / 195 : F) * b ^ 3 + (131 / 1547 : F) * a * b * c +
    (10 / 13 : F) * a ^ 2 * d + (894 / 1547 : F) * c * d +
    (63 / 65 : F) * b * e

private def b7m0 (a b c d e : F) : F :=
  (591 / 845 : F) * a * b ^ 2 - (41232 / 20111 : F) * a ^ 2 * c -
    (1152 / 2873 : F) * c ^ 2 + (1341 / 1183 : F) * b * d -
    (34992 / 5915 : F) * a * e

set_option maxHeartbeats 2000000 in
/-- Exact certificate that the five top rows force the seventh power of the
odd cubic load into their ideal. -/
theorem topRows_b_seventhPower_certificate68 (a b c d e : F) :
    b ^ 7 =
      b7m4 a b c d e * topRowFour68 a b c d e +
      b7m3 a b c d e * topRowThree68 a b c d e +
      b7m2 a b c d e * topRowTwo68 a b c d e +
      b7m1 a b c d e * topRowOne68 a b c d e +
      b7m0 a b c d e * topRowZero68 a b c d e := by
  simp only [b7m4, b7m3, b7m2, b7m1, b7m0, topRowFour68,
    topRowThree68, topRowTwo68, topRowOne68, topRowZero68]
  ring

/-- Once the two odd loads vanish, the next two top rows force the fourth
power of the quadratic-core discrepancy. -/
theorem topRows_evenCore_fourthPower_certificate68 (a c e : F) :
    (a ^ 2 - 3 * c) ^ 4 =
      ((1 / 4 : F) * a ^ 3 - (1 / 2 : F) * a * c - (9 / 4 : F) * e) *
        topRowThree68 a 0 c 0 e +
      (-(1 / 4 : F) * a ^ 2 + (3 / 4 : F) * c) *
        topRowOne68 a 0 c 0 e := by
  simp only [topRowThree68, topRowOne68]
  ring

/-- The complete top system has exactly the depressed cubic-core shape:
the odd loads vanish and the even loads are the coefficients of
`(z² + (a/3))³`. -/
theorem topRows_cubicCore68 (a b c d e : F)
    (h4 : topRowFour68 a b c d e = 0)
    (h3 : topRowThree68 a b c d e = 0)
    (h2 : topRowTwo68 a b c d e = 0)
    (h1 : topRowOne68 a b c d e = 0)
    (h0 : topRowZero68 a b c d e = 0) :
    b = 0 ∧ d = 0 ∧ c = a ^ 2 / 3 ∧ e = a ^ 3 / 27 := by
  have hb7 := topRows_b_seventhPower_certificate68 a b c d e
  simp only [h4, h3, h2, h1, h0, mul_zero, add_zero] at hb7
  have hb : b = 0 := by
    by_contra hb0
    exact (pow_ne_zero 7 hb0) hb7
  subst b
  simp [topRowFour68, topRowThree68, topRowTwo68, topRowOne68,
    topRowZero68] at h4 h3 h2 h1 h0
  have hd : d = 0 := by
    by_contra hd0
    have hcd : d * (3 * c - a ^ 2) = 0 := by
      linear_combination (1 / 9 : F) * h4
    have hc0 : 3 * c - a ^ 2 = 0 := (mul_eq_zero.mp hcd).resolve_left hd0
    have hc : c = a ^ 2 / 3 := by
      linear_combination (1 / 3 : F) * hc0
    have hed : d * (a ^ 3 - 27 * e) = 0 := by
      rw [hc] at h2
      linear_combination (1 / 11 : F) * h2
    have he0 : a ^ 3 - 27 * e = 0 := (mul_eq_zero.mp hed).resolve_left hd0
    have he : e = a ^ 3 / 27 := by
      linear_combination (-1 / 27 : F) * he0
    have hd2 : d ^ 2 = 0 := by
      rw [hc, he] at h3
      linear_combination (-1 / 81 : F) * h3
    apply hd0
    by_contra hd0'
    exact (pow_ne_zero 2 hd0') hd2
  subst d
  have hcore4 : (a ^ 2 - 3 * c) ^ 4 = 0 := by
    linear_combination
      ((1 / 4 : F) * a ^ 3 - (1 / 2 : F) * a * c - (9 / 4 : F) * e) * h3 +
      (-(1 / 4 : F) * a ^ 2 + (3 / 4 : F) * c) * h1
  have hcore : a ^ 2 - 3 * c = 0 := by
    by_contra hcore0
    exact (pow_ne_zero 4 hcore0) hcore4
  have hc : c = a ^ 2 / 3 := by
    linear_combination (-1 / 3 : F) * hcore
  have he2 : (a ^ 3 - 27 * e) ^ 2 = 0 := by
    rw [hc] at h1
    linear_combination (-3 / 2 : F) * h1
  have he0 : a ^ 3 - 27 * e = 0 := by
    by_contra he0'
    exact (pow_ne_zero 2 he0') he2
  have he : e = a ^ 3 / 27 := by
    linear_combination (-1 / 27 : F) * he0
  exact ⟨rfl, rfl, hc, he⟩

end TopSystem68

#print axioms topRows_b_seventhPower_certificate68
#print axioms topRows_evenCore_fourthPower_certificate68
#print axioms topRows_cubicCore68

end Max11DegreeRoutes
