import LowScale68SecondaryOneForms

/-! # Abstract mixed first face on the `(6,8)` wall `2g = n`

On the scale-zero equality wall `2g = n`, the homogeneous deficit-two face
collides with the Jacobian loads `l A^4` (quartic invariant, index `8n`)
and `l A^5` (row two at `10n-1`, row zero at `12n-1`).  Section 3.3 of
`Grok68LargeGapPlanScratch.md` records the five mixed leading scalars.
This module classifies that finite scalar system over a characteristic-zero
field: if `a ≠ 0` and `N ≠ 0`, then `l = 0`, `e = 0` and `a*b = 3*d`.

The argument is a finite `ring` certificate, not a trusted Groebner basis.
Row one is load-free on this wall and is the ordinary
`firstSecondaryOne68` at `G = N/2`.  I3 is likewise unchanged.
-/

noncomputable section

namespace Max11DegreeRoutes

section FirstLoadWallFace68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-! ## Cleared mixed numerators

These are the displayed leading scalars of §3.3 after dropping the
nonzero prefactors `1/1728`, `-N/324`, and `a N/1944`.  Vanishing of a
numerator is equivalent to vanishing of the corresponding scaled scalar
once `N ≠ 0` and (for the terminal row) `a ≠ 0`. -/

/-- Mixed I4 numerator at index `8n`:
`35 l a^4 - 1536 (a b c - 3 b e - 3 c d)`. -/
def firstLoadWallFourNumerator68 (a b c d e l : k) : k :=
  (35 : k) * l * a ^ 4 - (1536 : k) * firstSecondaryFour68 a b c d e

/-- Mixed row-two numerator at index `10n-1`, after dropping `-N/324`. -/
def firstLoadWallTwoNumerator68 (a b c d e l : k) : k :=
  -(35 : k) * l * a ^ 5 + (672 : k) * a ^ 2 * b * c +
    (864 : k) * a * b * e - (2016 : k) * a * c * d -
    (8640 : k) * d * e

/-- Mixed row-zero numerator at index `12n-1`, after dropping `a N/1944`. -/
def firstLoadWallZeroNumerator68 (a b c d e l : k) : k :=
  (35 : k) * l * a ^ 5 + (192 : k) * a ^ 2 * b * c -
    (576 : k) * a * c * d - (1728 : k) * d * e

/-- Plan §3.3 mixed I4 scalar `(35 l a^4 - 1536 a b c + 4608 b e + 4608 c d)/1728`. -/
def firstLoadWallFourScalar68 (a b c d e l : k) : k :=
  ((35 : k) * l * a ^ 4 - (1536 : k) * a * b * c +
    (4608 : k) * b * e + (4608 : k) * c * d) / (1728 : k)

/-- Plan §3.3 mixed row-two scalar. -/
def firstLoadWallTwoScalar68 (N a b c d e l : k) : k :=
  -N * (-(35 : k) * l * a ^ 5 + (672 : k) * a ^ 2 * b * c +
    (864 : k) * a * b * e - (2016 : k) * a * c * d -
    (8640 : k) * d * e) / (324 : k)

/-- Plan §3.3 mixed row-zero scalar. -/
def firstLoadWallZeroScalar68 (N a b c d e l : k) : k :=
  a * N * ((35 : k) * l * a ^ 5 + (192 : k) * a ^ 2 * b * c -
    (576 : k) * a * c * d - (1728 : k) * d * e) / (1944 : k)

/-- All five mixed leading equations on the wall `2G = N`. -/
structure FirstLoadWallFace68 (N G a b c d e l : k) : Prop where
  four : firstLoadWallFourNumerator68 a b c d e l = 0
  three : firstSecondaryThree68 a b c d e = 0
  two : firstLoadWallTwoNumerator68 a b c d e l = 0
  one : firstSecondaryOne68 N G a b c d e = 0
  zero : firstLoadWallZeroNumerator68 a b c d e l = 0

/-! ## Polynomial identities (the Groebner certificate) -/

theorem firstLoadWallFourScalar68_eq_numerator
    (a b c d e l : k) :
    firstLoadWallFourScalar68 a b c d e l =
      firstLoadWallFourNumerator68 a b c d e l / (1728 : k) := by
  simp only [firstLoadWallFourScalar68, firstLoadWallFourNumerator68,
    firstSecondaryFour68]
  ring

theorem firstLoadWallTwoScalar68_eq_numerator
    (N a b c d e l : k) :
    firstLoadWallTwoScalar68 N a b c d e l =
      -N * firstLoadWallTwoNumerator68 a b c d e l / (324 : k) := by
  simp only [firstLoadWallTwoScalar68, firstLoadWallTwoNumerator68]

theorem firstLoadWallZeroScalar68_eq_numerator
    (N a b c d e l : k) :
    firstLoadWallZeroScalar68 N a b c d e l =
      a * N * firstLoadWallZeroNumerator68 a b c d e l / (1944 : k) := by
  simp only [firstLoadWallZeroScalar68, firstLoadWallZeroNumerator68]

theorem firstLoadWallFourScalar68_eq_F4_load
    (a b c d e l : k) :
    firstLoadWallFourScalar68 a b c d e l =
      (35 / 1728 : k) * l * a ^ 4 +
        (-8 / 9 : k) * firstSecondaryFour68 a b c d e := by
  simp only [firstLoadWallFourScalar68, firstSecondaryFour68]
  ring

theorem firstLoadWallTwoScalar68_eq_F2_load
    (N a b c d e l : k) :
    firstLoadWallTwoScalar68 N a b c d e l =
      (8 / 27 : k) * firstSecondaryTwo68 N (N / 2) a b c d e +
        (35 / 324 : k) * N * l * a ^ 5 := by
  simp only [firstLoadWallTwoScalar68, firstSecondaryTwo68]
  ring

theorem firstLoadWallZeroScalar68_eq_F0_load
    (N a b c d e l : k) :
    firstLoadWallZeroScalar68 N a b c d e l =
      (8 / 81 : k) * N * a * firstSecondaryZero68 a b c d e +
        (35 / 1944 : k) * N * l * a ^ 6 := by
  simp only [firstLoadWallZeroScalar68, firstSecondaryZero68]
  ring

/-- I4/I0 combination that eliminates `l`. -/
theorem firstLoadWall_four_zero_combination
    (a b c d e l : k) :
    (-576 : k) *
        (3 * a ^ 2 * b * c - 8 * a * b * e - 9 * a * c * d - 3 * d * e) =
      a * firstLoadWallFourNumerator68 a b c d e l -
        firstLoadWallZeroNumerator68 a b c d e l := by
  simp only [firstLoadWallFourNumerator68, firstLoadWallZeroNumerator68,
    firstSecondaryFour68]
  ring

/-- I4/row-two combination that eliminates `l`. -/
theorem firstLoadWall_four_two_combination
    (a b c d e l : k) :
    (-288 : k) *
        (3 * a ^ 2 * b * c - 19 * a * b * e - 9 * a * c * d + 30 * d * e) =
      a * firstLoadWallFourNumerator68 a b c d e l +
        firstLoadWallTwoNumerator68 a b c d e l := by
  simp only [firstLoadWallFourNumerator68, firstLoadWallTwoNumerator68,
    firstSecondaryFour68]
  ring

/-- Difference of the two `l`-free relations factors as `11 e (a b - 3 d)`. -/
theorem firstLoadWall_e_factor_identity (a b c d e : k) :
    (3 * a ^ 2 * b * c - 8 * a * b * e - 9 * a * c * d - 3 * d * e) -
      (3 * a ^ 2 * b * c - 19 * a * b * e - 9 * a * c * d + 30 * d * e) =
      (11 : k) * (e * (a * b - 3 * d)) := by
  ring

theorem firstSecondaryThree68_factor (a b c d e : k) :
    firstSecondaryThree68 a b c d e =
      (a * b - d) * (a * b - 3 * d) + 6 * c * e := by
  simp only [firstSecondaryThree68]
  ring

theorem firstSecondaryOne68_of_bcd_zero (N G a e : k) :
    firstSecondaryOne68 N G a 0 0 0 e =
      (27 : k) * e ^ 2 * (G - 6 * N) := by
  simp only [firstSecondaryOne68]
  ring

theorem firstSecondaryOne68_of_e_c_zero_d_eq_ab (N G a b : k) :
    firstSecondaryOne68 N G a b 0 (a * b) 0 =
      (4 : k) * a ^ 3 * b ^ 2 * (6 * N - G) := by
  simp only [firstSecondaryOne68]
  ring

theorem firstLoadWall_wallGap (N G : k) (hwall : (2 : k) * G = N) :
    G - 6 * N = -(11 : k) * G := by
  calc
    G - 6 * N = G - 6 * (2 * G) := by rw [hwall]
    _ = -(11 : k) * G := by ring

theorem firstLoadWall_wallGap' (N G : k) (hwall : (2 : k) * G = N) :
    6 * N - G = (11 : k) * G := by
  calc
    6 * N - G = 6 * (2 * G) - G := by rw [hwall]
    _ = (11 : k) * G := by ring

set_option maxHeartbeats 2000000 in
/-- Exact algebraic classification of the mixed first face on `2G = N`. -/
theorem firstLoadWallFace68_classify
    (N G a b c d e l : k) (ha : a ≠ 0) (hN : N ≠ 0)
    (hwall : (2 : k) * G = N)
    (hface : FirstLoadWallFace68 N G a b c d e l) :
    l = 0 ∧ e = 0 ∧ a * b = 3 * d := by
  have hG0 : G ≠ 0 := by
    intro hG
    exact hN (by rw [← hwall, hG, mul_zero])
  have hGsix : G - 6 * N ≠ 0 := by
    intro h0
    have : -(11 : k) * G = 0 := by
      rw [← firstLoadWall_wallGap N G hwall]
      exact h0
    exact hG0 ((mul_eq_zero.mp this).resolve_left (by norm_num))
  have hSixG : 6 * N - G ≠ 0 := by
    intro h0
    have : (11 : k) * G = 0 := by
      rw [← firstLoadWall_wallGap' N G hwall]
      exact h0
    exact hG0 ((mul_eq_zero.mp this).resolve_left (by norm_num))
  have hRA :
      3 * a ^ 2 * b * c - 8 * a * b * e - 9 * a * c * d - 3 * d * e = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-576 : k) ≠ 0)
    calc
      (-576 : k) *
          (3 * a ^ 2 * b * c - 8 * a * b * e - 9 * a * c * d - 3 * d * e) =
        a * firstLoadWallFourNumerator68 a b c d e l -
          firstLoadWallZeroNumerator68 a b c d e l :=
        firstLoadWall_four_zero_combination a b c d e l
      _ = 0 := by rw [hface.four, hface.zero]; ring
  have hRB :
      3 * a ^ 2 * b * c - 19 * a * b * e - 9 * a * c * d + 30 * d * e = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-288 : k) ≠ 0)
    calc
      (-288 : k) *
          (3 * a ^ 2 * b * c - 19 * a * b * e - 9 * a * c * d + 30 * d * e) =
        a * firstLoadWallFourNumerator68 a b c d e l +
          firstLoadWallTwoNumerator68 a b c d e l :=
        firstLoadWall_four_two_combination a b c d e l
      _ = 0 := by rw [hface.four, hface.two]; ring
  have heFactor : e * (a * b - 3 * d) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (11 : k) ≠ 0)
    calc
      (11 : k) * (e * (a * b - 3 * d)) =
          (3 * a ^ 2 * b * c - 8 * a * b * e - 9 * a * c * d - 3 * d * e) -
            (3 * a ^ 2 * b * c - 19 * a * b * e - 9 * a * c * d +
              30 * d * e) :=
        (firstLoadWall_e_factor_identity a b c d e).symm
      _ = 0 := by rw [hRA, hRB]; ring
  have he0 : e = 0 := by
    by_contra he
    have hab3 : a * b = 3 * d :=
      sub_eq_zero.mp ((mul_eq_zero.mp heFactor).resolve_left he)
    have hce : c * e = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (6 : k) ≠ 0)
      calc
        (6 : k) * (c * e) =
            firstSecondaryThree68 a b c d e -
              (a * b - d) * (a * b - 3 * d) := by
          simp only [firstSecondaryThree68]
          ring
        _ = 0 := by rw [hface.three, hab3]; ring
    have hc0 : c = 0 := (mul_eq_zero.mp hce).resolve_right he
    have hcomb : (576 : k) * e * (8 * a * b + 3 * d) = 0 := by
      have hcz :
          a * firstLoadWallFourNumerator68 a b 0 d e l -
              firstLoadWallZeroNumerator68 a b 0 d e l =
            (576 : k) * e * (8 * a * b + 3 * d) := by
        simp only [firstLoadWallFourNumerator68, firstLoadWallZeroNumerator68,
          firstSecondaryFour68]
        ring
      have hfour0 : firstLoadWallFourNumerator68 a b 0 d e l = 0 := by
        simpa [hc0] using hface.four
      have hzero0 : firstLoadWallZeroNumerator68 a b 0 d e l = 0 := by
        simpa [hc0] using hface.zero
      simpa [hfour0, hzero0] using hcz
    have hlin : 8 * a * b + 3 * d = 0 := by
      have h576e : (576 : k) * e ≠ 0 :=
        mul_ne_zero (by norm_num) he
      exact (mul_eq_zero.mp hcomb).resolve_left h576e
    have hd0 : d = 0 := by
      have : (27 : k) * d = 0 := by
        calc
          (27 : k) * d = (8 * a * b + 3 * d) + 8 * (3 * d - a * b) := by ring
          _ = 0 := by rw [hlin, hab3]; ring
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    have hb0 : b = 0 := by
      have hab0 : a * b = 0 := by simpa [hd0] using hab3
      exact (mul_eq_zero.mp hab0).resolve_left ha
    have _hl0 : l = 0 := by
      have hfour' : (35 : k) * l * a ^ 4 = 0 := by
        have := hface.four
        simp only [firstLoadWallFourNumerator68, firstSecondaryFour68,
          hc0, hb0, hd0, mul_zero, sub_zero] at this
        linear_combination this
      have h35a : (35 : k) * a ^ 4 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 4 ha)
      have : ((35 : k) * a ^ 4) * l = 0 := by
        convert hfour' using 1
        ring
      exact (mul_eq_zero.mp this).resolve_left h35a
    have hone : (27 : k) * e ^ 2 * (G - 6 * N) = 0 := by
      calc
        (27 : k) * e ^ 2 * (G - 6 * N) =
            firstSecondaryOne68 N G a b c d e := by
          simp only [hb0, hc0, hd0]
          exact (firstSecondaryOne68_of_bcd_zero N G a e).symm
        _ = 0 := hface.one
    have heSq : e ^ 2 = 0 := by
      have hleft : (27 : k) * e ^ 2 = 0 :=
        (mul_eq_zero.mp hone).resolve_right hGsix
      exact (mul_eq_zero.mp hleft).resolve_left (by norm_num)
    exact he (sq_eq_zero_iff.mp heSq)
  have hcFactor : c * (a * b - 3 * d) = 0 := by
    have hcomb :
        a * firstLoadWallFourNumerator68 a b c d 0 l -
            firstLoadWallZeroNumerator68 a b c d 0 l =
          -(1728 : k) * a * c * (a * b - 3 * d) := by
      simp only [firstLoadWallFourNumerator68, firstLoadWallZeroNumerator68,
        firstSecondaryFour68]
      ring
    have : -(1728 : k) * a * c * (a * b - 3 * d) = 0 := by
      have hfour0 : firstLoadWallFourNumerator68 a b c d 0 l = 0 := by
        simpa [he0] using hface.four
      have hzero0 : firstLoadWallZeroNumerator68 a b c d 0 l = 0 := by
        simpa [he0] using hface.zero
      simpa [hfour0, hzero0] using hcomb
    have h1728a : -(1728 : k) * a ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (by norm_num)) ha
    have hassoc :
        (-(1728 : k) * a) * (c * (a * b - 3 * d)) = 0 := by
      convert this using 1
      ring
    exact (mul_eq_zero.mp hassoc).resolve_left h1728a
  have hl0 : l = 0 := by
    have hcz :
        firstLoadWallFourNumerator68 a b c d 0 l =
          (35 : k) * l * a ^ 4 -
            (1536 : k) * (c * (a * b - 3 * d)) := by
      simp only [firstLoadWallFourNumerator68, firstSecondaryFour68]
      ring
    have hfour0 : (35 : k) * l * a ^ 4 = 0 := by
      have := hface.four
      rw [he0] at this
      rw [hcz, hcFactor, mul_zero, sub_zero] at this
      exact this
    have h35a : (35 : k) * a ^ 4 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 4 ha)
    have : ((35 : k) * a ^ 4) * l = 0 := by
      convert hfour0 using 1
      ring
    exact (mul_eq_zero.mp this).resolve_left h35a
  refine ⟨hl0, he0, ?hab3⟩
  by_contra hab3
  have hab3sub : a * b - 3 * d ≠ 0 := sub_ne_zero.mpr hab3
  have hc0 : c = 0 := (mul_eq_zero.mp hcFactor).resolve_right hab3sub
  have hbd : (a * b - d) * (a * b - 3 * d) = 0 := by
    calc
      (a * b - d) * (a * b - 3 * d) =
          firstSecondaryThree68 a b c d e := by
        simp only [firstSecondaryThree68, he0, hc0, mul_zero, add_zero]
        ring
      _ = 0 := hface.three
  have habd : a * b = d :=
    sub_eq_zero.mp ((mul_eq_zero.mp hbd).resolve_right hab3sub)
  have hone :
      firstSecondaryOne68 N G a b c d e =
        (4 : k) * a ^ 3 * b ^ 2 * (6 * N - G) := by
    simpa [he0, hc0, habd.symm] using
      firstSecondaryOne68_of_e_c_zero_d_eq_ab N G a b
  have hbFace : (4 : k) * a ^ 3 * b ^ 2 * (6 * N - G) = 0 := by
    rw [← hone]
    exact hface.one
  have habSq : (4 : k) * a ^ 3 * b ^ 2 = 0 :=
    (mul_eq_zero.mp hbFace).resolve_right hSixG
  have hbSq : b ^ 2 = 0 := by
    apply (mul_eq_zero.mp habSq).resolve_left
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)
  have hb0 : b = 0 := sq_eq_zero_iff.mp hbSq
  have hd0 : d = 0 := by simpa [hb0] using habd.symm
  exact hab3 (by simp [hb0, hd0])

/-- Integer-radius form used by the polynomial wall extraction. -/
theorem firstLoadWallFace68_classify_of_two_mul_gap_eq_radius
    (n g : ℕ) (a b c d e l : k) (ha : a ≠ 0) (hn : 0 < n)
    (hwall : 2 * g = n)
    (hface : FirstLoadWallFace68 (n : k) (g : k) a b c d e l) :
    l = 0 ∧ e = 0 ∧ a * b = 3 * d := by
  refine firstLoadWallFace68_classify (n : k) (g : k) a b c d e l ha ?hN ?hk
    hface
  · exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  · exact_mod_cast hwall

end FirstLoadWallFace68

#print axioms firstLoadWallFourScalar68_eq_numerator
#print axioms firstLoadWallTwoScalar68_eq_numerator
#print axioms firstLoadWallZeroScalar68_eq_numerator
#print axioms firstLoadWallFourScalar68_eq_F4_load
#print axioms firstLoadWallTwoScalar68_eq_F2_load
#print axioms firstLoadWallZeroScalar68_eq_F0_load
#print axioms firstLoadWall_four_zero_combination
#print axioms firstLoadWall_four_two_combination
#print axioms firstLoadWall_e_factor_identity
#print axioms firstSecondaryThree68_factor
#print axioms firstSecondaryOne68_of_bcd_zero
#print axioms firstSecondaryOne68_of_e_c_zero_d_eq_ab
#print axioms firstLoadWall_wallGap
#print axioms firstLoadWall_wallGap'
#print axioms firstLoadWallFace68_classify
#print axioms firstLoadWallFace68_classify_of_two_mul_gap_eq_radius

end Max11DegreeRoutes
