import LowScale68SecondaryOneForms

/-! # Abstract mixed first face on the `(6,8)` wall `2g = n`

Untracked working note. No tracked file was edited.

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
set_option linter.unusedVariables false

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

/-! ## Polynomial coefficient extraction on `2g = n`

The formulas below re-prove the mixed leading coefficients of §3.3 by the
same `coeff_mul_at_bounds68` / `coeff_derivative_at_bound68` style as the
tracked first-face extraction.  Derivative substitutions are the coefficient
identity `(p').coeff(u-1) = u * p.coeff u`, which holds for constant
coordinates as well (both sides vanish).  On this wall every displayed
bound is positive: `2g = n` and `0 < n` force `n ≥ 2`. -/

section FirstLoadWallExtraction68

open Polynomial

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ### Jacobian load cores, with the `A^5` cancellation checked by `ring` -/

/-- The unique `l A^5` combination in row two: `Ul C0' + 3 Sl E' - 2 C0 Ul'`
on the cubic core `C0 = A^2/3`, `E = A^3/27`. -/
def cubicLoadRowTwoLCorePolynomial68 (l : k) (A : k[X]) : k[X] :=
  let C0 := (1 / 3 : k) • A ^ 2
  let E := (1 / 27 : k) • A ^ 3
  let Ul := (35 / 432 * l : k) • A ^ 3
  let Sl := (35 / 72 * l : k) • A ^ 2
  Ul * derivative C0 + (3 : k) • (Sl * derivative E) -
    (2 : k) • (C0 * derivative Ul)

/-- The unique `l A^6` combination in row zero: `Ul E'` on `E = A^3/27`. -/
def cubicLoadRowZeroLCorePolynomial68 (l : k) (A : k[X]) : k[X] :=
  ((35 / 432 * l : k) • A ^ 3) *
    derivative ((1 / 27 : k) • A ^ 3)

set_option maxHeartbeats 4000000 in
/-- `3 Sl E'` and `-2 C0 Ul'` cancel; only `Ul C0' = (35/648) l A^4 A'`
survives. -/
theorem cubicLoadRowTwoLCorePolynomial68_eq (l : k) (A : k[X]) :
    cubicLoadRowTwoLCorePolynomial68 l A =
      (35 / 648 * l : k) • (A ^ 4 * derivative A) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoLCorePolynomial68, derivative_add,
    derivative_sub, derivative_smul, derivative_mul, derivative_pow,
    derivative_C, Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowZeroLCorePolynomial68_eq (l : k) (A : k[X]) :
    cubicLoadRowZeroLCorePolynomial68 l A =
      (35 / 3888 * l : k) • (A ^ 5 * derivative A) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowZeroLCorePolynomial68, derivative_add,
    derivative_sub, derivative_smul, derivative_mul, derivative_pow,
    derivative_C, Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoLCorePolynomial68_coeff_loadWall
    (l : k) (A : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) :
    (cubicLoadRowTwoLCorePolynomial68 l A).coeff (10 * n - 1) =
      (35 / 324 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  have hA4deg : (A ^ 4).natDegree ≤ 8 * n := by
    compute_degree
    omega
  have hA4 : (A ^ 4).coeff (8 * n) = A.coeff (2 * n) ^ 4 := by
    have h := coeff_pow_at_bound68 A (2 * n) 4 hA
    have hi : 4 * (2 * n) = 8 * n := by omega
    simpa only [hi] using h
  have hprod : (A ^ 4 * derivative A).coeff (10 * n - 1) =
      A.coeff (2 * n) ^ 4 * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 (A ^ 4) A
      (8 * n) (2 * n) (by omega) hA4deg hA
    have hi : 8 * n + 2 * n - 1 = 10 * n - 1 := by omega
    rw [hi, hA4] at h
    exact h
  rw [cubicLoadRowTwoLCorePolynomial68_eq, coeff_smul, hprod, smul_eq_mul]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroLCorePolynomial68_coeff_loadWall
    (l : k) (A : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) :
    (cubicLoadRowZeroLCorePolynomial68 l A).coeff (12 * n - 1) =
      (35 / 1944 : k) * (n : k) * l * A.coeff (2 * n) ^ 6 := by
  have hA5deg : (A ^ 5).natDegree ≤ 10 * n := by
    compute_degree
    omega
  have hA5 : (A ^ 5).coeff (10 * n) = A.coeff (2 * n) ^ 5 := by
    have h := coeff_pow_at_bound68 A (2 * n) 5 hA
    have hi : 5 * (2 * n) = 10 * n := by omega
    simpa only [hi] using h
  have hprod : (A ^ 5 * derivative A).coeff (12 * n - 1) =
      A.coeff (2 * n) ^ 5 * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 (A ^ 5) A
      (10 * n) (2 * n) (by omega) hA5deg hA
    have hi : 10 * n + 2 * n - 1 = 12 * n - 1 := by omega
    rw [hi, hA5] at h
    exact h
  rw [cubicLoadRowZeroLCorePolynomial68_eq, coeff_smul, hprod, smul_eq_mul]
  push_cast
  ring

/-! ### Mixed I4 at `8n` and load-free I3 at `9n` -/

set_option maxHeartbeats 3000000 in
/-- Mixed I4 leading coefficient at index `8n` on `2g = n`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_loadWall
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (8 * n) =
      firstLoadWallFourScalar68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) l := by
  have lower (p : k[X]) (hp : p.natDegree < 8 * n) :
      p.coeff (8 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hA4 : (A ^ 4).coeff (8 * n) = A.coeff (2 * n) ^ 4 := by
    have h := coeff_pow_at_bound68 A (2 * n) 4 hA
    have hi : 4 * (2 * n) = 8 * n := by omega
    simpa only [hi] using h
  have hABC : (A * B * c).coeff (8 * n) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B c (2 * n)
      (3 * n - g) (4 * n - g) hA hB hc
    have hi : 2 * n + (3 * n - g) + (4 * n - g) = 8 * n := by omega
    simpa only [hi] using h
  have hBe : (B * e).coeff (8 * n) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - g) hB he
    have hi : (3 * n - g) + (6 * n - g) = 8 * n := by omega
    simpa only [hi] using h
  have hDc : (D * c).coeff (8 * n) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) := by
    have h := coeff_mul_at_bounds68 D c (5 * n - g) (4 * n - g) hD hc
    have hi : (5 * n - g) + (4 * n - g) = 8 * n := by omega
    simpa only [hi] using h
  have hB3 : (B ^ 3).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hAz : A.coeff (8 * n) = 0 := lower _ (by omega)
  have hBz : B.coeff (8 * n) = 0 := lower _ (by omega)
  have hA2 : (A ^ 2).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hcz : c.coeff (8 * n) = 0 := lower _ (by omega)
  have hDz : D.coeff (8 * n) = 0 := lower _ (by omega)
  have hAB : (A * B).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hez : e.coeff (8 * n) = 0 := lower _ (by omega)
  have hAc : (A * c).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hB2 : (B ^ 2).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hA3 : (A ^ 3).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hA2c : (A ^ 2 * c).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hAB2 : (A * B ^ 2).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hAe : (A * e).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hBD : (B * D).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hc2 : (c ^ 2).coeff (8 * n) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralFourPolynomial68, coeff_add, coeff_sub,
    coeff_smul, hABC, hBe, hDc, hB3, hAz, hBz, hA2, hcz, hDz,
    hAB, hez, hAc, hB2, hA3, hA4, hA2c, hAB2, hAe, hBD, hc2,
    smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstLoadWallFourScalar68]
  ring

set_option maxHeartbeats 3000000 in
/-- I3 is unchanged on this wall: the `l A^3 B` load sits at `9n-g < 9n`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_loadWall
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (9 * n) =
      (4 / 9 : k) * firstSecondaryThree68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have lower (p : k[X]) (hp : p.natDegree < 9 * n) :
      p.coeff (9 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hA2coeff : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hB2coeff : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hA2B2 : (A ^ 2 * B ^ 2).coeff (9 * n) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_mul_at_bounds68 (A ^ 2) (B ^ 2) (4 * n)
      (6 * n - 2 * g) hA2deg hB2deg
    have hi : 4 * n + (6 * n - 2 * g) = 9 * n := by omega
    rw [hi, hA2coeff, hB2coeff] at h
    exact h
  have hABD : (A * B * D).coeff (9 * n) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        D.coeff (5 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B D (2 * n)
      (3 * n - g) (5 * n - g) hA hB hD
    have hi : 2 * n + (3 * n - g) + (5 * n - g) = 9 * n := by omega
    simpa only [hi] using h
  have hD2 : (D ^ 2).coeff (9 * n) =
      D.coeff (5 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 D (5 * n - g) 2 hD
    have hi : 2 * (5 * n - g) = 9 * n := by omega
    simpa only [hi] using h
  have hce : (c * e).coeff (9 * n) =
      c.coeff (4 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - g) hc he
    have hi : (4 * n - g) + (6 * n - g) = 9 * n := by omega
    simpa only [hi] using h
  have hB2c : (B ^ 2 * c).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hBz : B.coeff (9 * n) = 0 := lower _ (by omega)
  have hcz : c.coeff (9 * n) = 0 := lower _ (by omega)
  have hez : e.coeff (9 * n) = 0 := lower _ (by omega)
  have hB2z : (B ^ 2).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hDz : D.coeff (9 * n) = 0 := lower _ (by omega)
  have hAB : (A * B).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hA2B : (A ^ 2 * B).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hAD : (A * D).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hBc : (B * c).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hA3B : (A ^ 3 * B).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hA2D : (A ^ 2 * D).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hABc : (A * B * c).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hB3 : (B ^ 3).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hBe : (B * e).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  have hDc : (D * c).coeff (9 * n) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralThreePolynomial68, coeff_add, coeff_sub,
    coeff_smul, hA2B2, hABD, hB2c, hD2, hce, hBz, hcz, hez, hB2z,
    hDz, hAB, hA2B, hAD, hBc, hA3B, hA2D, hABc, hB3, hBe, hDc,
    smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstSecondaryThree68]
  ring

/-! ### Homogeneous one-form cores at the wall indices -/

set_option maxHeartbeats 3000000 in
theorem firstSecondaryCoreRowTwoPolynomial68_coeff_loadWall
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (firstSecondaryCoreRowTwoPolynomial68 A B c D e).coeff (10 * n - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA2coeff : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * derivative c).coeff (10 * n - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B c
      (4 * n) (3 * n - g) (4 * n - g) (by omega) hA2deg hB hc
    have hi : 4 * n + (3 * n - g) + (4 * n - g) - 1 = 10 * n - 1 := by omega
    rw [hi, hA2coeff] at h
    exact h
  have h2 : (A ^ 2 * c * derivative B).coeff (10 * n - 1) =
      A.coeff (2 * n) ^ 2 * c.coeff (4 * n - g) *
        B.coeff (3 * n - g) * ((3 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) c B
      (4 * n) (4 * n - g) (3 * n - g) (by omega) hA2deg hc hB
    have hi : 4 * n + (4 * n - g) + (3 * n - g) - 1 = 10 * n - 1 := by omega
    rw [hi, hA2coeff] at h
    exact h
  have h3 : (A * B * c * derivative A).coeff (10 * n - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 A B c A
      (2 * n) (3 * n - g) (4 * n - g) (2 * n) (by omega)
      hA hB hc hA
    have hi : 2 * n + (3 * n - g) + (4 * n - g) + 2 * n - 1 =
        10 * n - 1 := by omega
    simpa only [hi] using h
  have h4 : (A * D * derivative c).coeff (10 * n - 1) =
      A.coeff (2 * n) * D.coeff (5 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A D c
      (2 * n) (5 * n - g) (4 * n - g) (by omega) hA hD hc
    have hi : 2 * n + (5 * n - g) + (4 * n - g) - 1 = 10 * n - 1 := by omega
    simpa only [hi] using h
  have h5 : (A * c * derivative D).coeff (10 * n - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        D.coeff (5 * n - g) * ((5 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A c D
      (2 * n) (4 * n - g) (5 * n - g) (by omega) hA hc hD
    have hi : 2 * n + (4 * n - g) + (5 * n - g) - 1 = 10 * n - 1 := by omega
    simpa only [hi] using h
  have h6 : (B * e * derivative A).coeff (10 * n - 1) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 B e A
      (3 * n - g) (6 * n - g) (2 * n) (by omega) hB he hA
    have hi : (3 * n - g) + (6 * n - g) + 2 * n - 1 = 10 * n - 1 := by omega
    simpa only [hi] using h
  have h7 : (D * c * derivative A).coeff (10 * n - 1) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 D c A
      (5 * n - g) (4 * n - g) (2 * n) (by omega) hD hc hA
    have hi : (5 * n - g) + (4 * n - g) + 2 * n - 1 = 10 * n - 1 := by omega
    simpa only [hi] using h
  have h8 : (D * derivative e).coeff (10 * n - 1) =
      D.coeff (5 * n - g) * e.coeff (6 * n - g) *
        ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 D e
      (5 * n - g) (6 * n - g) (by omega) hD he
    have hi : (5 * n - g) + (6 * n - g) - 1 = 10 * n - 1 := by omega
    simpa only [hi] using h
  have h9 : (e * derivative D).coeff (10 * n - 1) =
      e.coeff (6 * n - g) * D.coeff (5 * n - g) *
        ((5 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 e D
      (6 * n - g) (5 * n - g) (by omega) he hD
    have hi : (6 * n - g) + (5 * n - g) - 1 = 10 * n - 1 := by omega
    simpa only [hi] using h
  simp only [firstSecondaryCoreRowTwoPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2, h3, h4, h5, h6, h7, h8, h9, smul_eq_mul]
  have hg3 : g ≤ 3 * n := by omega
  have hg4 : g ≤ 4 * n := by omega
  have hg5 : g ≤ 5 * n := by omega
  have hg6 : g ≤ 6 * n := by omega
  have hcast3 : (((3 * n - g : ℕ) : k)) = (n : k) * 3 - (g : k) := by
    rw [Nat.cast_sub hg3]
    push_cast
    ring
  have hcast4 : (((4 * n - g : ℕ) : k)) = (n : k) * 4 - (g : k) := by
    rw [Nat.cast_sub hg4]
    push_cast
    ring
  have hcast5 : (((5 * n - g : ℕ) : k)) = (n : k) * 5 - (g : k) := by
    rw [Nat.cast_sub hg5]
    push_cast
    ring
  have hcast6 : (((6 * n - g : ℕ) : k)) = (n : k) * 6 - (g : k) := by
    rw [Nat.cast_sub hg6]
    push_cast
    ring
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  simp only [firstSecondaryTwo68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousRowTwoPolynomial68_coeff_loadWall
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowTwoPolynomial68 A B c D e).coeff (10 * n - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowTwoPolynomial68 A B c D).natDegree <
      10 * n - 1 := by
    simp only [cubicRemainderRowTwoPolynomial68]
    compute_degree
    omega
  rw [cubicHomogeneousRowTwoPolynomial68_eq_expanded,
    cubicHomogeneousRowTwoExpandedPolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowTwoPolynomial68_coeff_loadWall A B c D e n g
    hn hg hwall hA hB hc hD he

set_option maxHeartbeats 3000000 in
theorem firstSecondaryCoreRowOnePolynomial68_coeff_loadWall
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (firstSecondaryCoreRowOnePolynomial68 A B c D e).coeff (11 * n - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA3deg : (A ^ 3).natDegree ≤ 6 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hD2deg : (D ^ 2).natDegree ≤ 10 * n - 2 * g := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hA3 : (A ^ 3).coeff (6 * n) = A.coeff (2 * n) ^ 3 := by
    have h := coeff_pow_at_bound68 A (2 * n) 3 hA
    have hi : 3 * (2 * n) = 6 * n := by omega
    simpa only [hi] using h
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hD2 : (D ^ 2).coeff (10 * n - 2 * g) =
      D.coeff (5 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 D (5 * n - g) 2 hD
    have hi : 2 * (5 * n - g) = 10 * n - 2 * g := by omega
    simpa only [hi] using h
  have h1 : (A ^ 3 * B * derivative B).coeff (11 * n - 1) =
      A.coeff (2 * n) ^ 3 * B.coeff (3 * n - g) ^ 2 *
        ((3 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 3) B B
      (6 * n) (3 * n - g) (3 * n - g) (by omega) hA3deg hB hB
    have hi : 6 * n + (3 * n - g) + (3 * n - g) - 1 = 11 * n - 1 := by omega
    rw [hi, hA3] at h
    ring_nf at h ⊢
    exact h
  have h2 : (A ^ 2 * B ^ 2 * derivative A).coeff (11 * n - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 2 *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) (B ^ 2) A
      (4 * n) (6 * n - 2 * g) (2 * n) (by omega)
      hA2deg hB2deg hA
    have hi : 4 * n + (6 * n - 2 * g) + 2 * n - 1 = 11 * n - 1 := by omega
    rw [hi, hA2, hB2] at h
    exact h
  have h3 : (A ^ 2 * B * derivative D).coeff (11 * n - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        D.coeff (5 * n - g) * ((5 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B D
      (4 * n) (3 * n - g) (5 * n - g) (by omega) hA2deg hB hD
    have hi : 4 * n + (3 * n - g) + (5 * n - g) - 1 = 11 * n - 1 := by omega
    rw [hi, hA2] at h
    exact h
  have h4 : (A ^ 2 * D * derivative B).coeff (11 * n - 1) =
      A.coeff (2 * n) ^ 2 * D.coeff (5 * n - g) *
        B.coeff (3 * n - g) * ((3 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) D B
      (4 * n) (5 * n - g) (3 * n - g) (by omega) hA2deg hD hB
    have hi : 4 * n + (5 * n - g) + (3 * n - g) - 1 = 11 * n - 1 := by omega
    rw [hi, hA2] at h
    exact h
  have h5 : (A * c * derivative e).coeff (11 * n - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - g) * ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A c e
      (2 * n) (4 * n - g) (6 * n - g) (by omega) hA hc he
    have hi : 2 * n + (4 * n - g) + (6 * n - g) - 1 = 11 * n - 1 := by omega
    simpa only [hi] using h
  have h6 : (A * e * derivative c).coeff (11 * n - 1) =
      A.coeff (2 * n) * e.coeff (6 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A e c
      (2 * n) (6 * n - g) (4 * n - g) (by omega) hA he hc
    have hi : 2 * n + (6 * n - g) + (4 * n - g) - 1 = 11 * n - 1 := by omega
    simpa only [hi] using h
  have h7 : (D ^ 2 * derivative A).coeff (11 * n - 1) =
      D.coeff (5 * n - g) ^ 2 * A.coeff (2 * n) *
        ((2 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 (D ^ 2) A
      (10 * n - 2 * g) (2 * n) (by omega) hD2deg hA
    have hi : (10 * n - 2 * g) + 2 * n - 1 = 11 * n - 1 := by omega
    rw [hi, hD2] at h
    exact h
  have h8 : (e * derivative e).coeff (11 * n - 1) =
      e.coeff (6 * n - g) ^ 2 * ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 e e
      (6 * n - g) (6 * n - g) (by omega) he he
    have hi : (6 * n - g) + (6 * n - g) - 1 = 11 * n - 1 := by omega
    rw [hi] at h
    ring_nf at h ⊢
    exact h
  simp only [firstSecondaryCoreRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2, h3, h4, h5, h6, h7, h8, smul_eq_mul]
  have hg3 : g ≤ 3 * n := by omega
  have hg4 : g ≤ 4 * n := by omega
  have hg5 : g ≤ 5 * n := by omega
  have hg6 : g ≤ 6 * n := by omega
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg3]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = 4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg4]
    push_cast
    rfl
  have hcast5 : (((5 * n - g : ℕ) : k)) = 5 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg5]
    push_cast
    rfl
  have hcast6 : (((6 * n - g : ℕ) : k)) = 6 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg6]
    push_cast
    rfl
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  simp only [firstSecondaryOne68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousRowOnePolynomial68_coeff_loadWall
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowOnePolynomial68 A B c D e).coeff (11 * n - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowOnePolynomial68 A B c D e).natDegree <
      11 * n - 1 := by
    simp only [cubicRemainderRowOnePolynomial68]
    compute_degree
    omega
  rw [cubicHomogeneousRowOnePolynomial68_eq_expanded,
    cubicHomogeneousRowOneExpandedPolynomial68, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowOnePolynomial68_coeff_loadWall A B c D e n g
    hn hg hwall hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem firstSecondaryCoreRowZeroPolynomial68_coeff_loadWall
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (firstSecondaryCoreRowZeroPolynomial68 A B c D e).coeff (12 * n - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * c * derivative A).coeff (12 * n - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 (A ^ 2) B c A
      (4 * n) (3 * n - g) (4 * n - g) (2 * n) (by omega)
      hA2deg hB hc hA
    have hi : 4 * n + (3 * n - g) + (4 * n - g) + 2 * n - 1 =
        12 * n - 1 := by omega
    rw [hi, hA2] at h
    exact h
  have h2 : (A * D * c * derivative A).coeff (12 * n - 1) =
      A.coeff (2 * n) * D.coeff (5 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 A D c A
      (2 * n) (5 * n - g) (4 * n - g) (2 * n) (by omega)
      hA hD hc hA
    have hi : 2 * n + (5 * n - g) + (4 * n - g) + 2 * n - 1 =
        12 * n - 1 := by omega
    simpa only [hi] using h
  have h3 : (D * e * derivative A).coeff (12 * n - 1) =
      D.coeff (5 * n - g) * e.coeff (6 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 D e A
      (5 * n - g) (6 * n - g) (2 * n) (by omega) hD he hA
    have hi : (5 * n - g) + (6 * n - g) + 2 * n - 1 = 12 * n - 1 := by omega
    simpa only [hi] using h
  simp only [firstSecondaryCoreRowZeroPolynomial68, coeff_smul, coeff_sub,
    h1, h2, h3, smul_eq_mul]
  push_cast
  simp only [firstSecondaryZero68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousRowZeroPolynomial68_coeff_loadWall
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowZeroPolynomial68 A B c D e).coeff (12 * n - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowZeroPolynomial68 A B c D e).natDegree <
      12 * n - 1 := by
    simp only [cubicRemainderRowZeroPolynomial68]
    compute_degree
    omega
  rw [cubicHomogeneousRowZeroPolynomial68_eq_expanded,
    cubicHomogeneousRowZeroExpandedPolynomial68, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowZeroPolynomial68_coeff_loadWall A B c D e n g
    hn hg hwall hA hB hc hD he

/-! ### Load remainders versus the wall indices

Row one stays strictly load-free.  Rows two and zero meet the Jacobian
core, so only the non-core load is claimed to lie below the face. -/

set_option maxHeartbeats 3000000 in
theorem cubicLoadPolynomials68_degreeBounds_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadSPolynomial68 l alpha beta delta A B c).natDegree ≤ 4 * n ∧
    (cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D).natDegree ≤
      5 * n - g ∧
    (cubicLoadUPolynomial68 l alpha beta gamma delta zeta
      A B c D e).natDegree ≤ 6 * n ∧
    (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 7 * n - g := by
  simp only [cubicLoadSPolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68]
  constructor
  · compute_degree
    omega
  constructor
  · compute_degree
    omega
  constructor <;> compute_degree <;> omega

set_option maxHeartbeats 3000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 11 * n - 1 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hloads := cubicLoadPolynomials68_degreeBounds_loadWall
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 6 * n := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlD : (Ul * derivative D).natDegree < 11 * n - 1 := by
    compute_degree
    omega
  have hTlE : (Tl * derivative E).natDegree < 11 * n - 1 := by
    compute_degree
    omega
  have hC0Vl : (C0 * derivative Vl).natDegree < 11 * n - 1 := by
    compute_degree
    omega
  have hDUl : (D * derivative Ul).natDegree < 11 * n - 1 := by
    compute_degree
    omega
  change (Ul * derivative D + (2 : k) • (Tl * derivative E) -
    (2 : k) • (C0 * derivative Vl) - D * derivative Ul).natDegree < _
  compute_degree
  omega

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowOnePolynomial68_coeff_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (11 * n - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq, cubicRowOnePolynomial68_split,
    coeff_add, coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_loadWall
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hwall hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowOnePolynomial68_coeff_loadWall A B c D e n g
    hn hg hwall hA hB hc hD he

/-! The remaining gap on this wall is to identify the *full* load polynomials
`cubicLoadRowTwoPolynomial68` and `cubicLoadRowZeroPolynomial68` with their
Jacobian cores plus a remainder of degree strictly below `10n-1` / `12n-1`.
That comparison does not cancel in `compute_degree`, and the algebraic split
into core-plus-rest is not yet a `ring` identity.  Until that split is
checked, the canonical `IntegratedPolynomialLowerSystem68` wrapper cannot
feed `FirstLoadWallFace68`. -/

end FirstLoadWallExtraction68

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
#print axioms cubicLoadRowTwoLCorePolynomial68_eq
#print axioms cubicLoadRowZeroLCorePolynomial68_eq
#print axioms cubicLoadRowTwoLCorePolynomial68_coeff_loadWall
#print axioms cubicLoadRowZeroLCorePolynomial68_coeff_loadWall
#print axioms cubicFirstIntegralFourPolynomial68_coeff_loadWall
#print axioms cubicFirstIntegralThreePolynomial68_coeff_loadWall
#print axioms firstSecondaryCoreRowTwoPolynomial68_coeff_loadWall
#print axioms cubicHomogeneousRowTwoPolynomial68_coeff_loadWall
#print axioms firstSecondaryCoreRowOnePolynomial68_coeff_loadWall
#print axioms cubicHomogeneousRowOnePolynomial68_coeff_loadWall
#print axioms firstSecondaryCoreRowZeroPolynomial68_coeff_loadWall
#print axioms cubicHomogeneousRowZeroPolynomial68_coeff_loadWall
#print axioms cubicLoadPolynomials68_degreeBounds_loadWall
#print axioms cubicLoadRowOnePolynomial68_degree_lt_loadWall
#print axioms integratedLowerRowOnePolynomial68_coeff_loadWall

end Max11DegreeRoutes
