import LowScale68SecondaryResidualDoubleLoadWallPart02Scratch

/-! # Mixed residual double face on the `(6,8)` wall `n = 3g`, `h = 2g`

On `n = 3g` the residual double face `9n-3g` collides with the Jacobian
load `l A^4` at degree `8n`.  Row two and row zero likewise meet the cores
`l A^5` and `l A^6` at `10n-1` and `12n-1`.  I3 and row one remain
load-free.  The five leading scalars force `l = b = c = 0`; residual
support `b ≠ 0 ∨ c ≠ 0` therefore excludes the wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Abstract mixed numerators -/

/-! ## Scalar identities -/

set_option maxHeartbeats 4000000 in
/-- Exact algebraic classification: the mixed residual double load wall
forces `l = 0` and vanishing of both first-face directions `b,c`. -/
theorem residualDoubleLoadWallFace68_classify
    (N G a b c d e l : k) (ha : a ≠ 0) (hN : N ≠ 0)
    (hwall : (3 : k) * G = N)
    (hface : ResidualDoubleLoadWallFace68 N G a b c d e l) :
    l = 0 ∧ b = 0 ∧ c = 0 := by
  have hG : G ≠ 0 := by
    intro hG0
    exact hN (by rw [← hwall, hG0, mul_zero])
  have hP04 : residualDoubleLoadWallFourZeroPoly68 a b c d e = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (64 : k) ≠ 0)
    calc
      (64 : k) * residualDoubleLoadWallFourZeroPoly68 a b c d e =
          residualDoubleLoadWallZeroNumerator68 a b c d e l -
            a * residualDoubleLoadWallFourNumerator68 a b c d e l :=
        residualDoubleLoadWall_four_zero_combination a b c d e l
      _ = 0 := by rw [hface.zero, hface.four]; ring
  have hP24 : residualDoubleLoadWallFourTwoPoly68 a b c d e = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (32 : k) ≠ 0)
    calc
      (32 : k) * residualDoubleLoadWallFourTwoPoly68 a b c d e =
          residualDoubleLoadWallTwoNumerator68 a b c d e l -
            a * residualDoubleLoadWallFourNumerator68 a b c d e l :=
        residualDoubleLoadWall_four_two_combination a b c d e l
      _ = 0 := by rw [hface.two, hface.four]; ring
  have hfactor : b * (a * b ^ 2 - 9 * c ^ 2) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (11 : k) ≠ 0)
    calc
      (11 : k) * (b * (a * b ^ 2 - 9 * c ^ 2)) =
          residualDoubleLoadWallFourTwoPoly68 a b c d e -
            residualDoubleLoadWallFourZeroPoly68 a b c d e :=
        (residualDoubleLoadWall_disc_factor_identity a b c d e).symm
      _ = 0 := by rw [hP24, hP04]; ring
  by_cases hb : b = 0
  · have hc0 : c = 0 := by
      have hthree : (3 : k) * (c * e) = 0 := by
        simpa [residualDoubleThreeHom68, hb, mul_assoc] using hface.three
      have hone :
          (3 : k) * G * c * (27 * a * e - 11 * c ^ 2) = 0 := by
        have h := hface.one
        simp only [hb] at h
        rw [residualDoubleLoadWall_one_of_b_eq_zero N G a c d e hwall] at h
        exact h
      have hce : c * e = 0 :=
        (mul_eq_zero.mp hthree).resolve_left (by norm_num)
      by_cases hc : c = 0
      · exact hc
      · have he0 : e = 0 := (mul_eq_zero.mp hce).resolve_left hc
        have hGc : (3 : k) * G * c ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) hG) hc
        have hlin : 27 * a * e - 11 * c ^ 2 = 0 :=
          (mul_eq_zero.mp hone).resolve_left hGc
        have hc2 : (11 : k) * c ^ 2 = 0 := by
          rw [he0] at hlin
          linear_combination -hlin
        exact False.elim
          ((pow_ne_zero 2 hc)
            ((mul_eq_zero.mp hc2).resolve_left (by norm_num)))
    have hl0 : l = 0 := by
      have hfour : (35 : k) * l * a ^ 4 = 0 := by
        have h := hface.four
        simp only [residualDoubleLoadWallFourNumerator68,
          residualDoubleFourHom68, hb, hc0, mul_zero] at h
        linear_combination h
      have h35a : (35 : k) * a ^ 4 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 4 ha)
      have : ((35 : k) * a ^ 4) * l = 0 := by
        convert hfour using 1
        ring
      exact (mul_eq_zero.mp this).resolve_left h35a
    exact ⟨hl0, hb, hc0⟩
  · have hdisc : a * b ^ 2 = 9 * c ^ 2 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hb)
    have hc : c ≠ 0 := by
      intro hc0
      have hab2 : a * b ^ 2 = 0 := by simpa [hc0] using hdisc
      exact hb (sq_eq_zero_iff.mp
        ((mul_eq_zero.mp hab2).resolve_left ha))
    have hfour0 : residualDoubleFourHom68 b c d e = 0 := by
      have hP := residualDoubleLoadWallFourZeroPoly68_eq_four_of_disc
        a b c d e hdisc
      have hprod : -(9 : k) * a * residualDoubleFourHom68 b c d e = 0 := by
        rw [← hP]; exact hP04
      have h9a : -(9 : k) * a ≠ 0 :=
        mul_ne_zero (neg_ne_zero.mpr (by norm_num)) ha
      exact (mul_eq_zero.mp hprod).resolve_left h9a
    have hl0 : l = 0 := by
      have hfour : (35 : k) * l * a ^ 4 = 0 := by
        have h := hface.four
        simp only [residualDoubleLoadWallFourNumerator68, hfour0,
          mul_zero, add_zero] at h
        exact h
      have h35a : (35 : k) * a ^ 4 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 4 ha)
      have : ((35 : k) * a ^ 4) * l = 0 := by
        convert hfour using 1
        ring
      exact (mul_eq_zero.mp this).resolve_left h35a
    have htied := ResidualDoubleLoadWallFace68.toTiedDouble_of_l_eq_zero
      N G a b c d e l hl0 hface
    have hG4 := secondaryResidualTiedDoubleFace68_forces_gap_eq_four_radius
      N G a b c d e ha hb hc htied
    have h11 : (11 : k) * N = 0 := by
      calc
        (11 : k) * N = (3 : k) * (4 * N) - N := by ring
        _ = (3 : k) * G - N := by rw [hG4]
        _ = N - N := by rw [hwall]
        _ = 0 := by ring
    exact False.elim (hN ((mul_eq_zero.mp h11).resolve_left (by norm_num)))

end Max11DegreeRoutes
