import LowScale68SecondaryResidualDoubleLoadWallPart01Scratch

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

theorem residualDoubleLoadWallZeroScalar68_eq_hom_add_load
    (N a b c d e l : k) :
    residualDoubleLoadWallZeroScalar68 N a b c d e l =
      (8 / 27 : k) * N * a * residualDoubleZeroHom68 a b c d e +
        (35 / 1944 : k) * N * l * a ^ 6 := by
  simp only [residualDoubleLoadWallZeroScalar68,
    residualDoubleLoadWallZeroNumerator68, residualDoubleZeroHom68]
  ring

theorem residualDoubleLoadWall_four_zero_combination
    (a b c d e l : k) :
    (64 : k) * residualDoubleLoadWallFourZeroPoly68 a b c d e =
      residualDoubleLoadWallZeroNumerator68 a b c d e l -
        a * residualDoubleLoadWallFourNumerator68 a b c d e l := by
  simp only [residualDoubleLoadWallFourZeroPoly68,
    residualDoubleLoadWallZeroNumerator68,
    residualDoubleLoadWallFourNumerator68, residualDoubleFourHom68,
    residualDoubleZeroHom68]
  ring

theorem residualDoubleLoadWall_four_two_combination
    (a b c d e l : k) :
    (32 : k) * residualDoubleLoadWallFourTwoPoly68 a b c d e =
      residualDoubleLoadWallTwoNumerator68 a b c d e l -
        a * residualDoubleLoadWallFourNumerator68 a b c d e l := by
  simp only [residualDoubleLoadWallFourTwoPoly68,
    residualDoubleLoadWallTwoNumerator68,
    residualDoubleLoadWallFourNumerator68, residualDoubleFourHom68]
  ring

theorem residualDoubleLoadWall_disc_factor_identity (a b c d e : k) :
    residualDoubleLoadWallFourTwoPoly68 a b c d e -
        residualDoubleLoadWallFourZeroPoly68 a b c d e =
      (11 : k) * (b * (a * b ^ 2 - 9 * c ^ 2)) := by
  simp only [residualDoubleLoadWallFourTwoPoly68,
    residualDoubleLoadWallFourZeroPoly68]
  ring

theorem residualDoubleLoadWall_one_eq_cleared
    (N G a b c d e : k) (hwall : (3 : k) * G = N) :
    3 * a ^ 2 * b * G * d - 10 * a ^ 2 * b * N * d +
        2 * a * b ^ 2 * N * c - 9 * a * G * c * e +
        30 * a * N * c * e + 3 * G * c ^ 3 - 12 * N * c ^ 3 =
      -N * (9 * a ^ 2 * b * d - 2 * a * b ^ 2 * c -
        27 * a * c * e + 11 * c ^ 3) := by
  rw [← hwall]
  ring

theorem residualDoubleLoadWall_one_of_b_eq_zero
    (N G a c d e : k) (hwall : (3 : k) * G = N) :
    3 * a ^ 2 * (0 : k) * G * d - 10 * a ^ 2 * (0 : k) * N * d +
        2 * a * (0 : k) ^ 2 * N * c - 9 * a * G * c * e +
        30 * a * N * c * e + 3 * G * c ^ 3 - 12 * N * c ^ 3 =
      (3 : k) * G * c * (27 * a * e - 11 * c ^ 2) := by
  rw [← hwall]
  ring

theorem residualDoubleLoadWallFourZeroPoly68_eq_four_of_disc
    (a b c d e : k) (hdisc : a * b ^ 2 = 9 * c ^ 2) :
    residualDoubleLoadWallFourZeroPoly68 a b c d e =
      -(9 : k) * a * residualDoubleFourHom68 b c d e := by
  simp only [residualDoubleLoadWallFourZeroPoly68, residualDoubleFourHom68]
  have h9 : (9 : k) * c ^ 2 = a * b ^ 2 := hdisc.symm
  rw [show (9 : k) * b * c ^ 2 = b * ((9 : k) * c ^ 2) by ring, h9]
  ring

theorem residualDoubleLoadWallFourNumerator68_of_l_eq_zero
    (a b c d e : k) :
    residualDoubleLoadWallFourNumerator68 a b c d e 0 =
      (512 : k) * residualDoubleFourHom68 b c d e := by
  simp only [residualDoubleLoadWallFourNumerator68]
  ring

theorem residualDoubleLoadWallZeroNumerator68_of_l_eq_zero
    (a b c d e : k) :
    residualDoubleLoadWallZeroNumerator68 a b c d e 0 =
      (576 : k) * residualDoubleZeroHom68 a b c d e := by
  simp only [residualDoubleLoadWallZeroNumerator68]
  ring

theorem ResidualDoubleLoadWallFace68.toTiedDouble_of_l_eq_zero
    (N G a b c d e l : k) (hl : l = 0)
    (hface : ResidualDoubleLoadWallFace68 N G a b c d e l) :
    SecondaryResidualTiedDoubleFace68 N G a b c d e where
  four := by
    have h := hface.four
    rw [hl, residualDoubleLoadWallFourNumerator68_of_l_eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  three := hface.three
  zero := by
    have h := hface.zero
    rw [hl, residualDoubleLoadWallZeroNumerator68_of_l_eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  one := hface.one

end Max11DegreeRoutes
