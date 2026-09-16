import LowScale68SecondaryResidualLoadZeroEndgame
import LowScale68SecondaryFirstLoadWallRemainder

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

/-- Homogeneous residual-double I4 numerator `-b^3 + 9 b e + 9 c d`. -/
def residualDoubleFourHom68 (b c d e : k) : k :=
  -b ^ 3 + 9 * b * e + 9 * c * d

/-- Homogeneous residual-double I3 numerator. -/
def residualDoubleThreeHom68 (a b c d e : k) : k :=
  -a * b * d - b ^ 2 * c + 3 * c * e

/-- Homogeneous residual-double row-zero numerator. -/
def residualDoubleZeroHom68 (a b c d e : k) : k :=
  -a * b * e - a * c * d + b * c ^ 2

/-- Mixed I4 numerator at index `8n`: `35 l a^4 + 512 four_hom`. -/
def residualDoubleLoadWallFourNumerator68 (a b c d e l : k) : k :=
  (35 : k) * l * a ^ 4 + (512 : k) * residualDoubleFourHom68 b c d e

/-- Mixed row-zero numerator after dropping the nonzero factor `n a`
from the polynomial coefficient, then restoring the cancelled `a` in the
homogeneous summand: `35 l a^5 + 576 zero_hom`. -/
def residualDoubleLoadWallZeroNumerator68 (a b c d e l : k) : k :=
  (35 : k) * l * a ^ 5 + (576 : k) * residualDoubleZeroHom68 a b c d e

/-- Mixed row-two numerator after dropping `N/324`. -/
def residualDoubleLoadWallTwoNumerator68 (a b c d e l : k) : k :=
  (35 : k) * l * a ^ 5 + (96 : k) * a * b ^ 3 +
    (2016 : k) * a * b * e + (2016 : k) * a * c * d -
    (2880 : k) * b * c ^ 2

/-- Plan §3.5.G mixed I4 scalar. -/
def residualDoubleLoadWallFourScalar68 (a b c d e l : k) : k :=
  ((35 : k) * l * a ^ 4 - (512 : k) * b ^ 3 +
    (4608 : k) * b * e + (4608 : k) * c * d) / (1728 : k)

/-- Mixed row-two scalar at index `10n-1`. -/
def residualDoubleLoadWallTwoScalar68 (N a b c d e l : k) : k :=
  N * residualDoubleLoadWallTwoNumerator68 a b c d e l / (324 : k)

/-- Mixed row-zero scalar at index `12n-1`. -/
def residualDoubleLoadWallZeroScalar68 (N a b c d e l : k) : k :=
  N * a * residualDoubleLoadWallZeroNumerator68 a b c d e l / (1944 : k)

/-- `l`-free I4/row-zero combination. -/
def residualDoubleLoadWallFourZeroPoly68 (a b c d e : k) : k :=
  (8 : k) * a * b ^ 3 - (81 : k) * a * b * e -
    (81 : k) * a * c * d + (9 : k) * b * c ^ 2

/-- `l`-free I4/row-two combination. -/
def residualDoubleLoadWallFourTwoPoly68 (a b c d e : k) : k :=
  (19 : k) * a * b ^ 3 - (81 : k) * a * b * e -
    (81 : k) * a * c * d - (90 : k) * b * c ^ 2

/-- All five mixed leading equations on `3G = N` with residual gap `2G`. -/
structure ResidualDoubleLoadWallFace68 (N G a b c d e l : k) : Prop where
  four : residualDoubleLoadWallFourNumerator68 a b c d e l = 0
  three : residualDoubleThreeHom68 a b c d e = 0
  two : residualDoubleLoadWallTwoNumerator68 a b c d e l = 0
  one : 3 * a ^ 2 * b * G * d - 10 * a ^ 2 * b * N * d +
    2 * a * b ^ 2 * N * c - 9 * a * G * c * e +
    30 * a * N * c * e + 3 * G * c ^ 3 - 12 * N * c ^ 3 = 0
  zero : residualDoubleLoadWallZeroNumerator68 a b c d e l = 0

theorem residualDoubleLoadWallFourScalar68_eq_numerator
    (a b c d e l : k) :
    residualDoubleLoadWallFourScalar68 a b c d e l =
      residualDoubleLoadWallFourNumerator68 a b c d e l / (1728 : k) := by
  simp only [residualDoubleLoadWallFourScalar68,
    residualDoubleLoadWallFourNumerator68, residualDoubleFourHom68]
  ring

theorem residualDoubleLoadWallFourScalar68_eq_hom_add_load
    (a b c d e l : k) :
    residualDoubleLoadWallFourScalar68 a b c d e l =
      (35 / 1728 : k) * l * a ^ 4 +
        (8 / 27 : k) * residualDoubleFourHom68 b c d e := by
  simp only [residualDoubleLoadWallFourScalar68, residualDoubleFourHom68]
  ring

theorem residualDoubleLoadWallTwoScalar68_eq_hom_add_load
    (N a b c d e l : k) :
    residualDoubleLoadWallTwoScalar68 N a b c d e l =
      (8 / 27 : k) * N *
          (a * b ^ 3 + (21 : k) * a * b * e +
            (21 : k) * a * c * d - (30 : k) * b * c ^ 2) +
        (35 / 324 : k) * N * l * a ^ 5 := by
  simp only [residualDoubleLoadWallTwoScalar68,
    residualDoubleLoadWallTwoNumerator68]
  ring

end Max11DegreeRoutes
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

/-- Residual first-face support makes the mixed wall empty. -/
theorem residualDoubleLoadWallFace68_impossible
    (N G a b c d e l : k) (ha : a ≠ 0) (hN : N ≠ 0)
    (hsupport : b ≠ 0 ∨ c ≠ 0) (hwall : (3 : k) * G = N)
    (hface : ResidualDoubleLoadWallFace68 N G a b c d e l) : False := by
  obtain ⟨_, hb0, hc0⟩ :=
    residualDoubleLoadWallFace68_classify N G a b c d e l ha hN hwall hface
  rcases hsupport with hb | hc
  · exact hb hb0
  · exact hc hc0

theorem residualDoubleLoadWallFace68_classify_of_three_mul_gap_eq_radius
    (n g : ℕ) (a b c d e l : k) (ha : a ≠ 0) (hn : 0 < n)
    (hwall : 3 * g = n)
    (hface : ResidualDoubleLoadWallFace68 (n : k) (g : k) a b c d e l) :
    l = 0 ∧ b = 0 ∧ c = 0 := by
  refine residualDoubleLoadWallFace68_classify (n : k) (g : k)
    a b c d e l ha ?hN ?hk hface
  · exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  · exact_mod_cast hwall

theorem residualDoubleLoadWallFace68_impossible_of_three_mul_gap_eq_radius
    (n g : ℕ) (a b c d e l : k) (ha : a ≠ 0) (hn : 0 < n)
    (hsupport : b ≠ 0 ∨ c ≠ 0) (hwall : 3 * g = n)
    (hface : ResidualDoubleLoadWallFace68 (n : k) (g : k) a b c d e l) :
    False := by
  obtain ⟨_, hb0, hc0⟩ :=
    residualDoubleLoadWallFace68_classify_of_three_mul_gap_eq_radius
      n g a b c d e l ha hn hwall hface
  rcases hsupport with hb | hc
  · exact hb hb0
  · exact hc hc0

theorem residualDoubleLoadWall_twoGap
    (n g : ℕ) (hg : 0 < g) (hwall : 3 * g = n) : 2 * g < n := by
  omega

theorem residualDoubleLoadWall_fourIndex
    (n g : ℕ) (hwall : 3 * g = n) : 9 * n - 3 * g = 8 * n := by
  omega

theorem residualDoubleLoadWall_threeIndex
    (n g : ℕ) (hwall : 3 * g = n) : 10 * n - 3 * g = 9 * n := by
  omega

theorem residualDoubleLoadWall_twoIndex
    (n g : ℕ) (hwall : 3 * g = n) : 11 * n - 3 * g - 1 = 10 * n - 1 := by
  omega

theorem residualDoubleLoadWall_oneIndex
    (n g : ℕ) (hwall : 3 * g = n) : 12 * n - 3 * g - 1 = 11 * n - 1 := by
  omega

theorem residualDoubleLoadWall_zeroIndex
    (n g : ℕ) (hwall : 3 * g = n) : 13 * n - 3 * g - 1 = 12 * n - 1 := by
  omega

/-- Unique `l A^4` summand of the quartic-invariant load. -/
def secondaryLoadInvariantFourLCorePolynomial68 (l : k) (A : k[X]) : k[X] :=
  (35 / 1728 * l : k) • A ^ 4

/-- Complementary quartic-invariant load, every summand strictly below `8n`
on this wall. -/
def secondaryLoadInvariantFourRestPolynomial68
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X]) : k[X] :=
  zeta • A + (2 * epsilon : k) • B +
    (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
    (4 * gamma : k) • D - (4 / 3 * gamma : k) • (A * B) +
    (5 * beta : k) • e + (5 / 6 * beta : k) • (A * c) -
    (5 / 12 * beta : k) • B ^ 2 +
    (5 / 72 * beta : k) • A ^ 3 +
    (7 / 24 * l : k) • (A ^ 2 * c) -
    (35 / 72 * l : k) • (A * B ^ 2) +
    (7 / 6 * l : k) • (A * e) +
    (7 / 6 * l : k) • (B * D) + (7 / 12 * l : k) • c ^ 2

theorem secondaryLoadInvariantFourPolynomial68_eq_core_add_rest
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X]) :
    secondaryLoadInvariantFourPolynomial68 l beta gamma delta epsilon zeta
        A B c D e =
      secondaryLoadInvariantFourLCorePolynomial68 l A +
        secondaryLoadInvariantFourRestPolynomial68 l beta gamma delta
          epsilon zeta A B c D e := by
  simp only [secondaryLoadInvariantFourPolynomial68,
    secondaryLoadInvariantFourLCorePolynomial68,
    secondaryLoadInvariantFourRestPolynomial68, Polynomial.smul_eq_C_mul]
  ring

end Max11DegreeRoutes
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

/-! ## Wall index arithmetic -/

/-! ## I4 load core versus remainder -/

set_option maxHeartbeats 3000000 in
theorem secondaryLoadInvariantFourLCorePolynomial68_coeff_wall
    (l : k) (A : k[X]) (n : ℕ) (hA : A.natDegree ≤ 2 * n) :
    (secondaryLoadInvariantFourLCorePolynomial68 l A).coeff (8 * n) =
      (35 / 1728 : k) * l * A.coeff (2 * n) ^ 4 := by
  have hA4 : (A ^ 4).coeff (8 * n) = A.coeff (2 * n) ^ 4 := by
    have h := coeff_pow_at_bound68 A (2 * n) 4 hA
    have hi : 4 * (2 * n) = 8 * n := by omega
    simpa only [hi] using h
  rw [secondaryLoadInvariantFourLCorePolynomial68, coeff_smul, hA4,
    smul_eq_mul]

set_option maxHeartbeats 4000000 in
theorem secondaryLoadInvariantFourRestPolynomial68_degree_lt_wall
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantFourRestPolynomial68 l beta gamma delta epsilon
      zeta A B c D e).natDegree < 8 * n := by
  simp only [secondaryLoadInvariantFourRestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 4000000 in
/-- Mixed I4 coefficient at the collided index `8n = 9n-3g`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_residualDoubleLoadWall
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (8 * n) =
      residualDoubleLoadWallFourScalar68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (e.coeff (6 * n - 2 * g)) l := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have htwo : 2 * g < n := residualDoubleLoadWall_twoGap n g hg hwall
  have hidx : 9 * n - 3 * g = 8 * n :=
    residualDoubleLoadWall_fourIndex n g hwall
  have hhom := secondaryResidualInvariantFourPolynomial68_coeff_double_of_twoGap
    B c d e n g hg htwo hB hc hd he
  have hcore := secondaryLoadInvariantFourLCorePolynomial68_coeff_wall
    l A n hA
  have hrest := secondaryLoadInvariantFourRestPolynomial68_degree_lt_wall
    l beta gamma delta epsilon zeta A B c D e n g hg hwall
    hA hB hc hD he
  rw [← hidx, cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    secondaryLoadInvariantFourPolynomial68_eq_core_add_rest,
    coeff_add, coeff_add, hhom, hidx, hcore,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero]
  simp only [residualDoubleLoadWallFourScalar68]
  ring

end Max11DegreeRoutes
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

/-! ## Wall index arithmetic -/

/-! ## I4 load core versus remainder -/

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualDoubleLoadWall
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (9 * n) =
      (8 / 9 : k) * residualDoubleThreeHom68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (e.coeff (6 * n - 2 * g)) := by
  have htwo : 2 * g < n := residualDoubleLoadWall_twoGap n g hg hwall
  have hidx : 10 * n - 3 * g = 9 * n :=
    residualDoubleLoadWall_threeIndex n g hwall
  rw [← hidx, cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_twoGap
    l beta gamma delta epsilon zeta A B c d e n g hg htwo
    hA hB hc hd he]
  simp only [residualDoubleThreeHom68]
  ring

private theorem natDegree_mul_derivative_le_add_sub68
    (p q : k[X]) (u v : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hsum : p.natDegree + (derivative q).natDegree ≤ u + (v - 1) :=
    Nat.add_le_add hp hd
  have hidx : u + (v - 1) = u + v - 1 := by omega
  exact natDegree_mul_le.trans (hidx ▸ hsum)

private theorem natDegree_mul_derivative_lt_of_add_sub68
    (p q : k[X]) (u v bound : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (huv : u + v - 1 < bound) :
    (p * derivative q).natDegree < bound :=
  (natDegree_mul_derivative_le_add_sub68 p q u v hv hp hq).trans_lt huv

private theorem natDegree_smul_lt68 (r : k) {p : k[X]} {n : ℕ}
    (hp : p.natDegree < n) : (r • p).natDegree < n :=
  (natDegree_smul_le r p).trans_lt hp

private theorem natDegree_add_lt68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p + q).natDegree < n :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem natDegree_sub_lt68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p - q).natDegree < n :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

set_option maxHeartbeats 2000000 in
theorem cubicLoadSRestPolynomial68_degree_le_wall
    (l alpha beta delta : k) (A B c : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadSRestPolynomial68 l alpha beta delta A B c).natDegree ≤
      4 * n - g := by
  simp only [cubicLoadSRestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadURestPolynomial68_degree_le_wall
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
      A B c D e).natDegree ≤ 6 * n - g := by
  simp only [cubicLoadURestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicERestPolynomial68_degree_le_wall
    (A c e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicERestPolynomial68 A c e).natDegree ≤ 6 * n - g := by
  simp only [cubicERestPolynomial68]
  compute_degree
  omega

end Max11DegreeRoutes
