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
