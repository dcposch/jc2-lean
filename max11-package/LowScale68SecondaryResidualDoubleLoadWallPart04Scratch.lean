import LowScale68SecondaryResidualDoubleLoadWallPart03Scratch

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
