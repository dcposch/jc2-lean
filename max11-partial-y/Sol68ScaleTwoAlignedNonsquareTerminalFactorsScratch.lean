import LowScale68ScaleTwoAlignedNonsquareTerminalLastRow

/-! # Explicit terminal quotient factors one order below the cubic core -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

section QuotientFactorAlgebra68

variable {F : Type*} [Field F] [CharZero F]

/-- Exact quotient formulas after writing the two cubic-core defects as
`3t-r²=HX` and `27v-r³=HY`. -/
theorem terminalQuotientFactors_of_cubicDefects_68
    (H r t v p0 p1 p2 gamma epsilon X Yd b d w phi : F) (hH : H ≠ 0)
    (ht : 3 * t - r ^ 2 = H * X) (hv : 27 * v - r ^ 3 = H * Yd)
    (hb : v - (2 / 3 : F) * t * r + (5 / 27 : F) * r ^ 3 = H * b)
    (hd : H ^ 2 * p1 - (1 / 3 : F) * H * p2 * r +
        (1 / 12 : F) * v * r ^ 2 - (1 / 54 : F) * t * r ^ 3 +
        (1 / 324 : F) * r ^ 5 = H * d)
    (hw : (4 / 9 : F) *
          (H * p2 - (1 / 2 : F) * v * r + (1 / 6 : F) * t * r ^ 2 -
            (5 / 144 : F) * r ^ 4) -
        (4 / 27 : F) * (t - (5 / 12 : F) * r ^ 2) ^ 2 +
        (2 / 3 : F) * gamma * H ^ 2 = H * w)
    (hphi : -(8 / 27 : F) *
          (v - (2 / 3 : F) * t * r + (5 / 27 : F) * r ^ 3) ^ 2 +
        (8 / 3 : F) *
          (H ^ 3 * p0 - (1 / 6 : F) * H ^ 2 * p1 * r +
            (1 / 36 : F) * H * p2 * r ^ 2 -
            (1 / 216 : F) * v * r ^ 3 +
            (1 / 1296 : F) * t * r ^ 4 - (5 / 46656 : F) * r ^ 6) +
        2 * epsilon * H ^ 3 +
        (40 / 81 : F) * (t - (5 / 12 : F) * r ^ 2) ^ 3 -
        (16 / 9 : F) * (t - (5 / 12 : F) * r ^ 2) *
          (H * p2 - (1 / 2 : F) * v * r +
            (1 / 6 : F) * t * r ^ 2 - (5 / 144 : F) * r ^ 4) -
        (4 / 3 : F) * gamma * (t - (5 / 12 : F) * r ^ 2) * H ^ 2 =
          H * phi) :
    b = (Yd - 6 * r * X) / 27 ∧
    d = H * p1 - (1 / 3 : F) * r * p2 + (1 / 324 : F) * r ^ 2 * Yd -
        (1 / 162 : F) * r ^ 3 * X ∧
    w = (4 / 9 : F) * p2 - (2 / 243 : F) * r * Yd +
        (8 / 243 : F) * r ^ 2 * X +
        H * (-(4 / 243 : F) * X ^ 2 + (2 / 3 : F) * gamma) ∧
    phi = (2 / 9 : F) * r ^ 2 * p2 - (7 / 2187 : F) * r ^ 3 * Yd +
        (8 / 729 : F) * r ^ 4 * X +
        H * (-(134 / 2187 : F) * r ^ 2 * X ^ 2 +
          (104 / 6561 : F) * r * X * Yd + (1 / 9 : F) * r ^ 2 * gamma -
          (8 / 19683 : F) * Yd ^ 2 - (4 / 9 : F) * r * p1 -
          (16 / 27 : F) * X * p2) +
        H ^ 2 * ((40 / 2187 : F) * X ^ 3 -
          (4 / 9 : F) * X * gamma + (8 / 3 : F) * p0 + 2 * epsilon) := by
  have ht' : t = (r ^ 2 + H * X) / 3 := by
    linear_combination (1 / 3 : F) * ht
  have hv' : v = (r ^ 3 + H * Yd) / 27 := by
    linear_combination (1 / 27 : F) * hv
  have hb' : H * b = H * ((Yd - 6 * r * X) / 27) := by
    rw [← hb, ht', hv']
    ring
  have hd' : H * d = H * (H * p1 - (1 / 3 : F) * r * p2 +
      (1 / 324 : F) * r ^ 2 * Yd - (1 / 162 : F) * r ^ 3 * X) := by
    rw [← hd, ht', hv']
    ring
  have hw' : H * w = H * ((4 / 9 : F) * p2 - (2 / 243 : F) * r * Yd +
      (8 / 243 : F) * r ^ 2 * X +
      H * (-(4 / 243 : F) * X ^ 2 + (2 / 3 : F) * gamma)) := by
    rw [← hw, ht', hv']
    ring
  have hphi' : H * phi = H *
      ((2 / 9 : F) * r ^ 2 * p2 - (7 / 2187 : F) * r ^ 3 * Yd +
        (8 / 729 : F) * r ^ 4 * X +
        H * (-(134 / 2187 : F) * r ^ 2 * X ^ 2 +
          (104 / 6561 : F) * r * X * Yd + (1 / 9 : F) * r ^ 2 * gamma -
          (8 / 19683 : F) * Yd ^ 2 - (4 / 9 : F) * r * p1 -
          (16 / 27 : F) * X * p2) +
        H ^ 2 * ((40 / 2187 : F) * X ^ 3 -
          (4 / 9 : F) * X * gamma + (8 / 3 : F) * p0 + 2 * epsilon)) := by
    rw [← hphi, ht', hv']
    ring
  exact ⟨mul_left_cancel₀ hH hb', mul_left_cancel₀ hH hd',
    mul_left_cancel₀ hH hw', mul_left_cancel₀ hH hphi'⟩

/-- The terminal quotient face factors into two explicit transverse
components, apart from the desired `r=0` descent. -/
theorem terminalQuotientFace_cubicDefect_split_68
    (r X Yd p2 b d w phi : F)
    (hb : b = (Yd - 6 * r * X) / 27)
    (hd : d = -(1 / 3 : F) * r * p2 + (1 / 324 : F) * r ^ 2 * Yd -
      (1 / 162 : F) * r ^ 3 * X)
    (hw : w = (4 / 9 : F) * p2 - (2 / 243 : F) * r * Yd +
      (8 / 243 : F) * r ^ 2 * X)
    (hphi : phi = (2 / 9 : F) * r ^ 2 * p2 -
      (7 / 2187 : F) * r ^ 3 * Yd + (8 / 729 : F) * r ^ 4 * X)
    (hI4 : b * phi + 6 * w * d = 0) :
    r = 0 ∨
      9 * r ^ 2 * X - 2 * r * Yd + 81 * p2 = 0 ∨
      3 * r ^ 2 * X - r * Yd + 81 * p2 = 0 := by
  have hfac : r *
      (9 * r ^ 2 * X - 2 * r * Yd + 81 * p2) *
      (3 * r ^ 2 * X - r * Yd + 81 * p2) = 0 := by
    rw [hb, hd, hw, hphi] at hI4
    linear_combination (-59049 / 8 : F) * hI4
  rcases mul_eq_zero.mp hfac with hleftprod | hright
  · rcases mul_eq_zero.mp hleftprod with hr | hleft
    · exact Or.inl hr
    · exact Or.inr (Or.inl hleft)
  · exact Or.inr (Or.inr hright)

end QuotientFactorAlgebra68

end Max11DegreeRoutes
