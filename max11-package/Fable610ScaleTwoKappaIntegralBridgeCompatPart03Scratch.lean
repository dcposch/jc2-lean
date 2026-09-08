import Fable610ScaleTwoKappaIntegralBridgeCompatPart01Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- Exact denominator clearing for the decic `z¹` coordinate on the
ninth-power face. -/
theorem terminalDepressedW610_eq_cleared
    (h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    terminalDepressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3
        b2 b1 =
      (40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
          144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
          3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
          93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
          1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44) /
        (5038848 * h ^ 45) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h5038848 : (5038848 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [terminalDepressedW610, sexticDepressionR610, sexticDepressionR68]
  have hrewrite :
      -10 * (a5 / (6 * h ^ 5)) ^ 9 +
          9 * (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 8 -
        8 * (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) ^ 7 +
          7 * (b7 / h ^ 7) * (a5 / (6 * h ^ 5)) ^ 6 -
        6 * (b6 / h ^ 6) * (a5 / (6 * h ^ 5)) ^ 5 +
          5 * (b5 / h ^ 5) * (a5 / (6 * h ^ 5)) ^ 4 -
        4 * (b4 / h ^ 4) * (a5 / (6 * h ^ 5)) ^ 3 +
          3 * (b3 / h ^ 3) * (a5 / (6 * h ^ 5)) ^ 2 -
        2 * (b2 / h ^ 2) * (a5 / (6 * h ^ 5)) + b1 / h =
        (40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
            144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
            3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
            93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
            1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44) /
          (5038848 * h ^ 45) := by
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh45, h5038848]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh45, h5038848]
    ring
  exact hrewrite

end BridgeKappaDepression610

end Max11DegreeRoutes
