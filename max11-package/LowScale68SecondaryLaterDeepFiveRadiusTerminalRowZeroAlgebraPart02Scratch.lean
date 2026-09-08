import LowScale68SecondaryLaterDeepFiveRadiusTerminalRowZeroAlgebraPart01Scratch

/-! # Terminal row-zero algebra on `2g = 5n`, `h = 5n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusTerminalRowZeroAlgebra68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 6000000 in
theorem fiveRadiusTerminalRowZeroCore68_coeff
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 0) (he : e.natDegree ≤ n) :
    (fiveRadiusTerminalRowZeroCore68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (8 / 27 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) * e.coeff n) -
          A.coeff (2 * n) * c.coeff (4 * n - g) * d.coeff 0 +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
  have h1 := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) n (2 * n) (by omega) hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + n + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi1] at h1
  have h1' : (A * derivative A * B * e).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) *
        B.coeff (3 * n - g) * e.coeff n * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  have h2 := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) 0 (2 * n) (by omega) hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + 0 + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative A * c * d).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) *
        c.coeff (4 * n - g) * d.coeff 0 * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * n - g) (4 * n - g) (4 * n - g) (2 * n) (by omega)
    hB hc hc hA
  have hi3 : (3 * n - g) + (4 * n - g) + (4 * n - g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (derivative A * B * c ^ 2).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h3
  simp only [fiveRadiusTerminalRowZeroCore68, coeff_smul, coeff_add,
    coeff_sub, smul_eq_mul, h1', h2', h3']
  push_cast
  ring

theorem fiveRadiusTerminalEqualityScalarSelector68_rowZero_impossible
    (a b c d e : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hselector : FiveRadiusTerminalEqualityScalarSelector68 a b c d e)
    (hzero : -a * b * e - a * c * d + b * c ^ 2 = 0) : False := by
  rcases hselector.cases with hleft | hright
  · have h := hzero
    rw [hleft.1, hleft.2.1] at h
    have heq := hleft.2.2
    have hprod : a * b ^ 3 = 0 := by
      linear_combination (-9 : k) * h - a * b * heq
    exact (mul_ne_zero ha (pow_ne_zero 3 hb)) hprod
  · have hc := hright.1
    have hdisc := hright.2.1
    have hd := hright.2.2.1
    have he := hright.2.2.2
    have hprod : (16 : k) * a * b ^ 3 = 0 := by
      linear_combination
        (18 : k) * hzero + (a * b) * he + (3 * a) * hd -
          (18 * b) * hdisc
    have h16 : (16 : k) ≠ 0 := by norm_num
    exact (mul_ne_zero (mul_ne_zero h16 ha) (pow_ne_zero 3 hb)) hprod

end LaterDeepFiveRadiusTerminalRowZeroAlgebra68
end Max11DegreeRoutes
