import LowScale810ScaleTwoThirdFace

/-! # Scale-two fourth face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the third face supplies the degree-`14` integral
`Q - (5/4) B - (9/8) L A` and the local jet `h⁴ ∣ p₇`, `h² ∣ q₈`,
`h⁶ ∣ q₉`.  The next Keller coefficient is the degree-`13` Jacobian
row.  After the same octic depression that kills `z⁷`, that row is
`10 C' + 9 L B' + 8 P A' - 6 A P' - 8 R' = 0`.  The resulting first
integral clears to a polynomial defect `U` of weight twenty-eight.

Evaluating the second, third, and fourth defects together at the root
of `h` forces the finite initial jet `h⁵ ∣ p₇`, `h² ∣ p₆`, `h⁴ ∣ q₈`,
`h ∣ q₇`, and `h⁷ ∣ q₉`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The fourth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  It is the source of the first mixed octic/decic
`z⁴`/`z⁶` defect after the degree-`14` integral. -/
theorem fourthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 7).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 6).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 5).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 4).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 6).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 7).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 8).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 9).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 10).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 13) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (13 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 13 :
      Finset (ℕ × ℕ)) =
      ({(0, 13), (1, 12), (2, 11), (3, 10), (4, 9), (5, 8), (6, 7),
        (7, 6), (8, 5), (9, 4), (10, 3), (11, 2), (12, 1),
        (13, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  rw [hC8, hC9, hC10, hC7, hC6, hC5, hC4]
  linear_combination hcoeff

/-! ## Octic `z⁴` and decic `z⁶` coordinates -/

section Depression810Fourth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed octic `z⁴` coefficient. -/
def depressedC810 (h r a7 a6 a5 a4 : F) : F :=
  depressedR68 h r a7 a6 a5 a4

/-- Depressed decic `z⁶` coefficient. -/
def depressedR810 (h r b9 b8 b7 b6 : F) : F :=
  210 * r ^ 4 - 84 * (b9 / h ^ 9) * r ^ 3 +
    28 * (b8 / h ^ 8) * r ^ 2 - 7 * (b7 / h ^ 7) * r + b6 / h ^ 6

/-- First residual of the degree-`13` row. -/
def gammaResidual810 (L A B C0 P R : F) : F :=
  R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
    (9 / 8 : F) * L * B + alphaResidual810 A P * A)

/-- Polynomial numerator of `2048 h²⁸ γ` on the ninth-power face. -/
def localClearedFourthDefect810
    (h a7 a6 a5 a4 b8 b7 b6 : F[X]) (lambda : F) : F[X] :=
  -(2560 : F[X]) * a4 * h ^ 24 +
    (1600 : F[X]) * a5 * a7 * h ^ 16 +
    (576 : F[X]) * Polynomial.C lambda * a5 * h ^ 23 +
    (2240 : F[X]) * a6 ^ 2 * h ^ 16 -
    (1120 : F[X]) * a6 * a7 ^ 2 * h ^ 8 -
    (1008 : F[X]) * Polynomial.C lambda * a6 * a7 * h ^ 15 -
    (2048 : F[X]) * a6 * b8 * h ^ 14 -
    (385 : F[X]) * a7 ^ 4 +
    (462 : F[X]) * Polynomial.C lambda * a7 ^ 3 * h ^ 7 +
    (1792 : F[X]) * a7 ^ 2 * b8 * h ^ 6 -
    (1792 : F[X]) * a7 * b7 * h ^ 14 +
    (2048 : F[X]) * b6 * h ^ 22

theorem coeff_depressedOctic68_four
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 4 = R := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the octic `z⁴` coordinate. -/
theorem depressedC810_eq_cleared
    (h a7 a6 a5 a4 : F) (hh : h ≠ 0) :
    depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
      (2048 * a4 * h ^ 24 - 1280 * a5 * a7 * h ^ 16 +
          480 * a6 * a7 ^ 2 * h ^ 8 - 105 * a7 ^ 4) /
        (2048 * h ^ 28) := by
  simp only [depressedC810, depressedR68, octicDepressionR810]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z⁸` coordinate on the
ninth-power face. -/
theorem depressedP810_eq_cleared_ninthPower
    (h a7 b9 b8 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    depressedP810 h (octicDepressionR810 h a7) b9 b8 =
      (-45 * a7 ^ 2 + 18 * lambda * a7 * h ^ 7 + 64 * b8 * h ^ 6) /
        (64 * h ^ 14) := by
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hb9 : 4 * b9 = 5 * a7 * h ^ 2 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedP810, octicDepressionR810]
  have hrewrite :
      45 * (a7 / (8 * h ^ 7)) ^ 2 -
          9 * (b9 / h ^ 9) * (a7 / (8 * h ^ 7)) + b8 / h ^ 8 =
        (-45 * a7 ^ 2 + 18 * lambda * a7 * h ^ 7 + 64 * b8 * h ^ 6) /
          (64 * h ^ 14) := by
    field_simp [hh, h8, hh2, hh7, hh8pow, hh9, hh14, h64]
    have hb9' :
        b9 = (5 * a7 * h ^ 2 - lambda * h ^ 9) / 4 := by
      have h4 : (4 : F) ≠ 0 := by norm_num
      field_simp [h4]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h8, hh2, hh7, hh8pow, hh9, hh14, h64]
    ring
  exact hrewrite

/-- Exact denominator clearing for the decic `z⁶` coordinate on the
ninth-power face. -/
theorem depressedR810_eq_cleared
    (h a7 b9 b8 b7 b6 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 =
      (-315 * a7 ^ 4 + 84 * lambda * a7 ^ 3 * h ^ 7 +
          896 * a7 ^ 2 * b8 * h ^ 6 - 1792 * a7 * b7 * h ^ 14 +
          2048 * b6 * h ^ 22) /
        (2048 * h ^ 28) := by
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hb9 : 4 * b9 = 5 * a7 * h ^ 2 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedR810, octicDepressionR810]
  have hrewrite :
      210 * (a7 / (8 * h ^ 7)) ^ 4 -
          84 * (b9 / h ^ 9) * (a7 / (8 * h ^ 7)) ^ 3 +
        28 * (b8 / h ^ 8) * (a7 / (8 * h ^ 7)) ^ 2 -
          7 * (b7 / h ^ 7) * (a7 / (8 * h ^ 7)) + b6 / h ^ 6 =
        (-315 * a7 ^ 4 + 84 * lambda * a7 ^ 3 * h ^ 7 +
            896 * a7 ^ 2 * b8 * h ^ 6 - 1792 * a7 * b7 * h ^ 14 +
            2048 * b6 * h ^ 22) /
          (2048 * h ^ 28) := by
    field_simp [hh, h8, hh2, hh6, hh7, hh8pow, hh9, hh28, h2048]
    have hb9' :
        b9 = (5 * a7 * h ^ 2 - lambda * h ^ 9) / 4 := by
      have h4 : (4 : F) ≠ 0 := by norm_num
      field_simp [h4]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h8, hh2, hh6, hh7, hh8pow, hh9, hh28, h2048]
    ring
  exact hrewrite

set_option maxHeartbeats 4000000 in
/-- Clearing the first integral
`R - (5/4) C - (5/32) A² - (9/8) L B - α A` against `h²⁸` on the
ninth-power face. -/
theorem fourthDefect_eq_clearedGamma810
    (h a7 a6 a5 a4 b9 b8 b7 b6 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (2048 : F) * h ^ 28 *
        gammaResidual810
          (depressedL810 h (octicDepressionR810 h a7) b9)
          (depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
          (depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6) =
      -(2560 : F) * a4 * h ^ 24 + (1600 : F) * a5 * a7 * h ^ 16 +
        (576 : F) * lambda * a5 * h ^ 23 +
        (2240 : F) * a6 ^ 2 * h ^ 16 -
        (1120 : F) * a6 * a7 ^ 2 * h ^ 8 -
        (1008 : F) * lambda * a6 * a7 * h ^ 15 -
        (2048 : F) * a6 * b8 * h ^ 14 - (385 : F) * a7 ^ 4 +
        (462 : F) * lambda * a7 ^ 3 * h ^ 7 +
        (1792 : F) * a7 ^ 2 * b8 * h ^ 6 -
        (1792 : F) * a7 * b7 * h ^ 14 + (2048 : F) * b6 * h ^ 22 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hL :
      depressedL810 h (octicDepressionR810 h a7) b9 = -lambda / 4 :=
    depressedL810_eq_of_ninthPower h a7 b9 lambda hh hN
  have hA :
      depressedA810 h (octicDepressionR810 h a7) a7 a6 =
        (16 * a6 * h ^ 8 - 7 * a7 ^ 2) / (16 * h ^ 14) :=
    depressedA810_eq_cleared h a7 a6 hh
  have hB :
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
        (32 * a5 * h ^ 16 - 24 * a6 * a7 * h ^ 8 + 7 * a7 ^ 3) /
          (32 * h ^ 21) :=
    depressedB810_eq_cleared h a7 a6 a5 hh
  have hC :
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
        (2048 * a4 * h ^ 24 - 1280 * a5 * a7 * h ^ 16 +
            480 * a6 * a7 ^ 2 * h ^ 8 - 105 * a7 ^ 4) /
          (2048 * h ^ 28) :=
    depressedC810_eq_cleared h a7 a6 a5 a4 hh
  have hP :
      depressedP810 h (octicDepressionR810 h a7) b9 b8 =
        (-45 * a7 ^ 2 + 18 * lambda * a7 * h ^ 7 + 64 * b8 * h ^ 6) /
          (64 * h ^ 14) :=
    depressedP810_eq_cleared_ninthPower h a7 b9 b8 lambda hh hN
  have hR :
      depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 =
        (-315 * a7 ^ 4 + 84 * lambda * a7 ^ 3 * h ^ 7 +
            896 * a7 ^ 2 * b8 * h ^ 6 - 1792 * a7 * b7 * h ^ 14 +
            2048 * b6 * h ^ 22) /
          (2048 * h ^ 28) :=
    depressedR810_eq_cleared h a7 b9 b8 b7 b6 lambda hh hN
  have h2048R :
      (2048 : F) * h ^ 28 *
          depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 =
        -(315 : F) * a7 ^ 4 + (84 : F) * lambda * a7 ^ 3 * h ^ 7 +
          (896 : F) * a7 ^ 2 * b8 * h ^ 6 -
          (1792 : F) * a7 * b7 * h ^ 14 + (2048 : F) * b6 * h ^ 22 := by
    rw [hR]
    field_simp [hh, h2048, hh28]
    try ring
  have h2560C :
      (2560 : F) * h ^ 28 *
          depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
        (2560 : F) * a4 * h ^ 24 - (1600 : F) * a5 * a7 * h ^ 16 +
          (600 : F) * a6 * a7 ^ 2 * h ^ 8 - (525 / 4 : F) * a7 ^ 4 := by
    rw [hC]
    field_simp [hh, h2048, hh28]
    try ring
  have h576B :
      (576 : F) * lambda * h ^ 28 *
          depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
        (576 : F) * lambda * a5 * h ^ 23 -
          (432 : F) * lambda * a6 * a7 * h ^ 15 +
          (126 : F) * lambda * a7 ^ 3 * h ^ 7 := by
    rw [hB]
    field_simp [hh, h32, hh21, hh28]
    try ring
  have h16A :
      (16 : F) * h ^ 14 *
          depressedA810 h (octicDepressionR810 h a7) a7 a6 =
        (16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2 := by
    rw [hA]
    field_simp [hh, h16, hh14]
    try ring
  have h64P :
      (64 : F) * h ^ 14 *
          depressedP810 h (octicDepressionR810 h a7) b9 b8 =
        -(45 : F) * a7 ^ 2 + (18 : F) * lambda * a7 * h ^ 7 +
          (64 : F) * b8 * h ^ 6 := by
    rw [hP]
    field_simp [hh, h64, hh14]
    try ring
  have h2048AP :
      (2048 : F) * h ^ 28 *
          (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
            depressedP810 h (octicDepressionR810 h a7) b9 b8) =
        (2 : F) *
          ((16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2) *
            (-(45 : F) * a7 ^ 2 + (18 : F) * lambda * a7 * h ^ 7 +
              (64 : F) * b8 * h ^ 6) := by
    have hscale :
        (2048 : F) * h ^ 28 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
              depressedP810 h (octicDepressionR810 h a7) b9 b8) =
          (2 : F) *
            ((16 : F) * h ^ 14 *
                depressedA810 h (octicDepressionR810 h a7) a7 a6) *
              ((64 : F) * h ^ 14 *
                depressedP810 h (octicDepressionR810 h a7) b9 b8) := by
      ring
    rw [hscale, h16A, h64P]
  have h2240A2 :
      (2240 : F) * h ^ 28 *
          (depressedA810 h (octicDepressionR810 h a7) a7 a6) ^ 2 =
        (70 / 8 : F) *
          ((16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2) ^ 2 := by
    have hscale :
        (2240 : F) * h ^ 28 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6) ^ 2 =
          (2240 / 256 : F) *
            ((16 : F) * h ^ 14 *
                depressedA810 h (octicDepressionR810 h a7) a7 a6) ^ 2 := by
      field_simp [hh, h16, hh14, hh28]
      ring
    have hfrac : (2240 / 256 : F) = (70 / 8 : F) := by ring
    rw [hscale, hfrac, h16A]
  have hdiff :
      (2048 : F) * h ^ 28 *
          gammaResidual810
            (depressedL810 h (octicDepressionR810 h a7) b9)
            (depressedA810 h (octicDepressionR810 h a7) a7 a6)
            (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
            (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
            (depressedP810 h (octicDepressionR810 h a7) b9 b8)
            (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6) =
        (2048 : F) * h ^ 28 *
            depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 -
          (2560 : F) * h ^ 28 *
            depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 +
          (576 : F) * lambda * h ^ 28 *
            depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 -
          (2048 : F) * h ^ 28 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
              depressedP810 h (octicDepressionR810 h a7) b9 b8) +
          (2240 : F) * h ^ 28 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6) ^ 2 := by
    simp only [gammaResidual810, alphaResidual810, hL]
    field_simp [h4, h8, h32]
    ring
  rw [hdiff, h2048R, h2560C, h576B, h2048AP, h2240A2]
  ring

end Depression810Fourth

/-! ## Degree-`13` depressed Jacobian coefficient -/

section DepressedRow810Fourth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`13` Jacobian coefficient is
exactly `10 C' + 9 L B' + 8 P A' - 6 A P' - 8 R'`. -/
theorem differentialJacobian_coeff_13_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 13 =
      (10 : F) * d (f.coeff 4) + (9 : F) * g.coeff 9 * d (f.coeff 5) +
        (8 : F) * g.coeff 8 * d (f.coeff 6) -
          (6 : F) * f.coeff 6 * d (g.coeff 8) -
          (8 : F) * d (g.coeff 6) := by
  have hfd_high : ∀ n, 7 ≤ n → (coefficientDeriv d f).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      simpa [hf7]
    · have : 8 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq8 | hlt8
      · subst n
        simpa [hf8, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hf_high n (by omega))
  have hgd_high : ∀ n, 10 ≤ n → g.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 10 < n + 1 := by omega
    simp [hg_high (n + 1) this]
  have hfd'_high : ∀ n, 8 ≤ n → f.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 8 < n + 1 := by omega
    simp [hf_high (n + 1) this]
  have hgd'_high : ∀ n, 9 ≤ n → (coefficientDeriv d g).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      exact hL
    · have : 10 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq10 | hlt10
      · subst n
        simpa [hg10, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hg_high n (by omega))
  have hmem49 : ((4, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (13 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem58 : ((5, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (13 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem67 : ((6, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (13 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem76 : ((7, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (13 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 13 =
        (10 : F) * d (f.coeff 4) +
          (9 : F) * g.coeff 9 * d (f.coeff 5) +
          (8 : F) * g.coeff 8 * d (f.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne45 : ((4, 9) : ℕ × ℕ) ≠ (5, 8) := by decide
    have hne46 : ((4, 9) : ℕ × ℕ) ≠ (6, 7) := by decide
    have hne56 : ((5, 8) : ℕ × ℕ) ≠ (6, 7) := by decide
    have hsubset : ({(4, 9), (5, 8), (6, 7)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (13 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b
        exact hmem49
      · subst b
        exact hmem58
      · subst b
        exact hmem67
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (13 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(4, 9), (5, 8), (6, 7)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 13 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne49 : b ≠ (4, 9) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne58 : b ≠ (5, 8) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      have hne67 : b ≠ (6, 7) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 7 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne49
          ext
          · exact h4
          · omega
        have hne5 : b.1 ≠ 5 := by
          intro h5
          apply hne58
          ext
          · exact h5
          · omega
        have hne6 : b.1 ≠ 6 := by
          intro h6
          apply hne67
          ext
          · exact h6
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(4, 9), (5, 8), (6, 7)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 4 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 5 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 6 * g.derivative.coeff 7 := by
      rw [Finset.sum_insert (by simp [hne45, hne46]),
        Finset.sum_insert (by simp [hne56]), Finset.sum_singleton]
      ring
    have hder9 : g.derivative.coeff 9 = (10 : F) := by
      rw [Polynomial.coeff_derivative, hg10]
      norm_num
    have hder8 : g.derivative.coeff 8 = (9 : F) * g.coeff 9 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder7 : g.derivative.coeff 7 = (8 : F) * g.coeff 8 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder9, hder8, hder7]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 13 =
        (6 : F) * f.coeff 6 * d (g.coeff 8) +
          (8 : F) * d (g.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne : ((5, 8) : ℕ × ℕ) ≠ (7, 6) := by decide
    have hsubset : ({(5, 8), (7, 6)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (13 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · subst b
        exact hmem58
      · subst b
        exact hmem76
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (13 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(5, 8), (7, 6)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 13 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne58 : b ≠ (5, 8) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne76 : b ≠ (7, 6) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 8 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h6 : b.1 = 6
        · have hf6 : f.derivative.coeff b.1 = 0 := by
            rw [h6, Polynomial.coeff_derivative, hf7]
            simp
          simp [hf6]
        · have hne5 : b.1 ≠ 5 := by
            intro h5
            apply hne58
            ext
            · exact h5
            · omega
          have hne7 : b.1 ≠ 7 := by
            intro h7
            apply hne76
            ext
            · exact h7
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(5, 8), (7, 6)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 5 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 7 * (coefficientDeriv d g).coeff 6 := by
      rw [Finset.sum_pair hne]
    have hder5 : f.derivative.coeff 5 = (6 : F) * f.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder7 : f.derivative.coeff 7 = (8 : F) := by
      rw [Polynomial.coeff_derivative, hf8]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder5, hder7]
    try ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  try ring

theorem gammaResidual810_deriv_zero
    (d : Derivation k F F) (L A B C0 P R : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hrow : (10 : F) * d C0 + (9 : F) * L * d B +
        (8 : F) * P * d A - (6 : F) * A * d P -
        (8 : F) * d R = 0) :
    d (gammaResidual810 L A B C0 P R) = 0 := by
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h532 : d (5 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h5]
  have hPderiv : d P = (5 / 4 : F) * d A := by
    have halpha' : d P - (5 / 4 : F) * d A = 0 := by
      simpa [alphaResidual810, map_sub, Derivation.leibniz, h54, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hP0 : d P - (5 / 4 : F) * d A = 0 := by
    linear_combination hPderiv
  simp only [gammaResidual810, alphaResidual810, map_sub, map_add,
    Derivation.leibniz, h54, h98, h532, hL, zero_mul, add_zero, mul_zero,
    pow_two, hsq]
  linear_combination (-1 / 8 : F) * hrow + (-7 / 4 : F) * A * hP0

end DepressedRow810Fourth

/-! ## Affine depression of a degree-ten source, `z⁶` coefficient -/

section AffineDecic810Fourth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁶` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff6_810
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 6 =
      210 * r ^ 4 - 84 * (p.coeff 9 / h ^ 9) * r ^ 3 +
        28 * (p.coeff 8 / h ^ 8) * r ^ 2 -
        7 * (p.coeff 7 / h ^ 7) * r + p.coeff 6 / h ^ 6 := by
  let plow : (RatFunc k)[X] :=
    p - C (p.coeff 10) * X ^ 10 - C (p.coeff 9) * X ^ 9 -
      C (p.coeff 8) * X ^ 8 - C (p.coeff 7) * X ^ 7 -
      C (p.coeff 6) * X ^ 6
  have hplow : ∀ n, 6 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h6 | hlt6
    · subst n
      simp
    · have : 7 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h7 | hlt7
      · subst n
        simp
      · have : 8 ≤ n := by omega
        rcases Nat.eq_or_lt_of_le this with h8 | hlt8
        · subst n
          simp
        · have : 9 ≤ n := by omega
          rcases Nat.eq_or_lt_of_le this with h9 | hlt9
          · subst n
            simp
          · have : 10 ≤ n := by omega
            rcases Nat.eq_or_lt_of_le this with h10 | hlt10
            · subst n
              simp [hp10]
            · simp [hp_high n (by omega), show n ≠ 10 by omega,
                show n ≠ 9 by omega, show n ≠ 8 by omega,
                show n ≠ 7 by omega, show n ≠ 6 by omega]
  have hplowDeg : plow.natDegree ≤ 5 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = C (p.coeff 10) * X ^ 10 + C (p.coeff 9) * X ^ 9 +
        C (p.coeff 8) * X ^ 8 + C (p.coeff 7) * X ^ 7 +
        C (p.coeff 6) * X ^ 6 + plow := by
    simp only [plow]
    ring
  have hq :
      affineDepress68 h r p =
        (C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹) +
          plow.comp ((X - C r) * C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((X - C r) * C h⁻¹) := rfl
    have hsum (A B D E G H s : (RatFunc k)[X]) :
        (A + B + D + E + G + H).comp s =
          A.comp s + B.comp s + D.comp s + E.comp s + G.comp s +
            H.comp s := by
      have h1 : (A + B + D + E + G + H).comp s =
          (A + B + D + E + G).comp s + H.comp s := add_comp
      have h2 : (A + B + D + E + G).comp s =
          (A + B + D + E).comp s + G.comp s := add_comp
      have h3 : (A + B + D + E).comp s =
          (A + B + D).comp s + E.comp s := add_comp
      have h4 : (A + B + D).comp s =
          (A + B).comp s + D.comp s := add_comp
      have h5 : (A + B).comp s = A.comp s + B.comp s := add_comp
      rw [h1, h2, h3, h4, h5]
    exact hdef.trans ((congrArg (fun t => t.comp ((X - C r) * C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _))
  have hlow (n : ℕ) (hn : 6 ≤ n) :
      (plow.comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤
          plow.natDegree * ((X - C r) * C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((X - C r) * C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((X - C r) * C h⁻¹).natDegree ≤ 5 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤ 5 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 6 ≤ n))
  have h10_6 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 6 =
        210 * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 6 hh]
    have hle : (6 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 6 = 210 := by decide
    simp only [hle, ite_true, hp10, hbin]
    field_simp [hh]
    ring
  have h9_6 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 6 =
        -84 * (p.coeff 9 / h ^ 9) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 6 hh]
    have hle : (6 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 6 = 84 := by decide
    simp only [hle, ite_true, hbin, pow_three]
    field_simp [hh]
    ring
  have h8_6 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 6 =
        28 * (p.coeff 8 / h ^ 8) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 6 hh]
    have hle : (6 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 6 = 28 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]
    ring
  have h7_6 :
      ((C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹)).coeff 6 =
        -7 * (p.coeff 7 / h ^ 7) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 6 hh]
    have hle : (6 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 6 = 7 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]
    ring
  have h6_6 :
      ((C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹)).coeff 6 =
        p.coeff 6 / h ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 6 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  rw [hq, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, h10_6,
    h9_6, h8_6, h7_6, h6_6, hlow 6 (by omega)]
  ring

end AffineDecic810Fourth

/-! ## Local scalar identities at a simple root -/

section FourthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

/-- The third-face jet reduces `M`, `T`, and `U` to a finite scalar
system in `(t, p₆, s)`.  That system forces all three scalars to vanish. -/
theorem fourthFace_rootScalars_vanish810
    (p6 t s : F)
    (hM : (32 : F) * s - (40 : F) * p6 - (5 : F) * t ^ 2 = 0)
    (hT : (100 : F) * t ^ 3 - (512 : F) * t * s +
        (480 : F) * p6 * t = 0)
    (hU : (2240 : F) * p6 ^ 2 - (1120 : F) * p6 * t ^ 2 -
        (2048 : F) * p6 * s - (385 : F) * t ^ 4 +
        (1792 : F) * t ^ 2 * s = 0) :
    t = 0 ∧ p6 = 0 ∧ s = 0 := by
  have hidT :
      (100 : F) * t ^ 3 - (512 : F) * t * s + (480 : F) * p6 * t +
          (16 : F) * t *
            ((32 : F) * s - (40 : F) * p6 - (5 : F) * t ^ 2) =
        (20 : F) * t * (t ^ 2 - (8 : F) * p6) := by
    ring
  have hTprod : (20 : F) * t * (t ^ 2 - (8 : F) * p6) = 0 := by
    rw [← hidT]
    linear_combination hT + (16 : F) * t * hM
  have hidU :
      (2240 : F) * p6 ^ 2 - (1120 : F) * p6 * t ^ 2 -
            (2048 : F) * p6 * s - (385 : F) * t ^ 4 +
          (1792 : F) * t ^ 2 * s +
          ((64 : F) * p6 - (56 : F) * t ^ 2) *
            ((32 : F) * s - (40 : F) * p6 - (5 : F) * t ^ 2) =
        -(5 : F) * ((64 : F) * p6 ^ 2 - (160 : F) * p6 * t ^ 2 +
          (21 : F) * t ^ 4) := by
    ring
  have hUred :
      (64 : F) * p6 ^ 2 - (160 : F) * p6 * t ^ 2 +
        (21 : F) * t ^ 4 = 0 := by
    have h5 : (5 : F) ≠ 0 := by norm_num
    have hcomb :
        -(5 : F) * ((64 : F) * p6 ^ 2 - (160 : F) * p6 * t ^ 2 +
          (21 : F) * t ^ 4) = 0 := by
      rw [← hidU]
      linear_combination hU + ((64 : F) * p6 - (56 : F) * t ^ 2) * hM
    exact (mul_eq_zero.mp (by linear_combination -hcomb)).resolve_left h5
  have hidQuad :
      (64 : F) * p6 ^ 2 - (160 : F) * p6 * t ^ 2 + (21 : F) * t ^ 4 =
        ((8 : F) * p6 - t ^ 2) * ((8 : F) * p6 - (19 : F) * t ^ 2) +
          (2 : F) * t ^ 4 := by
    ring
  have h20 : (20 : F) ≠ 0 := by norm_num
  have ht_or : t = 0 ∨ t ^ 2 = (8 : F) * p6 := by
    have hprod : t * (t ^ 2 - (8 : F) * p6) = 0 :=
      (mul_eq_zero.mp (by linear_combination hTprod)).resolve_left h20
    rcases mul_eq_zero.mp hprod with ht0 | hdiff
    · exact Or.inl ht0
    · exact Or.inr (eq_of_sub_eq_zero hdiff)
  have hp6t : p6 = 0 ∧ t = 0 := by
    rcases ht_or with ht0 | hface
    · have ht0' : t = 0 := ht0
      have hU0 : (64 : F) * p6 ^ 2 = 0 := by
        simpa [ht0'] using hUred
      have h64 : (64 : F) ≠ 0 := by norm_num
      have hp6sq : p6 ^ 2 = 0 :=
        (mul_eq_zero.mp hU0).resolve_left h64
      exact ⟨sq_eq_zero_iff.mp hp6sq, ht0'⟩
    · have hquad : (2 : F) * t ^ 4 = 0 := by
        have : ((8 : F) * p6 - t ^ 2) * ((8 : F) * p6 - (19 : F) * t ^ 2) +
            (2 : F) * t ^ 4 = 0 := by
          rw [← hidQuad]
          exact hUred
        have hzero : (8 : F) * p6 - t ^ 2 = 0 := by
          rw [hface]
          ring
        simpa [hzero] using this
      have h2 : (2 : F) ≠ 0 := by norm_num
      have ht4 : t ^ 4 = 0 :=
        (mul_eq_zero.mp hquad).resolve_left h2
      have ht0 : t = 0 := by
        have hsq : (t ^ 2) ^ 2 = 0 := by
          convert ht4 using 1
          ring
        exact sq_eq_zero_iff.mp (sq_eq_zero_iff.mp hsq)
      have hp60 : p6 = 0 := by
        have h8 : (8 : F) ≠ 0 := by norm_num
        have : (8 : F) * p6 = 0 := by
          rw [← hface, ht0]
          exact zero_pow (by norm_num : (2 : ℕ) ≠ 0)
        exact (mul_eq_zero.mp this).resolve_left h8
      exact ⟨hp60, ht0⟩
  have hs0 : s = 0 := by
    have h32 : (32 : F) ≠ 0 := by norm_num
    have : (32 : F) * s = 0 := by
      rw [hp6t.1, hp6t.2] at hM
      linear_combination hM
    exact (mul_eq_zero.mp this).resolve_left h32
  exact ⟨hp6t.2, hp6t.1, hs0⟩

/-- After `h⁵ ∣ p₇`, the next reduced `M`/`U` pair kills the first jets
of `p₆` and `q₈`. -/
theorem fourthFace_nextRootScalars_vanish810
    (v s1 : F)
    (hM : (32 : F) * s1 - (40 : F) * v = 0)
    (hU : (2240 : F) * v ^ 2 - (2048 : F) * v * s1 = 0) :
    v = 0 ∧ s1 = 0 := by
  have hid :
      (2240 : F) * v ^ 2 - (2048 : F) * v * s1 +
          (64 : F) * v * ((32 : F) * s1 - (40 : F) * v) =
        -(320 : F) * v ^ 2 := by
    ring
  have hv2 : (320 : F) * v ^ 2 = 0 := by
    have hneg : -(320 : F) * v ^ 2 = 0 := by
      rw [← hid]
      linear_combination hU + (64 : F) * v * hM
    linear_combination -hneg
  have h320 : (320 : F) ≠ 0 := by norm_num
  have hv : v = 0 :=
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hv2).resolve_left h320)
  have hs1 : s1 = 0 := by
    have h32 : (32 : F) ≠ 0 := by norm_num
    have : (32 : F) * s1 = 0 := by
      rw [hv] at hM
      linear_combination hM
    exact (mul_eq_zero.mp this).resolve_left h32
  exact ⟨hv, hs1⟩

end FourthFaceScalars810

/-! ## Source-facing fourth-face packet -/

section NonzeroFourthFace810

variable {k : Type*} [Field k] [CharZero k]

/-- The third octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h²⁸`. -/
theorem nonzeroFace810_fourthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ delta : k,
      localClearedFourthDefect810 h0 (p.coeff 7) (p.coeff 6) (p.coeff 5)
          (p.coeff 4) (q.coeff 8) (q.coeff 7) (q.coeff 6) lambda =
        Polynomial.C delta * h0 ^ 28 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  have hh : h ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 8) = h ^ 8 := by
    simp only [hp8, hH, h, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = h ^ 10 := by
    simp only [hq10, hH, h, map_pow]
    ring
  have hpDep := affineDepress_sourceOctic68 p h
    (octicDepressionR810 h a7) hp hh hpTop
  have hL0 : depressedL68 h (octicDepressionR810 h a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter h a7 hh
  have hNrat : 5 * a7 * h ^ 2 - 4 * b9 = RatFunc.C lambda * h ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    simpa only [hH, h, a7, b9, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hLval :
      depressedL810 h (octicDepressionR810 h a7) b9 =
        RatFunc.C (-lambda / 4) := by
    have hL := depressedL810_eq_of_ninthPower h a7 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j h (octicDepressionR810 h a7) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 h (octicDepressionR810 h a7) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 h (octicDepressionR810 h a7) (sourceToRatFunc68 q)
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_seven, hL0]
  have hf8 : f.coeff 8 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_eight]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = h ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src
  have hg6 :
      g.coeff 6 =
        depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedR810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg8' :
      g.coeff 8 =
        depressedP810 h (octicDepressionR810 h a7) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 4) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * octicDepressionR810 h a7 +
        (sourceToRatFunc68 q).coeff 9 / h ^ 9 =
          depressedL810 h (octicDepressionR810 h a7) b9 := by
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 4) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow15 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_15_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 15) hbracket
    simpa [f, g, Polynomial.coeff_C, show (15 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow13 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 5) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 6) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 8) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_13_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf6 : f.coeff 6 = depressedA810 h (octicDepressionR810 h a7) a7 a6 := by
    dsimp only [f, depressedA810, a7, a6]
    rw [hpDep, coeff_depressedOctic68_six]
  have hf5 : f.coeff 5 =
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 := by
    dsimp only [f, depressedB810, a7, a6, a5]
    rw [hpDep, coeff_depressedOctic68_five]
  have hf4 : f.coeff 4 =
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 := by
    dsimp only [f, depressedC810, a7, a6, a5, a4]
    rw [hpDep, coeff_depressedOctic68_four]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual810 (f.coeff 6) (g.coeff 8)) = 0 :=
    alphaResidual810_deriv_zero ratFuncDerivation68 (f.coeff 6)
      (g.coeff 8) hrow15
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow13)
  obtain ⟨delta0, hdelta0⟩ :
      ∃ a : k,
        gammaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (g.coeff 8) (g.coeff 6) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hgamma0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedFourthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda) =
        (2048 : RatFunc k) * h ^ 28 *
          gammaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (g.coeff 8) (g.coeff 6) := by
    have hF := fourthDefect_eq_clearedGamma810 h a7 a6 a5 a4 b9 b8 b7 b6
      (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL810 h (octicDepressionR810 h a7) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    simpa [localClearedFourthDefect810, map_sub, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, h, a7, a6, a5, a4, b8,
      b7, b6, gammaResidual810, alphaResidual810, hf6, hf5, hf4, hg6,
      hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedFourthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (2048 * delta0) * h0 ^ 28) := by
    rw [hclear, hdelta0]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨2048 * delta0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the degree-one scale divides the
subleading octic coefficient to order five, the next octic coefficient
to order two, the first unused decic coefficient to order four, `q₇`
to order one, and `q₉` to order seven. -/
theorem nonzeroFace810_linearRoot_fourthInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    h0 ^ 5 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 6 ∧ h0 ^ 4 ∣ q.coeff 8 ∧
      h0 ∣ q.coeff 7 ∧ h0 ^ 7 ∣ q.coeff 9 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace810_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨delta, hU⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨hp7pow4, hq8pow2, _hq9pow6⟩ :=
    nonzeroFace810_linearRoot_thirdInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  obtain ⟨t, ht⟩ := hp7pow4
  obtain ⟨s, hs⟩ := hq8pow2
  have hM0 :
      (32 : k[X]) * s - (40 : k[X]) * p.coeff 6 +
          (9 : k[X]) * Polynomial.C lambda * t * h0 ^ 3 -
        (5 : k[X]) * t ^ 2 =
        Polynomial.C alpha * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 8 hh0)
    calc
      h0 ^ 8 *
            ((32 : k[X]) * s - (40 : k[X]) * p.coeff 6 +
                (9 : k[X]) * Polynomial.C lambda * t * h0 ^ 3 -
              (5 : k[X]) * t ^ 2) =
          localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect810, ht, hs]
        ring
      _ = Polynomial.C alpha * h0 ^ 14 := hM
      _ = h0 ^ 8 * (Polynomial.C alpha * h0 ^ 6) := by ring
  have hT0 :
      (100 : k[X]) * t ^ 3 - (512 : k[X]) * t * s +
          (480 : k[X]) * p.coeff 6 * t +
        (512 : k[X]) * q.coeff 7 * h0 ^ 2 +
          (144 : k[X]) * Polynomial.C lambda * p.coeff 6 * h0 ^ 3 -
        (135 : k[X]) * Polynomial.C lambda * t ^ 2 * h0 ^ 3 -
          (640 : k[X]) * p.coeff 5 * h0 ^ 4 =
        Polynomial.C gamma * h0 ^ 9 := by
    apply mul_left_cancel₀ (pow_ne_zero 12 hh0)
    calc
      h0 ^ 12 *
            ((100 : k[X]) * t ^ 3 - (512 : k[X]) * t * s +
                (480 : k[X]) * p.coeff 6 * t +
              (512 : k[X]) * q.coeff 7 * h0 ^ 2 +
                (144 : k[X]) * Polynomial.C lambda * p.coeff 6 * h0 ^ 3 -
              (135 : k[X]) * Polynomial.C lambda * t ^ 2 * h0 ^ 3 -
                (640 : k[X]) * p.coeff 5 * h0 ^ 4) =
          localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect810, ht, hs]
        ring
      _ = Polynomial.C gamma * h0 ^ 21 := hT
      _ = h0 ^ 12 * (Polynomial.C gamma * h0 ^ 9) := by ring
  have hU0 :
      (2240 : k[X]) * p.coeff 6 ^ 2 - (2048 : k[X]) * p.coeff 6 * s -
          (1120 : k[X]) * p.coeff 6 * t ^ 2 +
        (1792 : k[X]) * s * t ^ 2 - (385 : k[X]) * t ^ 4 +
          (1600 : k[X]) * p.coeff 5 * t * h0 ^ 4 -
        (1792 : k[X]) * q.coeff 7 * t * h0 ^ 2 -
          (1008 : k[X]) * Polynomial.C lambda * p.coeff 6 * t * h0 ^ 3 +
        (462 : k[X]) * Polynomial.C lambda * t ^ 3 * h0 ^ 3 +
          (2048 : k[X]) * q.coeff 6 * h0 ^ 6 +
        (576 : k[X]) * Polynomial.C lambda * p.coeff 5 * h0 ^ 7 -
          (2560 : k[X]) * p.coeff 4 * h0 ^ 8 =
        Polynomial.C delta * h0 ^ 12 := by
    apply mul_left_cancel₀ (pow_ne_zero 16 hh0)
    calc
      h0 ^ 16 *
            ((2240 : k[X]) * p.coeff 6 ^ 2 -
                (2048 : k[X]) * p.coeff 6 * s -
              (1120 : k[X]) * p.coeff 6 * t ^ 2 +
                (1792 : k[X]) * s * t ^ 2 - (385 : k[X]) * t ^ 4 +
              (1600 : k[X]) * p.coeff 5 * t * h0 ^ 4 -
                (1792 : k[X]) * q.coeff 7 * t * h0 ^ 2 -
              (1008 : k[X]) * Polynomial.C lambda * p.coeff 6 * t *
                  h0 ^ 3 +
                (462 : k[X]) * Polynomial.C lambda * t ^ 3 * h0 ^ 3 +
              (2048 : k[X]) * q.coeff 6 * h0 ^ 6 +
                (576 : k[X]) * Polynomial.C lambda * p.coeff 5 * h0 ^ 7 -
              (2560 : k[X]) * p.coeff 4 * h0 ^ 8) =
          localClearedFourthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect810, ht, hs]
        ring
      _ = Polynomial.C delta * h0 ^ 28 := hU
      _ = h0 ^ 16 * (Polynomial.C delta * h0 ^ 12) := by ring
  have hMroot : (32 : k) * s.eval a - (40 : k) * (p.coeff 6).eval a -
      (5 : k) * (t.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hM0
    simpa [hroot] using heval
  have hTroot : (100 : k) * (t.eval a) ^ 3 -
      (512 : k) * t.eval a * s.eval a +
        (480 : k) * (p.coeff 6).eval a * t.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT0
    simpa [hroot] using heval
  have hUroot : (2240 : k) * ((p.coeff 6).eval a) ^ 2 -
      (1120 : k) * (p.coeff 6).eval a * (t.eval a) ^ 2 -
        (2048 : k) * (p.coeff 6).eval a * s.eval a -
      (385 : k) * (t.eval a) ^ 4 +
        (1792 : k) * (t.eval a) ^ 2 * s.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU0
    have hraw : (2240 : k) * ((p.coeff 6).eval a) ^ 2 -
        (2048 : k) * (p.coeff 6).eval a * s.eval a -
          (1120 : k) * (p.coeff 6).eval a * (t.eval a) ^ 2 +
        (1792 : k) * s.eval a * (t.eval a) ^ 2 -
          (385 : k) * (t.eval a) ^ 4 = 0 := by
      simpa [hroot] using heval
    linear_combination hraw
  obtain ⟨ht0, hp6root, hs0⟩ :=
    fourthFace_rootScalars_vanish810 ((p.coeff 6).eval a) (t.eval a)
      (s.eval a) hMroot hTroot hUroot
  have ht_div : h0 ∣ t :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 t a hh0degree hroot ht0
  have hp6div : h0 ∣ p.coeff 6 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 6) a
      hh0degree hroot hp6root
  have hs_div : h0 ∣ s :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 s a hh0degree hroot hs0
  obtain ⟨t1, ht1⟩ := ht_div
  obtain ⟨v, hv⟩ := hp6div
  obtain ⟨s1, hs1⟩ := hs_div
  have hp7t1 : p.coeff 7 = h0 ^ 5 * t1 := by
    rw [ht, ht1]
    ring
  have hq8s1 : q.coeff 8 = h0 ^ 3 * s1 := by
    rw [hs, hs1]
    ring
  have hp6v : p.coeff 6 = h0 * v := hv
  have hM1 :
      (32 : k[X]) * s1 - (40 : k[X]) * v -
          (5 : k[X]) * t1 ^ 2 * h0 +
        (9 : k[X]) * Polynomial.C lambda * t1 * h0 ^ 3 =
        Polynomial.C alpha * h0 ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 9 hh0)
    calc
      h0 ^ 9 *
            ((32 : k[X]) * s1 - (40 : k[X]) * v -
                (5 : k[X]) * t1 ^ 2 * h0 +
              (9 : k[X]) * Polynomial.C lambda * t1 * h0 ^ 3) =
          localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect810, hp7t1, hp6v, hq8s1]
        ring
      _ = Polynomial.C alpha * h0 ^ 14 := hM
      _ = h0 ^ 9 * (Polynomial.C alpha * h0 ^ 5) := by ring
  have hU1 :
      (2240 : k[X]) * v ^ 2 - (2048 : k[X]) * v * s1 -
          (1120 : k[X]) * v * t1 ^ 2 * h0 +
        (1792 : k[X]) * s1 * t1 ^ 2 * h0 -
          (385 : k[X]) * t1 ^ 4 * h0 ^ 2 -
        (1792 : k[X]) * q.coeff 7 * t1 * h0 +
          (1600 : k[X]) * p.coeff 5 * t1 * h0 ^ 3 -
        (1008 : k[X]) * Polynomial.C lambda * v * t1 * h0 ^ 3 +
          (462 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 ^ 4 +
        (2048 : k[X]) * q.coeff 6 * h0 ^ 4 +
          (576 : k[X]) * Polynomial.C lambda * p.coeff 5 * h0 ^ 5 -
        (2560 : k[X]) * p.coeff 4 * h0 ^ 6 =
        Polynomial.C delta * h0 ^ 10 := by
    apply mul_left_cancel₀ (pow_ne_zero 18 hh0)
    calc
      h0 ^ 18 *
            ((2240 : k[X]) * v ^ 2 - (2048 : k[X]) * v * s1 -
                (1120 : k[X]) * v * t1 ^ 2 * h0 +
              (1792 : k[X]) * s1 * t1 ^ 2 * h0 -
                (385 : k[X]) * t1 ^ 4 * h0 ^ 2 -
              (1792 : k[X]) * q.coeff 7 * t1 * h0 +
                (1600 : k[X]) * p.coeff 5 * t1 * h0 ^ 3 -
              (1008 : k[X]) * Polynomial.C lambda * v * t1 * h0 ^ 3 +
                (462 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 ^ 4 +
              (2048 : k[X]) * q.coeff 6 * h0 ^ 4 +
                (576 : k[X]) * Polynomial.C lambda * p.coeff 5 * h0 ^ 5 -
              (2560 : k[X]) * p.coeff 4 * h0 ^ 6) =
          localClearedFourthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect810, hp7t1, hp6v, hq8s1]
        ring
      _ = Polynomial.C delta * h0 ^ 28 := hU
      _ = h0 ^ 18 * (Polynomial.C delta * h0 ^ 10) := by ring
  have hM1root : (32 : k) * s1.eval a - (40 : k) * v.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hM1
    simpa [hroot] using heval
  have hU1root : (2240 : k) * (v.eval a) ^ 2 -
      (2048 : k) * v.eval a * s1.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU1
    simpa [hroot] using heval
  obtain ⟨hv0, hs10⟩ :=
    fourthFace_nextRootScalars_vanish810 (v.eval a) (s1.eval a)
      hM1root hU1root
  have hv_div : h0 ∣ v :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 v a hh0degree hroot hv0
  have hs1_div : h0 ∣ s1 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 s1 a hh0degree hroot hs10
  have hT1 :
      (512 : k[X]) * q.coeff 7 - (512 : k[X]) * s1 * t1 +
          (480 : k[X]) * t1 * v + (100 : k[X]) * t1 ^ 3 * h0 -
        (640 : k[X]) * p.coeff 5 * h0 ^ 2 +
          (144 : k[X]) * Polynomial.C lambda * v * h0 ^ 2 -
        (135 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 ^ 3 =
        Polynomial.C gamma * h0 ^ 7 := by
    apply mul_left_cancel₀ (pow_ne_zero 14 hh0)
    calc
      h0 ^ 14 *
            ((512 : k[X]) * q.coeff 7 - (512 : k[X]) * s1 * t1 +
                (480 : k[X]) * t1 * v + (100 : k[X]) * t1 ^ 3 * h0 -
              (640 : k[X]) * p.coeff 5 * h0 ^ 2 +
                (144 : k[X]) * Polynomial.C lambda * v * h0 ^ 2 -
              (135 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 ^ 3) =
          localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect810, hp7t1, hp6v, hq8s1]
        ring
      _ = Polynomial.C gamma * h0 ^ 21 := hT
      _ = h0 ^ 14 * (Polynomial.C gamma * h0 ^ 7) := by ring
  have hq7root : (q.coeff 7).eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT1
    have h512 : (512 : k) ≠ 0 := by norm_num
    have h512q : (512 : k) * (q.coeff 7).eval a = 0 := by
      simpa [hroot, hv0, hs10] using heval
    exact (mul_eq_zero.mp h512q).resolve_left h512
  have hq7div : h0 ∣ q.coeff 7 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 7) a
      hh0degree hroot hq7root
  have hp7pow : h0 ^ 5 ∣ p.coeff 7 := ⟨t1, by rw [hp7t1]⟩
  have hp6pow : h0 ^ 2 ∣ p.coeff 6 := by
    obtain ⟨v2, hv2⟩ := hv_div
    refine ⟨v2, ?_⟩
    rw [hp6v, hv2]
    ring
  have hq8pow : h0 ^ 4 ∣ q.coeff 8 := by
    obtain ⟨s2, hs2⟩ := hs1_div
    refine ⟨s2, ?_⟩
    rw [hq8s1, hs2]
    ring
  have hq9pow : h0 ^ 7 ∣ q.coeff 9 := by
    have h4 : (4 : k) ≠ 0 := by norm_num
    have hN' :
        (4 : k[X]) * q.coeff 9 =
          (5 : k[X]) * p.coeff 7 * h0 ^ 2 -
            Polynomial.C lambda * h0 ^ 9 := by
      have : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := hN
      rw [hH] at this
      linear_combination -this
    have hform :
        (4 : k[X]) * q.coeff 9 =
          h0 ^ 7 * ((5 : k[X]) * t1 - Polynomial.C lambda * h0 ^ 2) := by
      rw [hN', hp7t1]
      ring
    have hC4 : Polynomial.C (4 : k) = (4 : k[X]) :=
      Polynomial.C_eq_natCast 4
    have hq9eq : q.coeff 9 =
        C ((4 : k)⁻¹) * ((4 : k[X]) * q.coeff 9) := by
      have hone : (C ((4 : k)⁻¹) * C (4 : k) : k[X]) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h4, map_one]
      calc
        q.coeff 9 = (1 : k[X]) * q.coeff 9 := (one_mul _).symm
        _ = (C ((4 : k)⁻¹) * C (4 : k)) * q.coeff 9 := by rw [hone]
        _ = C ((4 : k)⁻¹) * (C (4 : k) * q.coeff 9) := mul_assoc _ _ _
        _ = C ((4 : k)⁻¹) * ((4 : k[X]) * q.coeff 9) := by rw [hC4]
    refine ⟨C ((4 : k)⁻¹) *
        ((5 : k[X]) * t1 - Polynomial.C lambda * h0 ^ 2), ?_⟩
    rw [hq9eq, hform]
    ring
  exact ⟨hp7pow, hp6pow, hq8pow, hq7div, hq9pow⟩

/-- Source-facing fourth integral for a normalized scale-two `(8,10)`
nonzero face. -/
theorem normalized810ScaleTwo_nonzeroFace_fourthDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda delta : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedFourthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda =
          Polynomial.C delta * h0 ^ 28 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, _hroot, hN⟩ :=
    normalized810ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨delta, hU⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8' hq10' hN' hD
  exact ⟨h0, lambda, delta, hh0, hlambda, hh0degree, hH, hN', hU⟩

/-- Finite local initial packet of a normalized scale-two `(8,10)`
nonzero face: the degree-one scale divides `p₇` to order five, `p₆` to
order two, `q₈` to order four, `q₇` to order one, and `q₉` to order
seven. -/
theorem normalized810ScaleTwo_nonzeroFace_fourthInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        h0 ^ 5 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 6 ∧ h0 ^ 4 ∣ q.coeff 8 ∧
        h0 ∣ q.coeff 7 ∧ h0 ^ 7 ∣ q.coeff 9 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized810ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨hp7, hp6, hq8, hq7, hq9⟩ :=
    nonzeroFace810_linearRoot_fourthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp7, hp6, hq8,
    hq7, hq9, hN'⟩

end NonzeroFourthFace810

#print axioms fourthCoefficientJacobianRow_810
#print axioms differentialJacobian_coeff_13_monicOcticDecic
#print axioms fourthDefect_eq_clearedGamma810
#print axioms nonzeroFace810_fourthDefectPowerRelation
#print axioms nonzeroFace810_linearRoot_fourthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_fourthDefectPowerRelation
#print axioms normalized810ScaleTwo_nonzeroFace_fourthInitialPacket

end Max11DegreeRoutes
