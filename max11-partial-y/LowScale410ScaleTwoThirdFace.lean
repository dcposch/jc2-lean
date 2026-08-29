import LowScale410ScaleTwoSecondFace
import LowScale810ScaleTwoThirdFace

/-! # Scale-two third face for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the second face supplies the degree-`11` integral
`P - (5/2) A` and the local vanishings `h ∣ q₈`, `h⁶ ∣ q₉`.  The next
Keller coefficient is the degree-`10` Jacobian row.  After the same
quartic depression that kills `z³`, that row is
`10 B' + 9 L A' - 4 Q' = 0`.  The resulting first integral clears to a
polynomial defect `T` of weight eleven.

Evaluating the second and third defects together at the root of `h`
forces the finite initial jet `h ∣ p₃`, `h⁴ ∣ q₈`, `h ∣ q₇`, and
`h⁷ ∣ q₉`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The third row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  It is the source of the first mixed quartic/decic
`z`/`z⁷` defect after the degree-`11` integral. -/
theorem thirdCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 9).derivative +
        (p.coeff 1 * Polynomial.C (1 : K)) * (q.coeff 10).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 10) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (10 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 10 :
      Finset (ℕ × ℕ)) =
      ({(0, 10), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4),
        (7, 3), (8, 2), (9, 1), (10, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC7, hC8, hC9, hC10, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Quartic `z` and decic `z⁷` coordinates -/

section Depression410Third

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed quartic `z` coefficient. -/
abbrev depressedB410 (h r a3 a2 a1 : F) : F :=
  depressedB46 h r a3 a2 a1

/-- Depressed decic `z⁷` coefficient. -/
abbrev depressedQ410 (h r b9 b8 b7 : F) : F :=
  depressedQ810 h r b9 b8 b7

/-- First residual of the degree-`10` row. -/
def betaResidual410 (L A B Q : F) : F :=
  Q - (5 / 2 : F) * B - (9 / 4 : F) * L * A

/-- Polynomial numerator of `64 h¹¹ (Q - (5/2) B - (9/4) L A)` on the
ninth-power face. -/
def localClearedThirdDefect410
    (h a3 a2 a1 b8 b7 : F[X]) (lambda : F) : F[X] :=
  (220 : F[X]) * a3 ^ 3 * h ^ 2 -
    (99 : F[X]) * Polynomial.C lambda * a3 ^ 2 * h ^ 5 -
    (128 : F[X]) * a3 * b8 +
    (64 : F[X]) * b7 * h ^ 4 +
    (80 : F[X]) * a2 * a3 * h ^ 6 -
    (160 : F[X]) * a1 * h ^ 10 +
    (72 : F[X]) * Polynomial.C lambda * a2 * h ^ 9

omit [CharZero F] in
theorem coeff_depressedQuartic46_one
    (A B C0 : F) :
    (depressedQuartic46 A B C0).coeff 1 = B := by
  simp [depressedQuartic46, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the quartic `z` coordinate. -/
theorem depressedB410_eq_cleared
    (h a3 a2 a1 : F) (hh : h ≠ 0) :
    depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1 =
      (a3 ^ 3 - 4 * a2 * a3 * h ^ 4 + 8 * a1 * h ^ 8) /
        (8 * h ^ 9) := by
  simp only [depressedB410, depressedB46, quarticDepressionR410,
    quarticDepressionR46]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z⁷` coordinate on the
ninth-power face. -/
theorem depressedQ410_eq_cleared
    (h a3 b9 b8 b7 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7 =
      (30 * a3 ^ 3 * h ^ 2 - 9 * lambda * a3 ^ 2 * h ^ 5 -
          16 * a3 * b8 + 8 * b7 * h ^ 4) /
        (8 * h ^ 11) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh11 : h ^ 11 ≠ 0 := pow_ne_zero 11 hh
  have hb9 : 2 * b9 = 5 * a3 * h ^ 6 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedQ410, depressedQ810, quarticDepressionR410,
    quarticDepressionR46]
  have hrewrite :
      -120 * (a3 / (4 * h ^ 3)) ^ 3 +
          36 * (b9 / h ^ 9) * (a3 / (4 * h ^ 3)) ^ 2 -
        8 * (b8 / h ^ 8) * (a3 / (4 * h ^ 3)) + b7 / h ^ 7 =
        (30 * a3 ^ 3 * h ^ 2 - 9 * lambda * a3 ^ 2 * h ^ 5 -
            16 * a3 * b8 + 8 * b7 * h ^ 4) /
          (8 * h ^ 11) := by
    field_simp [hh, h2, h4, hh3, hh7, hh8pow, hh9, hh11]
    have hb9' :
        b9 = (5 * a3 * h ^ 6 - lambda * h ^ 9) / 2 := by
      field_simp [h2]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h2, h4, hh3, hh7, hh8pow, hh9, hh11]
    ring
  exact hrewrite

/-- Clearing the first integral `Q - (5/2) B - (9/4) L A` against `h¹¹`
on the ninth-power face. -/
theorem thirdDefect_eq_clearedBeta410
    (h a3 a2 a1 b9 b8 b7 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (64 : F) * h ^ 11 *
        betaResidual410
          (depressedL410 h (quarticDepressionR410 h a3) b9)
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
          (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
          (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7) =
      (220 : F) * a3 ^ 3 * h ^ 2 - (99 : F) * lambda * a3 ^ 2 * h ^ 5 -
        (128 : F) * a3 * b8 + (64 : F) * b7 * h ^ 4 +
        (80 : F) * a2 * a3 * h ^ 6 - (160 : F) * a1 * h ^ 10 +
        (72 : F) * lambda * a2 * h ^ 9 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh11 : h ^ 11 ≠ 0 := pow_ne_zero 11 hh
  have hL :
      depressedL410 h (quarticDepressionR410 h a3) b9 = -lambda / 2 :=
    depressedL410_eq_of_ninthPower h a3 b9 lambda hh hN
  have hA :
      depressedA410 h (quarticDepressionR410 h a3) a3 a2 =
        (8 * a2 * h ^ 4 - 3 * a3 ^ 2) / (8 * h ^ 6) :=
    depressedA410_eq_cleared h a3 a2 hh
  have hB :
      depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1 =
        (a3 ^ 3 - 4 * a2 * a3 * h ^ 4 + 8 * a1 * h ^ 8) /
          (8 * h ^ 9) :=
    depressedB410_eq_cleared h a3 a2 a1 hh
  have hQ :
      depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7 =
        (30 * a3 ^ 3 * h ^ 2 - 9 * lambda * a3 ^ 2 * h ^ 5 -
            16 * a3 * b8 + 8 * b7 * h ^ 4) / (8 * h ^ 11) :=
    depressedQ410_eq_cleared h a3 b9 b8 b7 lambda hh hN
  have h64Q :
      (64 : F) * h ^ 11 *
          depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7 =
        (240 : F) * a3 ^ 3 * h ^ 2 - (72 : F) * lambda * a3 ^ 2 * h ^ 5 -
          (128 : F) * a3 * b8 + (64 : F) * b7 * h ^ 4 := by
    rw [hQ]
    field_simp [hh, h8, hh11]
    ring
  have h160B :
      (160 : F) * h ^ 11 *
          depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1 =
        (20 : F) * a3 ^ 3 * h ^ 2 - (80 : F) * a2 * a3 * h ^ 6 +
          (160 : F) * a1 * h ^ 10 := by
    rw [hB]
    field_simp [hh, h8, hh9, hh11]
    ring
  have h72A :
      (72 : F) * lambda * h ^ 11 *
          depressedA410 h (quarticDepressionR410 h a3) a3 a2 =
        (72 : F) * lambda * a2 * h ^ 9 -
          (27 : F) * lambda * a3 ^ 2 * h ^ 5 := by
    rw [hA]
    field_simp [hh, h8, hh6, hh11]
    ring
  have hdiff :
      (64 : F) * h ^ 11 *
          betaResidual410
            (depressedL410 h (quarticDepressionR410 h a3) b9)
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
            (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
            (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7) =
        (64 : F) * h ^ 11 *
            depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7 -
          (160 : F) * h ^ 11 *
            depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1 +
          (72 : F) * lambda * h ^ 11 *
            depressedA410 h (quarticDepressionR410 h a3) a3 a2 := by
    simp only [betaResidual410, hL]
    field_simp [h2, h4]
    ring
  rw [hdiff, h64Q, h160B, h72A]
  ring

end Depression410Third

/-! ## Degree-`10` depressed Jacobian coefficient -/

section DepressedRow410Third

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`10` Jacobian coefficient is
exactly `10 B' + 9 L A' - 4 Q'`. -/
theorem differentialJacobian_coeff_10_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 10 =
      (10 : F) * d (f.coeff 1) + (9 : F) * g.coeff 9 * d (f.coeff 2) -
        (4 : F) * d (g.coeff 7) := by
  have hfd_high : ∀ n, 3 ≤ n → (coefficientDeriv d f).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      simpa [hf3]
    · have : 4 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq4 | hlt4
      · subst n
        simpa [hf4, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hf_high n (by omega))
  have hgd_high : ∀ n, 10 ≤ n → g.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 10 < n + 1 := by omega
    simp [hg_high (n + 1) this]
  have hfd'_high : ∀ n, 4 ≤ n → f.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 4 < n + 1 := by omega
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
  have hmem19 : ((1, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem28 : ((2, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem37 : ((3, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 10 =
        (10 : F) * d (f.coeff 1) +
          (9 : F) * g.coeff 9 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne : ((1, 9) : ℕ × ℕ) ≠ (2, 8) := by decide
    have hsubset : ({(1, 9), (2, 8)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (10 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · subst b
        exact hmem19
      · subst b
        exact hmem28
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(1, 9), (2, 8)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 10 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne19 : b ≠ (1, 9) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne28 : b ≠ (2, 8) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 3 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne19
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne28
          ext
          · exact h2
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(1, 9), (2, 8)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 1 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 8 := by
      rw [Finset.sum_pair hne]
    have hder9 : g.derivative.coeff 9 = (10 : F) := by
      rw [Polynomial.coeff_derivative, hg10]
      norm_num
    have hder8 : g.derivative.coeff 8 = (9 : F) * g.coeff 9 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder9, hder8]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 10 =
        (4 : F) * d (g.coeff 7) := by
    have hprod :
        (f.derivative * coefficientDeriv d g).coeff 10 =
          f.derivative.coeff 3 * (coefficientDeriv d g).coeff 7 := by
      rw [Polynomial.coeff_mul]
      refine Finset.sum_eq_single_of_mem _ hmem37 ?_
      intro b hb hne
      have hij : b.1 + b.2 = 10 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hi : b.1 ≠ 3 := by
        intro h3
        apply hne
        ext
        · exact h3
        · omega
      by_cases hige : 4 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h2 : b.1 = 2
        · have hf2 : f.derivative.coeff b.1 = 0 := by
            rw [h2, Polynomial.coeff_derivative, hf3]
            simp
          simp [hf2]
        · have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hder : f.derivative.coeff 3 = (4 : F) := by
      rw [Polynomial.coeff_derivative, hf4]
      norm_num
    rw [hprod, coeff_coefficientDeriv, hder]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]

theorem betaResidual410_deriv_zero
    (d : Derivation k F F) (L A B Q : F)
    (hL : d L = 0)
    (hrow : (10 : F) * d B + (9 : F) * L * d A - (4 : F) * d Q = 0) :
    d (betaResidual410 L A B Q) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h94 : d (9 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h9]
  simp only [betaResidual410, map_sub, Derivation.leibniz, h52, h94, hL,
    zero_mul, add_zero, mul_zero]
  linear_combination (-1 / 4 : F) * hrow

end DepressedRow410Third

/-! ## Source-facing third-face packet -/

section NonzeroThirdFace410

variable {k : Type*} [Field k] [CharZero k]

/-- The second quartic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h¹¹`. -/
theorem nonzeroFace410_thirdDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ gamma : k,
      localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (q.coeff 8) (q.coeff 7) lambda =
        Polynomial.C gamma * h0 ^ 11 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 4) = hRF ^ 4 := by
    simp only [hp4, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep :
      affineDepress68 hRF (quarticDepressionR410 hRF a3)
          (sourceToRatFunc68 p) =
        depressedQuartic46
          (depressedA46 hRF (quarticDepressionR410 hRF a3) a3 a2)
          (depressedB46 hRF (quarticDepressionR410 hRF a3) a3 a2 a1)
          (depressedC46 hRF (quarticDepressionR410 hRF a3) a3 a2 a1
            (algebraMap k[X] (RatFunc k) (p.coeff 0))) := by
    change affineDepress46 hRF (quarticDepressionR410 hRF a3)
        (sourceToRatFunc46 p) = _
    exact affineDepress_sourceQuartic46 p hRF
      (quarticDepressionR410 hRF a3) hp hh hpTop
      (by simp [a3, quarticDepressionR410])
  have hNrat : 5 * a3 * hRF ^ 6 - 2 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH3 : algebraMap k[X] (RatFunc k) (H ^ 3) = hRF ^ 6 := by
      simp only [hH, hRF, map_pow]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) (h0 ^ 9) = hRF ^ 9 := by
      simp only [hRF, map_pow]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9) =
        5 * a3 * hRF ^ 6 - 2 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a3, b9, hH3]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * h0 ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hLval :
      depressedL410 hRF (quarticDepressionR410 hRF a3) b9 =
        RatFunc.C (-lambda / 2) := by
    have hL := depressedL410_eq_of_ninthPower hRF a3 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (quarticDepressionR410 hRF a3) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (quarticDepressionR410 hRF a3) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (quarticDepressionR410 hRF a3) (sourceToRatFunc68 q)
  have hf3 : f.coeff 3 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_three]
  have hf4 : f.coeff 4 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_four]
  have hf_high : ∀ n, 4 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_of_gt_four _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, _, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedQ410, depressedQ810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 2) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * quarticDepressionR410 hRF a3 +
        (sourceToRatFunc68 q).coeff 9 / hRF ^ 9 =
          depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
      simp [depressedL410, depressedL810, quarticDepressionR410,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 2) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow :
      (differentialJacobian ratFuncDerivation68 f g).coeff 10 =
        (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) := by
    exact differentialJacobian_coeff_10_monicQuarticDecic
      ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
  have hrow0 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) -
        (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf2 : f.coeff 2 = depressedA410 hRF (quarticDepressionR410 hRF a3) a3 a2 := by
    dsimp only [f, depressedA410, a3, a2]
    rw [hpDep, coeff_depressedQuartic46_two]
  have hf1 : f.coeff 1 =
      depressedB410 hRF (quarticDepressionR410 hRF a3) a3 a2 a1 := by
    dsimp only [f, depressedB410, a3, a2, a1]
    rw [hpDep, coeff_depressedQuartic46_one]
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (g.coeff 7)) = 0 :=
    betaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (g.coeff 7) hLconst (by simpa using hrow0)
  obtain ⟨gamma, hgamma⟩ :
      ∃ a : k,
        betaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (g.coeff 7) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hbeta0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda) =
        (64 : RatFunc k) * hRF ^ 11 *
          betaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (g.coeff 7) := by
    have hF := thirdDefect_eq_clearedBeta410 hRF a3 a2 a1 b9 b8 b7
      (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL410, depressedL810, quarticDepressionR410,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedThirdDefect410, map_sub, map_add, map_mul, map_pow,
      map_ofNat, RatFunc.algebraMap_C, hRF, a3, a2, a1, b8, b7,
      betaResidual410, hf2, hf1, hg7, hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (64 * gamma) * h0 ^ 11) := by
    rw [hclear, hgamma]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨64 * gamma, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the degree-one scale divides the
subleading quartic coefficient to order one, the first unused decic
coefficient to order four, `q₇` to order one, and `q₉` to order seven. -/
theorem nonzeroFace410_linearRoot_thirdInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    h0 ∣ p.coeff 3 ∧ h0 ^ 4 ∣ q.coeff 8 ∧
      h0 ∣ q.coeff 7 ∧ h0 ^ 7 ∣ q.coeff 9 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace410_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace410_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  have hq8root : (q.coeff 8).eval a = 0 :=
    nonzeroFace410_linearRoot_q8_zero p q H h0 j lambda a
      hp hq hh0 hH hp4 hq10 hN hD hroot
  have hq8div : h0 ∣ q.coeff 8 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 (q.coeff 8) a
      hh0degree hroot hq8root
  obtain ⟨u, hu⟩ := hq8div
  have hM1 :
      (8 : k[X]) * u - (20 : k[X]) * p.coeff 2 * h0 ^ 5 +
        (9 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 4 -
          (15 : k[X]) * p.coeff 3 ^ 2 * h0 =
        Polynomial.C alpha * h0 ^ 7 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 *
            ((8 : k[X]) * u - (20 : k[X]) * p.coeff 2 * h0 ^ 5 +
              (9 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 4 -
                (15 : k[X]) * p.coeff 3 ^ 2 * h0) =
          localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect410, hu]
        ring
      _ = Polynomial.C alpha * h0 ^ 8 := hM
      _ = h0 * (Polynomial.C alpha * h0 ^ 7) := by ring
  have hu0 : u.eval a = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hM1
    have h8 : (8 : k) ≠ 0 := by norm_num
    have h8u : (8 : k) * u.eval a = 0 := by
      simpa [hroot] using heval
    exact (mul_eq_zero.mp h8u).resolve_left h8
  have hu_div : h0 ∣ u :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 u a hh0degree hroot hu0
  obtain ⟨v, hv⟩ := hu_div
  have hM2 :
      (8 : k[X]) * v - (20 : k[X]) * p.coeff 2 * h0 ^ 4 +
        (9 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 3 -
          (15 : k[X]) * p.coeff 3 ^ 2 =
        Polynomial.C alpha * h0 ^ 6 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 *
            ((8 : k[X]) * v - (20 : k[X]) * p.coeff 2 * h0 ^ 4 +
              (9 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 3 -
                (15 : k[X]) * p.coeff 3 ^ 2) =
          (8 : k[X]) * u - (20 : k[X]) * p.coeff 2 * h0 ^ 5 +
              (9 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 4 -
            (15 : k[X]) * p.coeff 3 ^ 2 * h0 := by
        rw [hv]
        ring
      _ = Polynomial.C alpha * h0 ^ 7 := hM1
      _ = h0 * (Polynomial.C alpha * h0 ^ 6) := by ring
  have hM2root : (8 : k) * v.eval a -
      (15 : k) * ((p.coeff 3).eval a) ^ 2 = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hM2
    simpa [hroot] using heval
  have hq8v : q.coeff 8 = h0 ^ 2 * v := by
    rw [hu, hv]
    ring
  have hT1 :
      (220 : k[X]) * p.coeff 3 ^ 3 - (99 : k[X]) * Polynomial.C lambda *
          p.coeff 3 ^ 2 * h0 ^ 3 - (128 : k[X]) * p.coeff 3 * v +
        (64 : k[X]) * q.coeff 7 * h0 ^ 2 +
        (80 : k[X]) * p.coeff 2 * p.coeff 3 * h0 ^ 4 -
          (160 : k[X]) * p.coeff 1 * h0 ^ 8 +
        (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 7 =
        Polynomial.C gamma * h0 ^ 9 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 *
            ((220 : k[X]) * p.coeff 3 ^ 3 -
                (99 : k[X]) * Polynomial.C lambda * p.coeff 3 ^ 2 *
                  h0 ^ 3 - (128 : k[X]) * p.coeff 3 * v +
              (64 : k[X]) * q.coeff 7 * h0 ^ 2 +
              (80 : k[X]) * p.coeff 2 * p.coeff 3 * h0 ^ 4 -
                (160 : k[X]) * p.coeff 1 * h0 ^ 8 +
              (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 7) =
          localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect410, hq8v]
        ring
      _ = Polynomial.C gamma * h0 ^ 11 := hT
      _ = h0 ^ 2 * (Polynomial.C gamma * h0 ^ 9) := by ring
  have hT1root : (220 : k) * ((p.coeff 3).eval a) ^ 3 -
      (128 : k) * (p.coeff 3).eval a * v.eval a = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hT1
    simpa [hroot] using heval
  have hp3root : (p.coeff 3).eval a = 0 := by
    have h128v :
        (128 : k) * v.eval a =
          (240 : k) * ((p.coeff 3).eval a) ^ 2 := by
      have hscale : (128 : k) = (16 : k) * (8 : k) := by norm_num
      have h240 : (240 : k) = (16 : k) * (15 : k) := by norm_num
      rw [hscale, mul_assoc, h240]
      linear_combination (16 : k) * hM2root
    have hcomb :
        (220 : k) * ((p.coeff 3).eval a) ^ 3 -
            (128 : k) * (p.coeff 3).eval a * v.eval a =
          (-20 : k) * ((p.coeff 3).eval a) ^ 3 := by
      have : (128 : k) * (p.coeff 3).eval a * v.eval a =
          (p.coeff 3).eval a * ((128 : k) * v.eval a) := by ring
      rw [this, h128v]
      ring
    have ha3 : ((p.coeff 3).eval a) ^ 3 = 0 := by
      have hcomb' := hcomb.symm.trans hT1root
      have hneg : (-20 : k) ≠ 0 := by norm_num
      apply (mul_eq_zero.mp ?_).resolve_left hneg
      linear_combination hcomb'
    have hprod :
        (p.coeff 3).eval a *
          ((p.coeff 3).eval a * (p.coeff 3).eval a) = 0 := by
      have hcube :
          (p.coeff 3).eval a *
              ((p.coeff 3).eval a * (p.coeff 3).eval a) =
            ((p.coeff 3).eval a) ^ 3 := by
        ring
      rw [hcube, ha3]
    rcases mul_eq_zero.mp hprod with hp3 | hsq
    · exact hp3
    · exact (mul_eq_zero.mp hsq).elim id id
  have hv0 : v.eval a = 0 := by
    have h8 : (8 : k) ≠ 0 := by norm_num
    have hsq : ((p.coeff 3).eval a) ^ 2 = 0 := by simp [hp3root]
    have : (8 : k) * v.eval a = 0 := by
      linear_combination hM2root + (15 : k) * hsq
    exact (mul_eq_zero.mp this).resolve_left h8
  have hp3div : h0 ∣ p.coeff 3 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 (p.coeff 3) a
      hh0degree hroot hp3root
  have hv_div : h0 ∣ v :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 v a hh0degree hroot hv0
  obtain ⟨t, ht⟩ := hp3div
  obtain ⟨r8, hr8⟩ := hv_div
  have hM3 :
      (8 : k[X]) * r8 - (20 : k[X]) * p.coeff 2 * h0 ^ 3 +
        (9 : k[X]) * Polynomial.C lambda * t * h0 ^ 3 -
          (15 : k[X]) * t ^ 2 * h0 =
        Polynomial.C alpha * h0 ^ 5 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 *
            ((8 : k[X]) * r8 - (20 : k[X]) * p.coeff 2 * h0 ^ 3 +
              (9 : k[X]) * Polynomial.C lambda * t * h0 ^ 3 -
                (15 : k[X]) * t ^ 2 * h0) =
          (8 : k[X]) * v - (20 : k[X]) * p.coeff 2 * h0 ^ 4 +
              (9 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 3 -
            (15 : k[X]) * p.coeff 3 ^ 2 := by
        rw [ht, hr8]
        ring
      _ = Polynomial.C alpha * h0 ^ 6 := hM2
      _ = h0 * (Polynomial.C alpha * h0 ^ 5) := by ring
  have hr80 : r8.eval a = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hM3
    have h8 : (8 : k) ≠ 0 := by norm_num
    have h8r : (8 : k) * r8.eval a = 0 := by
      simpa [hroot] using heval
    exact (mul_eq_zero.mp h8r).resolve_left h8
  have hr8_div : h0 ∣ r8 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 r8 a hh0degree hroot hr80
  obtain ⟨s8, hs8⟩ := hr8_div
  have hq8s : q.coeff 8 = h0 ^ 4 * s8 := by
    rw [hq8v, hr8, hs8]
    ring
  have hp3t : p.coeff 3 = h0 * t := ht
  have hT2 :
      (64 : k[X]) * q.coeff 7 - (128 : k[X]) * t * r8 +
          (220 : k[X]) * t ^ 3 * h0 -
        (99 : k[X]) * Polynomial.C lambda * t ^ 2 * h0 ^ 3 +
        (80 : k[X]) * p.coeff 2 * t * h0 ^ 3 -
          (160 : k[X]) * p.coeff 1 * h0 ^ 6 +
        (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 5 =
        Polynomial.C gamma * h0 ^ 7 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 *
            ((64 : k[X]) * q.coeff 7 - (128 : k[X]) * t * r8 +
                (220 : k[X]) * t ^ 3 * h0 -
              (99 : k[X]) * Polynomial.C lambda * t ^ 2 * h0 ^ 3 +
              (80 : k[X]) * p.coeff 2 * t * h0 ^ 3 -
                (160 : k[X]) * p.coeff 1 * h0 ^ 6 +
              (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 5) =
          (220 : k[X]) * p.coeff 3 ^ 3 -
              (99 : k[X]) * Polynomial.C lambda * p.coeff 3 ^ 2 *
                h0 ^ 3 - (128 : k[X]) * p.coeff 3 * v +
            (64 : k[X]) * q.coeff 7 * h0 ^ 2 +
            (80 : k[X]) * p.coeff 2 * p.coeff 3 * h0 ^ 4 -
              (160 : k[X]) * p.coeff 1 * h0 ^ 8 +
            (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 7 := by
        rw [ht, hr8]
        ring
      _ = Polynomial.C gamma * h0 ^ 9 := hT1
      _ = h0 ^ 2 * (Polynomial.C gamma * h0 ^ 7) := by ring
  have hq7root : (q.coeff 7).eval a = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hT2
    have h64 : (64 : k) ≠ 0 := by norm_num
    have h64q : (64 : k) * (q.coeff 7).eval a -
        (128 : k) * t.eval a * r8.eval a = 0 := by
      simpa [hroot] using heval
    have hr8z : r8.eval a = 0 := hr80
    have : (64 : k) * (q.coeff 7).eval a = 0 := by
      linear_combination h64q + (128 : k) * t.eval a * hr8z
    exact (mul_eq_zero.mp this).resolve_left h64
  have hq7div : h0 ∣ q.coeff 7 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 (q.coeff 7) a
      hh0degree hroot hq7root
  have hq8pow : h0 ^ 4 ∣ q.coeff 8 := ⟨s8, by rw [hq8s]⟩
  have hq9pow : h0 ^ 7 ∣ q.coeff 9 := by
    have h2 : (2 : k) ≠ 0 := by norm_num
    have hN' :
        (2 : k[X]) * q.coeff 9 =
          (5 : k[X]) * p.coeff 3 * h0 ^ 6 -
            Polynomial.C lambda * h0 ^ 9 := by
      have : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := hN
      rw [hH] at this
      have hH3 : (h0 ^ 2) ^ 3 = h0 ^ 6 := by ring
      rw [hH3] at this
      linear_combination -this
    have hform :
        (2 : k[X]) * q.coeff 9 =
          h0 ^ 7 * ((5 : k[X]) * t - Polynomial.C lambda * h0 ^ 2) := by
      rw [hN', hp3t]
      ring
    have hC2 : Polynomial.C (2 : k) = (2 : k[X]) :=
      Polynomial.C_eq_natCast 2
    have hq9eq : q.coeff 9 =
        C ((2 : k)⁻¹) * ((2 : k[X]) * q.coeff 9) := by
      have hone : (C ((2 : k)⁻¹) * C (2 : k) : k[X]) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h2, map_one]
      calc
        q.coeff 9 = (1 : k[X]) * q.coeff 9 := (one_mul _).symm
        _ = (C ((2 : k)⁻¹) * C (2 : k)) * q.coeff 9 := by rw [hone]
        _ = C ((2 : k)⁻¹) * (C (2 : k) * q.coeff 9) := mul_assoc _ _ _
        _ = C ((2 : k)⁻¹) * ((2 : k[X]) * q.coeff 9) := by rw [hC2]
    refine ⟨C ((2 : k)⁻¹) *
        ((5 : k[X]) * t - Polynomial.C lambda * h0 ^ 2), ?_⟩
    rw [hq9eq, hform]
    ring
  exact ⟨⟨t, ht⟩, hq8pow, hq7div, hq9pow⟩

/-- Source-facing third integral for a normalized scale-two `(4,10)`
nonzero face. -/
theorem normalized410ScaleTwo_nonzeroFace_thirdDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda gamma : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda =
          Polynomial.C gamma * h0 ^ 11 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, _a, hh0, hlambda, hh0degree, hH, _hroot, hN⟩ :=
    normalized410ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace410_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4' hq10' hN' hD
  exact ⟨h0, lambda, gamma, hh0, hlambda, hh0degree, hH, hN', hT⟩

/-- Finite local initial packet of a normalized scale-two `(4,10)`
nonzero face: the degree-one scale divides `p₃` to order one, `q₈` to
order four, `q₇` to order one, and `q₉` to order seven. -/
theorem normalized410ScaleTwo_nonzeroFace_thirdInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        h0 ∣ p.coeff 3 ∧ h0 ^ 4 ∣ q.coeff 8 ∧
        h0 ∣ q.coeff 7 ∧ h0 ^ 7 ∣ q.coeff 9 ∧
        (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized410ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨hp3, hq8, hq7, hq9⟩ :=
    nonzeroFace410_linearRoot_thirdInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp3, hq8, hq7,
    hq9, hN'⟩

end NonzeroThirdFace410

#print axioms thirdCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_10_monicQuarticDecic
#print axioms thirdDefect_eq_clearedBeta410
#print axioms nonzeroFace410_thirdDefectPowerRelation
#print axioms nonzeroFace410_linearRoot_thirdInitialPacket
#print axioms normalized410ScaleTwo_nonzeroFace_thirdDefectPowerRelation
#print axioms normalized410ScaleTwo_nonzeroFace_thirdInitialPacket

end Max11DegreeRoutes
