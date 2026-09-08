import LowScale610ScaleTwoSecondFace
import LowScale810ScaleTwoThirdFace

/-! # Scale-two third face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the second face supplies the degree-`13` integral
`P - (5/3) A` and the local vanishing `p₅(a) = 0`.  The next Keller
coefficient is the degree-`12` Jacobian row.  After the same sextic
depression that kills `z⁵`, that row is
`10 B' + 9 L A' - 6 Q' = 0`.  The resulting first integral clears to a
polynomial defect `T` of weight fifteen.

Evaluating the second and third defects together at the root of `h`
forces the finite initial jet `h³ ∣ p₅`, `h⁴ ∣ q₈`, `h ∣ q₇`, and
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
degrees `(6,10)`.  It is the source of the first mixed sextic/decic
`z³`/`z⁷` defect after the degree-`13` integral. -/
theorem thirdCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 7).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 8).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 9).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 10).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 12) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (12 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 12 :
      Finset (ℕ × ℕ)) =
      ({(0, 12), (1, 11), (2, 10), (3, 9), (4, 8), (5, 7), (6, 6),
        (7, 5), (8, 4), (9, 3), (10, 2), (11, 1),
        (12, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC7, hC8, hC9, hC10, hC6, hC5, hC4, hC3]
  linear_combination hcoeff

/-! ## Sextic `z³` and decic `z⁷` coordinates -/

section Depression610Third

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed sextic `z³` coefficient. -/
abbrev depressedB610 (h r a5 a4 a3 : F) : F :=
  depressedB68 h r a5 a4 a3

/-- Depressed decic `z⁷` coefficient. -/
abbrev depressedQ610 (h r b9 b8 b7 : F) : F :=
  depressedQ810 h r b9 b8 b7

/-- First residual of the degree-`12` row. -/
def betaResidual610 (L A B Q : F) : F :=
  Q - (5 / 3 : F) * B - (3 / 2 : F) * L * A

/-- Polynomial numerator of `648 h¹⁵ (Q - (5/3) B - (3/2) L A)` on the
ninth-power face. -/
def localClearedThirdDefect610
    (h a5 a4 a3 b8 b7 : F[X]) (lambda : F) : F[X] :=
  (520 : F[X]) * a5 ^ 3 -
    (864 : F[X]) * a5 * b8 * h ^ 2 -
    (351 : F[X]) * Polynomial.C lambda * a5 ^ 2 * h ^ 5 +
    (720 : F[X]) * a4 * a5 * h ^ 6 +
    (648 : F[X]) * b7 * h ^ 8 +
    (324 : F[X]) * Polynomial.C lambda * a4 * h ^ 11 -
    (1080 : F[X]) * a3 * h ^ 12

theorem coeff_depressedSextic68_three
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 3 = B := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the sextic `z³` coordinate. -/
theorem depressedB610_eq_cleared
    (h a5 a4 a3 : F) (hh : h ≠ 0) :
    depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 =
      (54 * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3) /
        (54 * h ^ 15) := by
  simp only [depressedB610, depressedB68, sexticDepressionR610,
    sexticDepressionR68]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z⁷` coordinate on the
ninth-power face. -/
theorem depressedQ610_eq_cleared
    (h a5 b9 b8 b7 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7 =
      (10 * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
          12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8) /
        (9 * h ^ 15) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedQ610, depressedQ810, sexticDepressionR610,
    sexticDepressionR68]
  have hrewrite :
      -120 * (a5 / (6 * h ^ 5)) ^ 3 +
          36 * (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 2 -
        8 * (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) + b7 / h ^ 7 =
        (10 * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
            12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8) /
          (9 * h ^ 15) := by
    field_simp [hh, h6, h3, hh4, hh5, hh7, hh8pow, hh9, hh15]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh4, hh5, hh7, hh8pow, hh9, hh15]
    ring
  exact hrewrite

/-- Clearing the first integral `Q - (5/3) B - (3/2) L A` against `h¹⁵`
on the ninth-power face. -/
theorem thirdDefect_eq_clearedBeta610
    (h a5 a4 a3 b9 b8 b7 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (648 : F) * h ^ 15 *
        betaResidual610
          (depressedL610 h (sexticDepressionR610 h a5) b9)
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
          (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
          (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7) =
      (520 : F) * a5 ^ 3 - (864 : F) * a5 * b8 * h ^ 2 -
        (351 : F) * lambda * a5 ^ 2 * h ^ 5 +
        (720 : F) * a4 * a5 * h ^ 6 + (648 : F) * b7 * h ^ 8 +
        (324 : F) * lambda * a4 * h ^ 11 - (1080 : F) * a3 * h ^ 12 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h54 : (54 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hL :
      depressedL610 h (sexticDepressionR610 h a5) b9 = -lambda / 3 :=
    depressedL610_eq_of_ninthPower h a5 b9 lambda hh hN
  have hA :
      depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (12 * a4 * h ^ 6 - 5 * a5 ^ 2) / (12 * h ^ 10) :=
    depressedA610_eq_cleared h a5 a4 hh
  have hB :
      depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 =
        (54 * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3) /
          (54 * h ^ 15) :=
    depressedB610_eq_cleared h a5 a4 a3 hh
  have hQ :
      depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7 =
        (10 * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
            12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8) /
          (9 * h ^ 15) :=
    depressedQ610_eq_cleared h a5 b9 b8 b7 lambda hh hN
  have h648Q :
      (648 : F) * h ^ 15 *
          depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7 =
        (720 : F) * a5 ^ 3 - (216 : F) * lambda * a5 ^ 2 * h ^ 5 -
          (864 : F) * a5 * b8 * h ^ 2 + (648 : F) * b7 * h ^ 8 := by
    rw [hQ]
    field_simp [hh, h9, hh15]
    ring
  have h1080B :
      (1080 : F) * h ^ 15 *
          depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 =
        (1080 : F) * a3 * h ^ 12 - (720 : F) * a4 * a5 * h ^ 6 +
          (200 : F) * a5 ^ 3 := by
    rw [hB]
    field_simp [hh, h54, hh15]
    ring
  have h324A :
      (324 : F) * lambda * h ^ 15 *
          depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (324 : F) * lambda * a4 * h ^ 11 -
          (135 : F) * lambda * a5 ^ 2 * h ^ 5 := by
    rw [hA]
    field_simp [hh, h12, hh10, hh15]
    ring
  have hdiff :
      (648 : F) * h ^ 15 *
          betaResidual610
            (depressedL610 h (sexticDepressionR610 h a5) b9)
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
            (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
            (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7) =
        (648 : F) * h ^ 15 *
            depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7 -
          (1080 : F) * h ^ 15 *
            depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 +
          (324 : F) * lambda * h ^ 15 *
            depressedA610 h (sexticDepressionR610 h a5) a5 a4 := by
    simp only [betaResidual610, hL]
    field_simp [h2, h3]
    ring
  rw [hdiff, h648Q, h1080B, h324A]
  ring

end Depression610Third

/-! ## Degree-`12` depressed Jacobian coefficient -/

section DepressedRow610Third

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`12` Jacobian coefficient is
exactly `10 B' + 9 L A' - 6 Q'`. -/
theorem differentialJacobian_coeff_12_monicSexticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 12 =
      (10 : F) * d (f.coeff 3) + (9 : F) * g.coeff 9 * d (f.coeff 4) -
        (6 : F) * d (g.coeff 7) := by
  have hfd_high : ∀ n, 5 ≤ n → (coefficientDeriv d f).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      simpa [hf5]
    · have : 6 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq6 | hlt6
      · subst n
        simpa [hf6, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hf_high n (by omega))
  have hgd_high : ∀ n, 10 ≤ n → g.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 10 < n + 1 := by omega
    simp [hg_high (n + 1) this]
  have hfd'_high : ∀ n, 6 ≤ n → f.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 6 < n + 1 := by omega
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
  have hmem39 : ((3, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem48 : ((4, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem57 : ((5, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 12 =
        (10 : F) * d (f.coeff 3) +
          (9 : F) * g.coeff 9 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne : ((3, 9) : ℕ × ℕ) ≠ (4, 8) := by decide
    have hsubset : ({(3, 9), (4, 8)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (12 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · subst b
        exact hmem39
      · subst b
        exact hmem48
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(3, 9), (4, 8)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 12 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne39 : b ≠ (3, 9) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne48 : b ≠ (4, 8) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 5 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne3 : b.1 ≠ 3 := by
          intro h3
          apply hne39
          ext
          · exact h3
          · omega
        have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne48
          ext
          · exact h4
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(3, 9), (4, 8)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 3 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 8 := by
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
      (f.derivative * coefficientDeriv d g).coeff 12 =
        (6 : F) * d (g.coeff 7) := by
    have hprod :
        (f.derivative * coefficientDeriv d g).coeff 12 =
          f.derivative.coeff 5 * (coefficientDeriv d g).coeff 7 := by
      rw [Polynomial.coeff_mul]
      refine Finset.sum_eq_single_of_mem _ hmem57 ?_
      intro b hb hne
      have hij : b.1 + b.2 = 12 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hi : b.1 ≠ 5 := by
        intro h5
        apply hne
        ext
        · exact h5
        · omega
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h4 : b.1 = 4
        · have hf4 : f.derivative.coeff b.1 = 0 := by
            rw [h4, Polynomial.coeff_derivative, hf5]
            simp
          simp [hf4]
        · have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hder : f.derivative.coeff 5 = (6 : F) := by
      rw [Polynomial.coeff_derivative, hf6]
      norm_num
    rw [hprod, coeff_coefficientDeriv, hder]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]

theorem betaResidual610_deriv_zero
    (d : Derivation k F F) (L A B Q : F)
    (hL : d L = 0)
    (hrow : (10 : F) * d B + (9 : F) * L * d A - (6 : F) * d Q = 0) :
    d (betaResidual610 L A B Q) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h53 : d (5 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h5]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  simp only [betaResidual610, map_sub, Derivation.leibniz, h53, h32, hL,
    zero_mul, add_zero, mul_zero]
  linear_combination (-1 / 6 : F) * hrow

end DepressedRow610Third

/-! ## Source-facing third-face packet -/

section NonzeroThirdFace610

variable {k : Type*} [Field k] [CharZero k]

/-- The second sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h¹⁵`. -/
theorem nonzeroFace610_thirdDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ gamma : k,
      localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (q.coeff 8) (q.coeff 7) lambda =
        Polynomial.C gamma * h0 ^ 15 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    simp only [hp6, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  have hNrat : 5 * a5 * hRF ^ 4 - 3 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) (h0 ^ 9) = hRF ^ 9 := by
      simp only [hRF, map_pow]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * h0 ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hLval :
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 =
        RatFunc.C (-lambda / 3) := by
    have hL := depressedL610_eq_of_ninthPower hRF a5 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (sexticDepressionR610 hRF a5) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 q)
  have hf5 : f.coeff 5 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_five]
  have hf6 : f.coeff 6 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_six]
  have hf_high : ∀ n, 6 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_of_gt_six _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, _, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedQ610, depressedQ810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 3) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * sexticDepressionR610 hRF a5 +
        (sourceToRatFunc68 q).coeff 9 / hRF ^ 9 =
          depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 3) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow :
      (differentialJacobian ratFuncDerivation68 f g).coeff 12 =
        (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) := by
    exact differentialJacobian_coeff_12_monicSexticDecic
      ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
  have hrow0 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 12) hbracket
    simpa [f, g, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf4 : f.coeff 4 = depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
    dsimp only [f, depressedA610, a5, a4]
    rw [hpDep, coeff_depressedSextic68_four]
  have hf3 : f.coeff 3 =
      depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 := by
    dsimp only [f, depressedB610, a5, a4, a3]
    rw [hpDep, coeff_depressedSextic68_three]
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (g.coeff 7)) = 0 :=
    betaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (g.coeff 7) hLconst (by simpa using hrow0)
  obtain ⟨gamma, hgamma⟩ :
      ∃ a : k,
        betaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (g.coeff 7) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hbeta0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda) =
        (648 : RatFunc k) * hRF ^ 15 *
          betaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (g.coeff 7) := by
    have hF := thirdDefect_eq_clearedBeta610 hRF a5 a4 a3 b9 b8 b7
      (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedThirdDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, RatFunc.algebraMap_C, hRF, a5, a4, a3, b8, b7,
      betaResidual610, hf4, hf3, hg7, hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (648 * gamma) * h0 ^ 15) := by
    rw [hclear, hgamma]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨648 * gamma, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the degree-one scale divides the
subleading sextic coefficient to order three, the first unused decic
coefficient to order four, `q₇` to order one, and `q₉` to order seven. -/
theorem nonzeroFace610_linearRoot_thirdInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 8 ∧
      h0 ∣ q.coeff 7 ∧ h0 ^ 7 ∣ q.coeff 9 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace610_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace610_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have hp5root : (p.coeff 5).eval a = 0 :=
    nonzeroFace610_linearRoot_p5_zero p q H h0 j lambda a
      hp hq hh0 hH hp6 hq10 hN hD hroot
  have hp5div : h0 ∣ p.coeff 5 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 5) a
      hh0degree hroot hp5root
  obtain ⟨u, hu⟩ := hp5div
  have hM1 :
      (18 : k[X]) * q.coeff 8 - (30 : k[X]) * p.coeff 4 * h0 ^ 4 +
        (9 : k[X]) * Polynomial.C lambda * u * h0 ^ 4 -
          (10 : k[X]) * u ^ 2 =
        Polynomial.C alpha * h0 ^ 8 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 *
            ((18 : k[X]) * q.coeff 8 - (30 : k[X]) * p.coeff 4 * h0 ^ 4 +
              (9 : k[X]) * Polynomial.C lambda * u * h0 ^ 4 -
                (10 : k[X]) * u ^ 2) =
          localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect610, hu]
        ring
      _ = Polynomial.C alpha * h0 ^ 10 := hM
      _ = h0 ^ 2 * (Polynomial.C alpha * h0 ^ 8) := by ring
  have hMroot : (18 : k) * (q.coeff 8).eval a -
      (10 : k) * (u.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hM1
    simpa [hroot] using heval
  have hT1 :
      (520 : k[X]) * u ^ 3 - (864 : k[X]) * u * q.coeff 8 -
          (351 : k[X]) * Polynomial.C lambda * u ^ 2 * h0 ^ 4 +
        (720 : k[X]) * p.coeff 4 * u * h0 ^ 4 +
          (648 : k[X]) * q.coeff 7 * h0 ^ 5 +
        (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 8 -
          (1080 : k[X]) * p.coeff 3 * h0 ^ 9 =
        Polynomial.C gamma * h0 ^ 12 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    calc
      h0 ^ 3 *
            ((520 : k[X]) * u ^ 3 - (864 : k[X]) * u * q.coeff 8 -
                (351 : k[X]) * Polynomial.C lambda * u ^ 2 * h0 ^ 4 +
              (720 : k[X]) * p.coeff 4 * u * h0 ^ 4 +
                (648 : k[X]) * q.coeff 7 * h0 ^ 5 +
              (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 8 -
                (1080 : k[X]) * p.coeff 3 * h0 ^ 9) =
          localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect610, hu]
        ring
      _ = Polynomial.C gamma * h0 ^ 15 := hT
      _ = h0 ^ 3 * (Polynomial.C gamma * h0 ^ 12) := by ring
  have hTroot : (520 : k) * (u.eval a) ^ 3 -
      (864 : k) * u.eval a * (q.coeff 8).eval a = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hT1
    simpa [hroot] using heval
  have hu0 : u.eval a = 0 := by
    have h40 : (40 : k) ≠ 0 := by norm_num
    have h864b :
        (864 : k) * (q.coeff 8).eval a =
          (480 : k) * (u.eval a) ^ 2 := by
      have hscale : (864 : k) = (48 : k) * (18 : k) := by norm_num
      have h480 : (480 : k) = (48 : k) * (10 : k) := by norm_num
      rw [hscale, mul_assoc, h480]
      linear_combination (48 : k) * hMroot
    have hcomb :
        (520 : k) * (u.eval a) ^ 3 -
            (864 : k) * u.eval a * (q.coeff 8).eval a =
          (40 : k) * (u.eval a) ^ 3 := by
      have : (864 : k) * u.eval a * (q.coeff 8).eval a =
          u.eval a * ((864 : k) * (q.coeff 8).eval a) := by ring
      rw [this, h864b]
      ring
    have hu3 : (u.eval a) ^ 3 = 0 := by
      have hcomb' := hcomb.symm.trans hTroot
      apply (mul_eq_zero.mp ?_).resolve_left h40
      linear_combination hcomb'
    have hprod : u.eval a * (u.eval a * u.eval a) = 0 := by
      have hcube : u.eval a * (u.eval a * u.eval a) = (u.eval a) ^ 3 := by
        ring
      rw [hcube, hu3]
    rcases mul_eq_zero.mp hprod with hu | hsq
    · exact hu
    · exact (mul_eq_zero.mp hsq).elim id id
  have hb8root : (q.coeff 8).eval a = 0 := by
    have h18 : (18 : k) ≠ 0 := by norm_num
    have husq : (u.eval a) ^ 2 = 0 := by simp [hu0]
    have : (18 : k) * (q.coeff 8).eval a = 0 := by
      linear_combination hMroot + (10 : k) * husq
    exact (mul_eq_zero.mp this).resolve_left h18
  have hu_div : h0 ∣ u :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 u a hh0degree hroot hu0
  have hb8div : h0 ∣ q.coeff 8 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 8) a
      hh0degree hroot hb8root
  obtain ⟨v, hv⟩ := hu_div
  obtain ⟨s, hs⟩ := hb8div
  have hM2 :
      (18 : k[X]) * s - (30 : k[X]) * p.coeff 4 * h0 ^ 3 +
        (9 : k[X]) * Polynomial.C lambda * v * h0 ^ 4 -
          (10 : k[X]) * v ^ 2 * h0 =
        Polynomial.C alpha * h0 ^ 7 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 *
            ((18 : k[X]) * s - (30 : k[X]) * p.coeff 4 * h0 ^ 3 +
              (9 : k[X]) * Polynomial.C lambda * v * h0 ^ 4 -
                (10 : k[X]) * v ^ 2 * h0) =
          (18 : k[X]) * q.coeff 8 - (30 : k[X]) * p.coeff 4 * h0 ^ 4 +
              (9 : k[X]) * Polynomial.C lambda * u * h0 ^ 4 -
            (10 : k[X]) * u ^ 2 := by
        rw [hs, hv]
        ring
      _ = Polynomial.C alpha * h0 ^ 8 := hM1
      _ = h0 * (Polynomial.C alpha * h0 ^ 7) := by ring
  have hs0 : s.eval a = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hM2
    have h18 : (18 : k) ≠ 0 := by norm_num
    have h18s : (18 : k) * s.eval a = 0 := by
      simpa [hroot] using heval
    exact (mul_eq_zero.mp h18s).resolve_left h18
  have hs_div : h0 ∣ s :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 s a hh0degree hroot hs0
  obtain ⟨t, ht⟩ := hs_div
  have hM3 :
      (18 : k[X]) * t - (30 : k[X]) * p.coeff 4 * h0 ^ 2 +
        (9 : k[X]) * Polynomial.C lambda * v * h0 ^ 3 -
          (10 : k[X]) * v ^ 2 =
        Polynomial.C alpha * h0 ^ 6 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 *
            ((18 : k[X]) * t - (30 : k[X]) * p.coeff 4 * h0 ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * v * h0 ^ 3 -
                (10 : k[X]) * v ^ 2) =
          (18 : k[X]) * s - (30 : k[X]) * p.coeff 4 * h0 ^ 3 +
              (9 : k[X]) * Polynomial.C lambda * v * h0 ^ 4 -
            (10 : k[X]) * v ^ 2 * h0 := by
        rw [ht]
        ring
      _ = Polynomial.C alpha * h0 ^ 7 := hM2
      _ = h0 * (Polynomial.C alpha * h0 ^ 6) := by ring
  have hM3root : (18 : k) * t.eval a - (10 : k) * (v.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hM3
    simpa [hroot] using heval
  have hT2 :
      (520 : k[X]) * v ^ 3 - (864 : k[X]) * v * t -
          (351 : k[X]) * Polynomial.C lambda * v ^ 2 * h0 ^ 3 +
        (720 : k[X]) * p.coeff 4 * v * h0 ^ 2 +
          (648 : k[X]) * q.coeff 7 * h0 ^ 2 +
        (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 5 -
          (1080 : k[X]) * p.coeff 3 * h0 ^ 6 =
        Polynomial.C gamma * h0 ^ 9 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    calc
      h0 ^ 3 *
            ((520 : k[X]) * v ^ 3 - (864 : k[X]) * v * t -
                (351 : k[X]) * Polynomial.C lambda * v ^ 2 * h0 ^ 3 +
              (720 : k[X]) * p.coeff 4 * v * h0 ^ 2 +
                (648 : k[X]) * q.coeff 7 * h0 ^ 2 +
              (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 5 -
                (1080 : k[X]) * p.coeff 3 * h0 ^ 6) =
          (520 : k[X]) * u ^ 3 - (864 : k[X]) * u * q.coeff 8 -
              (351 : k[X]) * Polynomial.C lambda * u ^ 2 * h0 ^ 4 +
            (720 : k[X]) * p.coeff 4 * u * h0 ^ 4 +
              (648 : k[X]) * q.coeff 7 * h0 ^ 5 +
            (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 8 -
              (1080 : k[X]) * p.coeff 3 * h0 ^ 9 := by
        rw [hv, hs, ht]
        ring
      _ = Polynomial.C gamma * h0 ^ 12 := hT1
      _ = h0 ^ 3 * (Polynomial.C gamma * h0 ^ 9) := by ring
  have hT2root : (520 : k) * (v.eval a) ^ 3 -
      (864 : k) * v.eval a * t.eval a = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hT2
    simpa [hroot] using heval
  have hv0 : v.eval a = 0 := by
    have h40 : (40 : k) ≠ 0 := by norm_num
    have h864t :
        (864 : k) * t.eval a =
          (480 : k) * (v.eval a) ^ 2 := by
      have hscale : (864 : k) = (48 : k) * (18 : k) := by norm_num
      have h480 : (480 : k) = (48 : k) * (10 : k) := by norm_num
      rw [hscale, mul_assoc, h480]
      linear_combination (48 : k) * hM3root
    have hcomb :
        (520 : k) * (v.eval a) ^ 3 -
            (864 : k) * v.eval a * t.eval a =
          (40 : k) * (v.eval a) ^ 3 := by
      have : (864 : k) * v.eval a * t.eval a =
          v.eval a * ((864 : k) * t.eval a) := by ring
      rw [this, h864t]
      ring
    have hv3 : (v.eval a) ^ 3 = 0 := by
      have hcomb' := hcomb.symm.trans hT2root
      apply (mul_eq_zero.mp ?_).resolve_left h40
      linear_combination hcomb'
    have hprod : v.eval a * (v.eval a * v.eval a) = 0 := by
      have hcube : v.eval a * (v.eval a * v.eval a) = (v.eval a) ^ 3 := by
        ring
      rw [hcube, hv3]
    rcases mul_eq_zero.mp hprod with hv | hsq
    · exact hv
    · exact (mul_eq_zero.mp hsq).elim id id
  have ht0 : t.eval a = 0 := by
    have h18 : (18 : k) ≠ 0 := by norm_num
    have hvsq : (v.eval a) ^ 2 = 0 := by simp [hv0]
    have : (18 : k) * t.eval a = 0 := by
      linear_combination hM3root + (10 : k) * hvsq
    exact (mul_eq_zero.mp this).resolve_left h18
  have hv_div : h0 ∣ v :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 v a hh0degree hroot hv0
  have ht_div : h0 ∣ t :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 t a hh0degree hroot ht0
  obtain ⟨w, hw⟩ := hv_div
  obtain ⟨r8, hr8⟩ := ht_div
  have hp5w : p.coeff 5 = h0 ^ 3 * w := by
    rw [hu, hv, hw]
    ring
  have hq8r : q.coeff 8 = h0 ^ 3 * r8 := by
    rw [hs, ht, hr8]
    ring
  have hM4 :
      (18 : k[X]) * r8 - (30 : k[X]) * p.coeff 4 * h0 +
        (9 : k[X]) * Polynomial.C lambda * w * h0 ^ 3 -
          (10 : k[X]) * w ^ 2 * h0 =
        Polynomial.C alpha * h0 ^ 5 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 *
            ((18 : k[X]) * r8 - (30 : k[X]) * p.coeff 4 * h0 +
              (9 : k[X]) * Polynomial.C lambda * w * h0 ^ 3 -
                (10 : k[X]) * w ^ 2 * h0) =
          (18 : k[X]) * t - (30 : k[X]) * p.coeff 4 * h0 ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * v * h0 ^ 3 -
            (10 : k[X]) * v ^ 2 := by
        rw [hr8, hw]
        ring
      _ = Polynomial.C alpha * h0 ^ 6 := hM3
      _ = h0 * (Polynomial.C alpha * h0 ^ 5) := by ring
  have hr80 : r8.eval a = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hM4
    have h18 : (18 : k) ≠ 0 := by norm_num
    have h18r : (18 : k) * r8.eval a = 0 := by
      simpa [hroot] using heval
    exact (mul_eq_zero.mp h18r).resolve_left h18
  have hr8_div : h0 ∣ r8 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 r8 a hh0degree hroot hr80
  obtain ⟨s8, hs8⟩ := hr8_div
  have hT3 :
      (648 : k[X]) * q.coeff 7 - (864 : k[X]) * w * r8 +
          (520 : k[X]) * w ^ 3 * h0 +
        (720 : k[X]) * p.coeff 4 * w * h0 -
          (351 : k[X]) * Polynomial.C lambda * w ^ 2 * h0 ^ 3 +
        (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 3 -
          (1080 : k[X]) * p.coeff 3 * h0 ^ 4 =
        Polynomial.C gamma * h0 ^ 7 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 *
            ((648 : k[X]) * q.coeff 7 - (864 : k[X]) * w * r8 +
                (520 : k[X]) * w ^ 3 * h0 +
              (720 : k[X]) * p.coeff 4 * w * h0 -
                (351 : k[X]) * Polynomial.C lambda * w ^ 2 * h0 ^ 3 +
              (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 3 -
                (1080 : k[X]) * p.coeff 3 * h0 ^ 4) =
          (520 : k[X]) * v ^ 3 - (864 : k[X]) * v * t -
              (351 : k[X]) * Polynomial.C lambda * v ^ 2 * h0 ^ 3 +
            (720 : k[X]) * p.coeff 4 * v * h0 ^ 2 +
              (648 : k[X]) * q.coeff 7 * h0 ^ 2 +
            (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 5 -
              (1080 : k[X]) * p.coeff 3 * h0 ^ 6 := by
        rw [hw, hr8]
        ring
      _ = Polynomial.C gamma * h0 ^ 9 := hT2
      _ = h0 ^ 2 * (Polynomial.C gamma * h0 ^ 7) := by ring
  have hq7root : (q.coeff 7).eval a = 0 := by
    have heval := congrArg (fun poly : k[X] => poly.eval a) hT3
    have h648 : (648 : k) ≠ 0 := by norm_num
    have h648q : (648 : k) * (q.coeff 7).eval a -
        (864 : k) * w.eval a * r8.eval a = 0 := by
      simpa [hroot] using heval
    have hr8sq : r8.eval a = 0 := hr80
    have : (648 : k) * (q.coeff 7).eval a = 0 := by
      linear_combination h648q + (864 : k) * w.eval a * hr8sq
    exact (mul_eq_zero.mp this).resolve_left h648
  have hq7div : h0 ∣ q.coeff 7 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 7) a
      hh0degree hroot hq7root
  have hp5pow : h0 ^ 3 ∣ p.coeff 5 := ⟨w, by rw [hp5w]⟩
  have hq8pow : h0 ^ 4 ∣ q.coeff 8 := by
    refine ⟨s8, ?_⟩
    rw [hq8r, hs8]
    ring
  have hq9pow : h0 ^ 7 ∣ q.coeff 9 := by
    have h3 : (3 : k) ≠ 0 := by norm_num
    have hN' :
        (3 : k[X]) * q.coeff 9 =
          (5 : k[X]) * p.coeff 5 * h0 ^ 4 -
            Polynomial.C lambda * h0 ^ 9 := by
      have : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := hN
      rw [hH] at this
      linear_combination -this
    have hform :
        (3 : k[X]) * q.coeff 9 =
          h0 ^ 7 * ((5 : k[X]) * w - Polynomial.C lambda * h0 ^ 2) := by
      rw [hN', hp5w]
      ring
    have hC3 : Polynomial.C (3 : k) = (3 : k[X]) :=
      Polynomial.C_eq_natCast 3
    have hq9eq : q.coeff 9 =
        C ((3 : k)⁻¹) * ((3 : k[X]) * q.coeff 9) := by
      have hone : (C ((3 : k)⁻¹) * C (3 : k) : k[X]) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h3, map_one]
      calc
        q.coeff 9 = (1 : k[X]) * q.coeff 9 := (one_mul _).symm
        _ = (C ((3 : k)⁻¹) * C (3 : k)) * q.coeff 9 := by rw [hone]
        _ = C ((3 : k)⁻¹) * (C (3 : k) * q.coeff 9) := mul_assoc _ _ _
        _ = C ((3 : k)⁻¹) * ((3 : k[X]) * q.coeff 9) := by rw [hC3]
    refine ⟨C ((3 : k)⁻¹) *
        ((5 : k[X]) * w - Polynomial.C lambda * h0 ^ 2), ?_⟩
    rw [hq9eq, hform]
    ring
  exact ⟨hp5pow, hq8pow, hq7div, hq9pow⟩

/-- Source-facing third integral for a normalized scale-two `(6,10)`
nonzero face. -/
theorem normalized610ScaleTwo_nonzeroFace_thirdDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda gamma : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda =
          Polynomial.C gamma * h0 ^ 15 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, _hroot, hN⟩ :=
    normalized610ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace610_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6' hq10' hN' hD
  exact ⟨h0, lambda, gamma, hh0, hlambda, hh0degree, hH, hN', hT⟩

/-- Finite local initial packet of a normalized scale-two `(6,10)`
nonzero face: the degree-one scale divides `p₅` to order three, `q₈` to
order four, `q₇` to order one, and `q₉` to order seven. -/
theorem normalized610ScaleTwo_nonzeroFace_thirdInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 8 ∧
        h0 ∣ q.coeff 7 ∧ h0 ^ 7 ∣ q.coeff 9 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized610ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨hp5, hq8, hq7, hq9⟩ :=
    nonzeroFace610_linearRoot_thirdInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp5, hq8, hq7,
    hq9, hN'⟩

end NonzeroThirdFace610

#print axioms thirdCoefficientJacobianRow_610
#print axioms differentialJacobian_coeff_12_monicSexticDecic
#print axioms thirdDefect_eq_clearedBeta610
#print axioms nonzeroFace610_thirdDefectPowerRelation
#print axioms nonzeroFace610_linearRoot_thirdInitialPacket
#print axioms normalized610ScaleTwo_nonzeroFace_thirdDefectPowerRelation
#print axioms normalized610ScaleTwo_nonzeroFace_thirdInitialPacket

end Max11DegreeRoutes
