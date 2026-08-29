import LowScale810ScaleTwoSecondFace

/-! # Scale-two third face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the second face supplies the degree-`15` integral
`P - (5/4) A` and the local vanishing `p₇(a) = 0`.  The next Keller
coefficient is the degree-`14` Jacobian row.  After the same octic
depression that kills `z⁷`, that row is
`10 B' + 9 L A' - 8 Q' = 0`.  The resulting first integral clears to a
polynomial defect `T` of weight twenty-one.

Evaluating the second and third defects together at the root of `h`
forces the finite initial jet `h⁴ ∣ p₇`, `h² ∣ q₈`, and `h⁶ ∣ q₉`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The third row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  It is the source of the first mixed octic/decic
`z⁵`/`z⁷` defect after the degree-`15` integral. -/
theorem thirdCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 7).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 6).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 5).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 7).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 8).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 9).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 10).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 14) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (14 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 14 :
      Finset (ℕ × ℕ)) =
      ({(0, 14), (1, 13), (2, 12), (3, 11), (4, 10), (5, 9), (6, 8),
        (7, 7), (8, 6), (9, 5), (10, 4), (11, 3), (12, 2), (13, 1),
        (14, 0)} : Finset (ℕ × ℕ)) := by decide
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
  rw [hC8, hC9, hC10, hC7, hC6, hC5]
  linear_combination hcoeff

/-! ## Octic `z⁵` and decic `z⁷` coordinates -/

section Depression810Third

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed octic `z⁵` coefficient. -/
def depressedB810 (h r a7 a6 a5 : F) : F :=
  depressedQ68 h r a7 a6 a5

/-- Depressed decic `z⁷` coefficient. -/
def depressedQ810 (h r b9 b8 b7 : F) : F :=
  -120 * r ^ 3 + 36 * (b9 / h ^ 9) * r ^ 2 -
    8 * (b8 / h ^ 8) * r + b7 / h ^ 7

/-- First residual of the degree-`14` row. -/
def betaResidual810 (L A B Q : F) : F :=
  Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A

/-- Polynomial numerator of `512 h²¹ (Q - (5/4) B - (9/8) L A)` on the
ninth-power face. -/
def localClearedThirdDefect810
    (h a7 a6 a5 b8 b7 : F[X]) (lambda : F) : F[X] :=
  (100 : F[X]) * a7 ^ 3 -
    (512 : F[X]) * a7 * b8 * h ^ 6 -
    (135 : F[X]) * Polynomial.C lambda * a7 ^ 2 * h ^ 7 +
    (480 : F[X]) * a6 * a7 * h ^ 8 +
    (512 : F[X]) * b7 * h ^ 14 +
    (144 : F[X]) * Polynomial.C lambda * a6 * h ^ 15 -
    (640 : F[X]) * a5 * h ^ 16

theorem coeff_depressedOctic68_five
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 5 = Q := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the octic `z⁵` coordinate. -/
theorem depressedB810_eq_cleared
    (h a7 a6 a5 : F) (hh : h ≠ 0) :
    depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
      (32 * a5 * h ^ 16 - 24 * a6 * a7 * h ^ 8 + 7 * a7 ^ 3) /
        (32 * h ^ 21) := by
  simp only [depressedB810, depressedQ68, octicDepressionR810]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z⁷` coordinate on the
ninth-power face. -/
theorem depressedQ810_eq_cleared
    (h a7 b9 b8 b7 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 =
      (64 * b7 * h ^ 14 - 64 * a7 * b8 * h ^ 6 -
          9 * lambda * a7 ^ 2 * h ^ 7 + 30 * a7 ^ 3) /
        (64 * h ^ 21) := by
  have h8 : (8 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hb9 : 4 * b9 = 5 * a7 * h ^ 2 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedQ810, octicDepressionR810]
  have hrewrite :
      -120 * (a7 / (8 * h ^ 7)) ^ 3 +
          36 * (b9 / h ^ 9) * (a7 / (8 * h ^ 7)) ^ 2 -
        8 * (b8 / h ^ 8) * (a7 / (8 * h ^ 7)) + b7 / h ^ 7 =
        (64 * b7 * h ^ 14 - 64 * a7 * b8 * h ^ 6 -
            9 * lambda * a7 ^ 2 * h ^ 7 + 30 * a7 ^ 3) /
          (64 * h ^ 21) := by
    field_simp [hh, h8, hh2, hh7, hh8pow, hh9, hh21]
    have hb9' :
        b9 = (5 * a7 * h ^ 2 - lambda * h ^ 9) / 4 := by
      have h4 : (4 : F) ≠ 0 := by norm_num
      field_simp [h4]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h8, hh2, hh7, hh8pow, hh9, hh21]
    ring
  exact hrewrite

/-- Clearing the first integral `Q - (5/4) B - (9/8) L A` against `h²¹`
on the ninth-power face. -/
theorem thirdDefect_eq_clearedBeta810
    (h a7 a6 a5 b9 b8 b7 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (512 : F) * h ^ 21 *
        betaResidual810
          (depressedL810 h (octicDepressionR810 h a7) b9)
          (depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7) =
      (100 : F) * a7 ^ 3 - (512 : F) * a7 * b8 * h ^ 6 -
        (135 : F) * lambda * a7 ^ 2 * h ^ 7 +
        (480 : F) * a6 * a7 * h ^ 8 + (512 : F) * b7 * h ^ 14 +
        (144 : F) * lambda * a6 * h ^ 15 - (640 : F) * a5 * h ^ 16 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
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
  have hQ :
      depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 =
        (64 * b7 * h ^ 14 - 64 * a7 * b8 * h ^ 6 -
            9 * lambda * a7 ^ 2 * h ^ 7 + 30 * a7 ^ 3) /
          (64 * h ^ 21) :=
    depressedQ810_eq_cleared h a7 b9 b8 b7 lambda hh hN
  have h512Q :
      (512 : F) * h ^ 21 *
          depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 =
        (512 : F) * b7 * h ^ 14 - (512 : F) * a7 * b8 * h ^ 6 -
          (72 : F) * lambda * a7 ^ 2 * h ^ 7 + (240 : F) * a7 ^ 3 := by
    rw [hQ]
    field_simp [hh, h64, hh21]
    ring
  have h640B :
      (640 : F) * h ^ 21 *
          depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
        (640 : F) * a5 * h ^ 16 - (480 : F) * a6 * a7 * h ^ 8 +
          (140 : F) * a7 ^ 3 := by
    rw [hB]
    field_simp [hh, h32, hh21]
    ring
  have h144A :
      (144 : F) * lambda * h ^ 21 *
          depressedA810 h (octicDepressionR810 h a7) a7 a6 =
        (144 : F) * lambda * a6 * h ^ 15 -
          (63 : F) * lambda * a7 ^ 2 * h ^ 7 := by
    rw [hA]
    field_simp [hh, h16, hh14, hh21]
    ring
  have hdiff :
      (512 : F) * h ^ 21 *
          betaResidual810
            (depressedL810 h (octicDepressionR810 h a7) b9)
            (depressedA810 h (octicDepressionR810 h a7) a7 a6)
            (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
            (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7) =
        (512 : F) * h ^ 21 *
            depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 -
          (640 : F) * h ^ 21 *
            depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 +
          (144 : F) * lambda * h ^ 21 *
            depressedA810 h (octicDepressionR810 h a7) a7 a6 := by
    simp only [betaResidual810, hL]
    field_simp [h4, h8]
    ring
  rw [hdiff, h512Q, h640B, h144A]
  ring

end Depression810Third

/-! ## Degree-`14` depressed Jacobian coefficient -/

section DepressedRow810Third

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`14` Jacobian coefficient is
exactly `10 B' + 9 L A' - 8 Q'`. -/
theorem differentialJacobian_coeff_14_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 14 =
      (10 : F) * d (f.coeff 5) + (9 : F) * g.coeff 9 * d (f.coeff 6) -
        (8 : F) * d (g.coeff 7) := by
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
  have hmem59 : ((5, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (14 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem68 : ((6, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (14 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem77 : ((7, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (14 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 14 =
        (10 : F) * d (f.coeff 5) +
          (9 : F) * g.coeff 9 * d (f.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne : ((5, 9) : ℕ × ℕ) ≠ (6, 8) := by decide
    have hsubset : ({(5, 9), (6, 8)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (14 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · subst b
        exact hmem59
      · subst b
        exact hmem68
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (14 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(5, 9), (6, 8)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 14 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne59 : b ≠ (5, 9) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne68 : b ≠ (6, 8) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 7 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne5 : b.1 ≠ 5 := by
          intro h5
          apply hne59
          ext
          · exact h5
          · omega
        have hne6 : b.1 ≠ 6 := by
          intro h6
          apply hne68
          ext
          · exact h6
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(5, 9), (6, 8)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 5 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 6 * g.derivative.coeff 8 := by
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
      (f.derivative * coefficientDeriv d g).coeff 14 =
        (8 : F) * d (g.coeff 7) := by
    have hprod :
        (f.derivative * coefficientDeriv d g).coeff 14 =
          f.derivative.coeff 7 * (coefficientDeriv d g).coeff 7 := by
      rw [Polynomial.coeff_mul]
      refine Finset.sum_eq_single_of_mem _ hmem77 ?_
      intro b hb hne
      have hij : b.1 + b.2 = 14 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hi : b.1 ≠ 7 := by
        intro h7
        apply hne
        ext
        · exact h7
        · omega
      by_cases hige : 8 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h6 : b.1 = 6
        · have hf6 : f.derivative.coeff b.1 = 0 := by
            rw [h6, Polynomial.coeff_derivative, hf7]
            simp
          simp [hf6]
        · have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hder : f.derivative.coeff 7 = (8 : F) := by
      rw [Polynomial.coeff_derivative, hf8]
      norm_num
    rw [hprod, coeff_coefficientDeriv, hder]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]

theorem betaResidual810_deriv_zero
    (d : Derivation k F F) (L A B Q : F)
    (hL : d L = 0)
    (hrow : (10 : F) * d B + (9 : F) * L * d A - (8 : F) * d Q = 0) :
    d (betaResidual810 L A B Q) = 0 := by
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  simp only [betaResidual810, map_sub, Derivation.leibniz, h54, h98, hL,
    zero_mul, add_zero, mul_zero]
  linear_combination (-1 / 8 : F) * hrow

end DepressedRow810Third

/-! ## Affine depression of a degree-ten source, `z⁷` coefficient -/

section AffineDecic810Third

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁷` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff7_810
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 7 =
      -120 * r ^ 3 + 36 * (p.coeff 9 / h ^ 9) * r ^ 2 -
        8 * (p.coeff 8 / h ^ 8) * r + p.coeff 7 / h ^ 7 := by
  let plow : (RatFunc k)[X] :=
    p - C (p.coeff 10) * X ^ 10 - C (p.coeff 9) * X ^ 9 -
      C (p.coeff 8) * X ^ 8 - C (p.coeff 7) * X ^ 7
  have hplow : ∀ n, 7 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h7 | hlt7
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
              show n ≠ 7 by omega]
  have hplowDeg : plow.natDegree ≤ 6 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = C (p.coeff 10) * X ^ 10 + C (p.coeff 9) * X ^ 9 +
        C (p.coeff 8) * X ^ 8 + C (p.coeff 7) * X ^ 7 + plow := by
    simp only [plow]
    ring
  have hq :
      affineDepress68 h r p =
        (C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹) +
          plow.comp ((X - C r) * C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((X - C r) * C h⁻¹) := rfl
    have hsum (A B D E G s : (RatFunc k)[X]) :
        (A + B + D + E + G).comp s =
          A.comp s + B.comp s + D.comp s + E.comp s + G.comp s := by
      have h1 : (A + B + D + E + G).comp s =
          (A + B + D + E).comp s + G.comp s := add_comp
      have h2 : (A + B + D + E).comp s =
          (A + B + D).comp s + E.comp s := add_comp
      have h3 : (A + B + D).comp s =
          (A + B).comp s + D.comp s := add_comp
      have h4 : (A + B).comp s = A.comp s + B.comp s := add_comp
      rw [h1, h2, h3, h4]
    exact hdef.trans ((congrArg (fun t => t.comp ((X - C r) * C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _))
  have hlow (n : ℕ) (hn : 7 ≤ n) :
      (plow.comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤
          plow.natDegree * ((X - C r) * C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((X - C r) * C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((X - C r) * C h⁻¹).natDegree ≤ 6 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤ 6 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 7 ≤ n))
  have h10_7 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 7 =
        -120 * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 7 hh]
    have hle : (7 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 7 = 120 := by decide
    simp only [hle, ite_true, hp10, hbin, pow_three]
    field_simp [hh]
    ring
  have h9_7 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 7 =
        36 * (p.coeff 9 / h ^ 9) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 7 hh]
    have hle : (7 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 7 = 36 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]
    ring
  have h8_7 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 7 =
        -8 * (p.coeff 8 / h ^ 8) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 7 hh]
    have hle : (7 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 7 = 8 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]
    ring
  have h7_7 :
      ((C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹)).coeff 7 =
        p.coeff 7 / h ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 7 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  rw [hq, coeff_add, coeff_add, coeff_add, coeff_add, h10_7, h9_7, h8_7,
    h7_7, hlow 7 (by omega)]
  ring

end AffineDecic810Third

/-! ## Linear divisibility at a simple root -/

section LinearDvd810

variable {k : Type*} [Field k]

/-- A degree-one polynomial divides every polynomial vanishing at its
unique root. -/
theorem linearPolynomial_dvd_of_eval_eq_zero_810
    (h f : k[X]) (a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0) (hf : f.eval a = 0) : h ∣ f := by
  have hlinearRoot : X - C a ∣ f := Polynomial.dvd_iff_isRoot.mpr hf
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by simpa [← hlinear] using hroot
  have hd : d = -(c * a) := by linear_combination hca
  have hfactor : h = C c * (X - C a) := by
    calc
      h = C c * X + C d := hlinear.symm
      _ = C c * X - C (c * a) := by rw [hd, map_neg]; ring
      _ = C c * (X - C a) := by rw [mul_sub, ← map_mul]
  have hscaleDvd : h ∣ X - C a := by
    refine ⟨C c⁻¹, ?_⟩
    rw [hfactor]
    calc
      X - C a = 1 * (X - C a) := by rw [one_mul]
      _ = (C c * C c⁻¹) * (X - C a) := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]
      _ = C c * (X - C a) * C c⁻¹ := by ring
  exact hscaleDvd.trans hlinearRoot

end LinearDvd810

/-! ## Source-facing third-face packet -/

section NonzeroThirdFace810

variable {k : Type*} [Field k] [CharZero k]

/-- The second octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h²¹`. -/
theorem nonzeroFace810_thirdDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ gamma : k,
      localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6) (p.coeff 5)
          (q.coeff 8) (q.coeff 7) lambda =
        Polynomial.C gamma * h0 ^ 21 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
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
  obtain ⟨hg10, hg9, _, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedQ810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7]
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
  have hrow :
      (differentialJacobian ratFuncDerivation68 f g).coeff 14 =
        (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 5) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 6) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) := by
    exact differentialJacobian_coeff_14_monicOcticDecic
      ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
  have hrow0 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 5) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 14) hbracket
    simpa [f, g, Polynomial.coeff_C, show (14 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf6 : f.coeff 6 = depressedA810 h (octicDepressionR810 h a7) a7 a6 := by
    dsimp only [f, depressedA810, a7, a6]
    rw [hpDep, coeff_depressedOctic68_six]
  have hf5 : f.coeff 5 =
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 := by
    dsimp only [f, depressedB810, a7, a6, a5]
    rw [hpDep, coeff_depressedOctic68_five]
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (g.coeff 7)) = 0 :=
    betaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (g.coeff 7) hLconst (by simpa using hrow0)
  obtain ⟨gamma, hgamma⟩ :
      ∃ a : k,
        betaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (g.coeff 7) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hbeta0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda) =
        (512 : RatFunc k) * h ^ 21 *
          betaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (g.coeff 7) := by
    have hF := thirdDefect_eq_clearedBeta810 h a7 a6 a5 b9 b8 b7
      (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL810 h (octicDepressionR810 h a7) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    simpa [localClearedThirdDefect810, map_sub, map_mul, map_pow,
      map_ofNat, RatFunc.algebraMap_C, h, a7, a6, a5, b8, b7,
      betaResidual810, hf6, hf5, hg7, hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (512 * gamma) * h0 ^ 21) := by
    rw [hclear, hgamma]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨512 * gamma, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the degree-one scale divides the
subleading octic coefficient to order four, the first unused decic
coefficient to order two, and `q₉` to order six. -/
theorem nonzeroFace810_linearRoot_thirdInitialPacket
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
    h0 ^ 4 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 9 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace810_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  have hp7root : (p.coeff 7).eval a = 0 :=
    nonzeroFace810_linearRoot_p7_zero p q H h0 j lambda a
      hp hq hh0 hH hp8 hq10 hN hD hroot
  have hp7div : h0 ∣ p.coeff 7 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 7) a
      hh0degree hroot hp7root
  obtain ⟨u, hu⟩ := hp7div
  have hM1 :
      (32 : k[X]) * q.coeff 8 * h0 ^ 4 -
          (40 : k[X]) * p.coeff 6 * h0 ^ 6 +
        (9 : k[X]) * Polynomial.C lambda * u * h0 ^ 6 -
          (5 : k[X]) * u ^ 2 =
        Polynomial.C alpha * h0 ^ 12 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 *
            ((32 : k[X]) * q.coeff 8 * h0 ^ 4 -
                (40 : k[X]) * p.coeff 6 * h0 ^ 6 +
              (9 : k[X]) * Polynomial.C lambda * u * h0 ^ 6 -
                (5 : k[X]) * u ^ 2) =
          localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect810, hu]
        ring
      _ = Polynomial.C alpha * h0 ^ 14 := hM
      _ = h0 ^ 2 * (Polynomial.C alpha * h0 ^ 12) := by ring
  have hu0 : u.eval a = 0 := by
    have heval := congrArg (fun t : k[X] => t.eval a) hM1
    have h5 : (5 : k) ≠ 0 := by norm_num
    have hzero : -((5 : k) * (u.eval a) ^ 2) = 0 := by
      simpa [hroot] using heval
    have hsq : (u.eval a) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linear_combination -hzero)).resolve_left h5
    exact sq_eq_zero_iff.mp hsq
  have hu_div : h0 ∣ u :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 u a hh0degree hroot hu0
  obtain ⟨v, hv⟩ := hu_div
  have hM2 :
      (32 : k[X]) * q.coeff 8 * h0 ^ 2 -
          (40 : k[X]) * p.coeff 6 * h0 ^ 4 +
        (9 : k[X]) * Polynomial.C lambda * v * h0 ^ 5 -
          (5 : k[X]) * v ^ 2 =
        Polynomial.C alpha * h0 ^ 10 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 *
            ((32 : k[X]) * q.coeff 8 * h0 ^ 2 -
                (40 : k[X]) * p.coeff 6 * h0 ^ 4 +
              (9 : k[X]) * Polynomial.C lambda * v * h0 ^ 5 -
                (5 : k[X]) * v ^ 2) =
          (32 : k[X]) * q.coeff 8 * h0 ^ 4 -
              (40 : k[X]) * p.coeff 6 * h0 ^ 6 +
            (9 : k[X]) * Polynomial.C lambda * u * h0 ^ 6 -
              (5 : k[X]) * u ^ 2 := by
        rw [hv]
        ring
      _ = Polynomial.C alpha * h0 ^ 12 := hM1
      _ = h0 ^ 2 * (Polynomial.C alpha * h0 ^ 10) := by ring
  have hv0 : v.eval a = 0 := by
    have heval := congrArg (fun t : k[X] => t.eval a) hM2
    have h5 : (5 : k) ≠ 0 := by norm_num
    have hzero : -((5 : k) * (v.eval a) ^ 2) = 0 := by
      simpa [hroot] using heval
    have hsq : (v.eval a) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linear_combination -hzero)).resolve_left h5
    exact sq_eq_zero_iff.mp hsq
  have hv_div : h0 ∣ v :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 v a hh0degree hroot hv0
  obtain ⟨w, hw⟩ := hv_div
  have hM3 :
      (32 : k[X]) * q.coeff 8 - (40 : k[X]) * p.coeff 6 * h0 ^ 2 +
          (9 : k[X]) * Polynomial.C lambda * w * h0 ^ 4 -
        (5 : k[X]) * w ^ 2 =
        Polynomial.C alpha * h0 ^ 8 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 *
            ((32 : k[X]) * q.coeff 8 - (40 : k[X]) * p.coeff 6 * h0 ^ 2 +
                (9 : k[X]) * Polynomial.C lambda * w * h0 ^ 4 -
              (5 : k[X]) * w ^ 2) =
          (32 : k[X]) * q.coeff 8 * h0 ^ 2 -
              (40 : k[X]) * p.coeff 6 * h0 ^ 4 +
            (9 : k[X]) * Polynomial.C lambda * v * h0 ^ 5 -
              (5 : k[X]) * v ^ 2 := by
        rw [hw]
        ring
      _ = Polynomial.C alpha * h0 ^ 10 := hM2
      _ = h0 ^ 2 * (Polynomial.C alpha * h0 ^ 8) := by ring
  have hMroot : (32 : k) * (q.coeff 8).eval a -
      (5 : k) * (w.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun t : k[X] => t.eval a) hM3
    simpa [hroot] using heval
  have hp7w : p.coeff 7 = h0 ^ 3 * w := by
    rw [hu, hv, hw]
    ring
  have hT3 :
      (100 : k[X]) * w ^ 3 - (512 : k[X]) * w * q.coeff 8 -
          (135 : k[X]) * Polynomial.C lambda * w ^ 2 * h0 ^ 4 +
        (480 : k[X]) * p.coeff 6 * w * h0 ^ 2 +
          (512 : k[X]) * q.coeff 7 * h0 ^ 5 +
        (144 : k[X]) * Polynomial.C lambda * p.coeff 6 * h0 ^ 6 -
          (640 : k[X]) * p.coeff 5 * h0 ^ 7 =
        Polynomial.C gamma * h0 ^ 12 := by
    apply mul_left_cancel₀ (pow_ne_zero 9 hh0)
    calc
      h0 ^ 9 *
            ((100 : k[X]) * w ^ 3 - (512 : k[X]) * w * q.coeff 8 -
                (135 : k[X]) * Polynomial.C lambda * w ^ 2 * h0 ^ 4 +
              (480 : k[X]) * p.coeff 6 * w * h0 ^ 2 +
                (512 : k[X]) * q.coeff 7 * h0 ^ 5 +
              (144 : k[X]) * Polynomial.C lambda * p.coeff 6 * h0 ^ 6 -
                (640 : k[X]) * p.coeff 5 * h0 ^ 7) =
          localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect810, hp7w]
        ring
      _ = Polynomial.C gamma * h0 ^ 21 := hT
      _ = h0 ^ 9 * (Polynomial.C gamma * h0 ^ 12) := by ring
  have hTroot : (100 : k) * (w.eval a) ^ 3 -
      (512 : k) * w.eval a * (q.coeff 8).eval a = 0 := by
    have heval := congrArg (fun t : k[X] => t.eval a) hT3
    simpa [hroot] using heval
  have hw0 : w.eval a = 0 := by
    have h20 : (20 : k) ≠ 0 := by norm_num
    have h512b :
        (512 : k) * (q.coeff 8).eval a =
          (80 : k) * (w.eval a) ^ 2 := by
      have hscale : (512 : k) = (16 : k) * (32 : k) := by norm_num
      have h80 : (80 : k) = (16 : k) * (5 : k) := by norm_num
      rw [hscale, mul_assoc, h80]
      linear_combination (16 : k) * hMroot
    have hcomb :
        (100 : k) * (w.eval a) ^ 3 -
            (512 : k) * w.eval a * (q.coeff 8).eval a =
          (20 : k) * (w.eval a) ^ 3 := by
      have : (512 : k) * w.eval a * (q.coeff 8).eval a =
          w.eval a * ((512 : k) * (q.coeff 8).eval a) := by ring
      rw [this, h512b]
      ring
    have hw3 : (w.eval a) ^ 3 = 0 := by
      have h := hcomb.symm.trans hTroot
      apply (mul_eq_zero.mp ?_).resolve_left h20
      linear_combination h
    have hprod : w.eval a * (w.eval a * w.eval a) = 0 := by
      convert hw3 using 1
      ring
    rcases mul_eq_zero.mp hprod with hw | hsq
    · exact hw
    · exact (mul_eq_zero.mp hsq).elim id id
  have hb8root : (q.coeff 8).eval a = 0 := by
    have h32 : (32 : k) ≠ 0 := by norm_num
    have hwsq : (w.eval a) ^ 2 = 0 := by simp [hw0]
    have : (32 : k) * (q.coeff 8).eval a = 0 := by
      linear_combination hMroot + (5 : k) * hwsq
    exact (mul_eq_zero.mp this).resolve_left h32
  have hw_div : h0 ∣ w :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 w a hh0degree hroot hw0
  have hb8div : h0 ∣ q.coeff 8 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 8) a
      hh0degree hroot hb8root
  obtain ⟨t, ht⟩ := hw_div
  obtain ⟨s, hs⟩ := hb8div
  have hp7t : p.coeff 7 = h0 ^ 4 * t := by
    rw [hp7w, ht]
    ring
  have hM4 :
      (32 : k[X]) * s - (40 : k[X]) * p.coeff 6 * h0 +
          (9 : k[X]) * Polynomial.C lambda * t * h0 ^ 4 -
        (5 : k[X]) * t ^ 2 * h0 =
        Polynomial.C alpha * h0 ^ 7 := by
    apply mul_left_cancel₀ hh0
    calc
      h0 *
            ((32 : k[X]) * s - (40 : k[X]) * p.coeff 6 * h0 +
                (9 : k[X]) * Polynomial.C lambda * t * h0 ^ 4 -
              (5 : k[X]) * t ^ 2 * h0) =
          (32 : k[X]) * q.coeff 8 - (40 : k[X]) * p.coeff 6 * h0 ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * w * h0 ^ 4 -
            (5 : k[X]) * w ^ 2 := by
        rw [hs, ht]
        ring
      _ = Polynomial.C alpha * h0 ^ 8 := hM3
      _ = h0 * (Polynomial.C alpha * h0 ^ 7) := by ring
  have hs0 : s.eval a = 0 := by
    have heval := congrArg (fun t : k[X] => t.eval a) hM4
    have h32 : (32 : k) ≠ 0 := by norm_num
    have h32s : (32 : k) * s.eval a = 0 := by
      simpa [hroot] using heval
    exact (mul_eq_zero.mp h32s).resolve_left h32
  have hs_div : h0 ∣ s :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 s a hh0degree hroot hs0
  have hp7pow : h0 ^ 4 ∣ p.coeff 7 := ⟨t, by rw [hp7t]⟩
  have hq8pow : h0 ^ 2 ∣ q.coeff 8 := by
    obtain ⟨u8, hu8⟩ := hs_div
    refine ⟨u8, ?_⟩
    rw [hs, hu8]
    ring
  have hq9pow : h0 ^ 6 ∣ q.coeff 9 := by
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
          h0 ^ 6 * ((5 : k[X]) * t - Polynomial.C lambda * h0 ^ 3) := by
      rw [hN', hp7t]
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
        ((5 : k[X]) * t - Polynomial.C lambda * h0 ^ 3), ?_⟩
    rw [hq9eq, hform]
    ring
  exact ⟨hp7pow, hq8pow, hq9pow⟩

/-- Source-facing third integral for a normalized scale-two `(8,10)`
nonzero face. -/
theorem normalized810ScaleTwo_nonzeroFace_thirdDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda gamma : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda =
          Polynomial.C gamma * h0 ^ 21 := by
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
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8' hq10' hN' hD
  exact ⟨h0, lambda, gamma, hh0, hlambda, hh0degree, hH, hN', hT⟩

/-- Finite local initial packet of a normalized scale-two `(8,10)`
nonzero face: the degree-one scale divides `p₇` to order four, `q₈` to
order two, and `q₉` to order six. -/
theorem normalized810ScaleTwo_nonzeroFace_thirdInitialPacket
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
        h0 ^ 4 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 9 ∧
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
  obtain ⟨hp7, hq8, hq9⟩ :=
    nonzeroFace810_linearRoot_thirdInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp7, hq8, hq9,
    hN'⟩

end NonzeroThirdFace810

#print axioms thirdCoefficientJacobianRow_810
#print axioms differentialJacobian_coeff_14_monicOcticDecic
#print axioms thirdDefect_eq_clearedBeta810
#print axioms nonzeroFace810_thirdDefectPowerRelation
#print axioms nonzeroFace810_linearRoot_thirdInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_thirdDefectPowerRelation
#print axioms normalized810ScaleTwo_nonzeroFace_thirdInitialPacket

end Max11DegreeRoutes
