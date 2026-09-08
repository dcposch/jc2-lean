import LowScale610ScaleTwoSourceFace
import LowScale810ScaleTwoSecondFace

/-! # Scale-two second face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the next Keller coefficient is the degree-`13` Jacobian
row.  After the sextic affine depression that kills `z⁵`, that row is the
weighted derivative `10 A' - 6 P' = 0` of the first new sextic/decic pair.
The resulting first integral clears to a polynomial defect `M` of weight
ten, and evaluating at the root of `h` forces `p₅(a) = 0`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened: the same row is available, but the polynomial square root
of `H` is not.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The second row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  It is the source of the first sextic/decic defect after
the nonic discriminator. -/
theorem secondCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 5).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 4).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 8).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 9).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 10).derivative) = 0 := by
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
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  rw [hC8, hC9, hC10, hC6, hC5, hC4]
  linear_combination hcoeff

/-! ## Sextic/decic depression and the cleared defect -/

section Depression610

variable {F : Type*} [Field F] [CharZero F]

/-- Sextic linear depression that kills the `z⁵` coefficient of a monic
degree-six source with leading coefficient `h⁶`. -/
abbrev sexticDepressionR610 (h a5 : F) : F :=
  sexticDepressionR68 h a5

/-- Depressed sextic `z⁴` coefficient.  This is the first new sextic
coordinate after the source discriminator. -/
abbrev depressedA610 (h r a5 a4 : F) : F :=
  depressedA68 h r a5 a4

/-- Depressed decic `z⁹` coefficient. -/
abbrev depressedL610 (h r b9 : F) : F :=
  depressedL810 h r b9

/-- Depressed decic `z⁸` coefficient. -/
abbrev depressedP610 (h r b9 b8 : F) : F :=
  depressedP810 h r b9 b8

/-- Polynomial numerator of `12 h¹⁰ A`. -/
def localClearedA610 (h a5 a4 : F[X]) : F[X] :=
  (12 : F[X]) * a4 * h ^ 6 - (5 : F[X]) * a5 ^ 2

/-- Polynomial numerator of `18 h¹⁰ (P - (5/3) A)` on the ninth-power
face.  This is the sharpest cleared next defect. -/
def localClearedSecondDefect610 (h a5 a4 b8 : F[X]) (lambda : F) : F[X] :=
  (18 : F[X]) * b8 * h ^ 2 - (30 : F[X]) * a4 * h ^ 6 +
    (9 : F[X]) * Polynomial.C lambda * a5 * h ^ 5 - (10 : F[X]) * a5 ^ 2

/-- Exact denominator clearing for the first sextic coordinate. -/
theorem natDegree_depressedSextic68_le_six
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).natDegree ≤ 6 := by
  have add6 {p q : F[X]} (hp : p.natDegree ≤ 6) (hq : q.natDegree ≤ 6) :
      (p + q).natDegree ≤ 6 :=
    (natDegree_add_le p q).trans (max_le hp hq)
  have term (c : F) (k : ℕ) (hk : k ≤ 6) :
      (C c * X ^ k : F[X]).natDegree ≤ 6 :=
    (natDegree_C_mul_X_pow_le c k).trans hk
  simp only [depressedSextic68]
  have h0 : (X ^ 6 : F[X]).natDegree ≤ 6 := natDegree_X_pow_le (R := F) 6
  have h1 : (X ^ 6 + C A * X ^ 4).natDegree ≤ 6 :=
    add6 h0 (term A 4 (by omega))
  have h2 : (X ^ 6 + C A * X ^ 4 + C B * X ^ 3).natDegree ≤ 6 :=
    add6 h1 (term B 3 (by omega))
  have h3 : (X ^ 6 + C A * X ^ 4 + C B * X ^ 3 +
      C C0 * X ^ 2).natDegree ≤ 6 :=
    add6 h2 (term C0 2 (by omega))
  have h4 : (X ^ 6 + C A * X ^ 4 + C B * X ^ 3 + C C0 * X ^ 2 +
      C D * X).natDegree ≤ 6 :=
    add6 h3 ((natDegree_C_mul_le D X).trans
      ((natDegree_X_le).trans (by omega)))
  exact add6 h4 ((natDegree_C E).trans_le (by omega))

theorem coeff_depressedSextic68_of_gt_six
    (A B C0 D E : F) {n : ℕ} (hn : 6 < n) :
    (depressedSextic68 A B C0 D E).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (natDegree_depressedSextic68_le_six A B C0 D E) hn)

theorem coeff_depressedSextic68_six
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 6 = 1 := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem coeff_depressedSextic68_five
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 5 = 0 := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem coeff_depressedSextic68_four
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 4 = A := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the first sextic coordinate. -/
theorem depressedA610_eq_cleared
    (h a5 a4 : F) (hh : h ≠ 0) :
    depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
      (12 * a4 * h ^ 6 - 5 * a5 ^ 2) / (12 * h ^ 10) := by
  simp only [depressedA610, depressedA68, sexticDepressionR610,
    sexticDepressionR68]
  field_simp [hh]
  ring

/-- On the nonzero first face the depressed decic `z⁹` coefficient is the
ground constant `-λ/3`. -/
theorem depressedL610_eq_of_ninthPower
    (h a5 b9 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    depressedL610 h (sexticDepressionR610 h a5) b9 = -lambda / 3 := by
  have hh5 : 6 * h ^ 5 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 5 hh)
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  simp only [depressedL610, depressedL810, sexticDepressionR610,
    sexticDepressionR68]
  have hrewrite :
      -10 * (a5 / (6 * h ^ 5)) + b9 / h ^ 9 =
        (-10 * a5 * h ^ 4 + 6 * b9) / (6 * h ^ 9) := by
    field_simp [hh, hh5, hh9]
  rw [hrewrite]
  have hnum : -10 * a5 * h ^ 4 + 6 * b9 = -2 * (5 * a5 * h ^ 4 - 3 * b9) := by
    ring
  rw [hnum, hN]
  field_simp [hh, hh9]
  ring

/-- Clearing the first integral `P - (5/3) A` against `h¹⁰` on the ninth-power
face. -/
theorem secondDefect_eq_clearedAlpha610
    (h a5 a4 b9 b8 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (18 : F) * h ^ 10 *
        (depressedP610 h (sexticDepressionR610 h a5) b9 b8 -
          (5 / 3 : F) *
            depressedA610 h (sexticDepressionR610 h a5) a5 a4) =
      (18 : F) * b8 * h ^ 2 - (30 : F) * a4 * h ^ 6 +
        (9 : F) * lambda * a5 * h ^ 5 - (10 : F) * a5 ^ 2 := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h12 : (12 : F) ≠ 0 := by norm_num
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh8 : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  have hA :
      depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (12 * a4 * h ^ 6 - 5 * a5 ^ 2) / (12 * h ^ 10) :=
    depressedA610_eq_cleared h a5 a4 hh
  have h30A :
      (30 : F) * h ^ 10 *
          depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (30 : F) * a4 * h ^ 6 - (25 / 2 : F) * a5 ^ 2 := by
    rw [hA]
    field_simp [hh, h12, hh10]
    ring
  have h18P :
      (18 : F) * h ^ 10 *
          depressedP610 h (sexticDepressionR610 h a5) b9 b8 =
        (45 / 2 : F) * a5 ^ 2 - (27 : F) * a5 * b9 / h ^ 4 +
          (18 : F) * b8 * h ^ 2 := by
    simp only [depressedP610, depressedP810, sexticDepressionR610,
      sexticDepressionR68]
    field_simp [hh, h6, hh4, hh5, hh8, hh9, hh10]
    ring
  have hdiff :
      (18 : F) * h ^ 10 *
          (depressedP610 h (sexticDepressionR610 h a5) b9 b8 -
            (5 / 3 : F) *
              depressedA610 h (sexticDepressionR610 h a5) a5 a4) =
        (18 : F) * h ^ 10 *
            depressedP610 h (sexticDepressionR610 h a5) b9 b8 -
          (30 : F) * h ^ 10 *
            depressedA610 h (sexticDepressionR610 h a5) a5 a4 := by
    ring
  have hfrac :
      (27 : F) * a5 * b9 / h ^ 4 =
        (45 : F) * a5 ^ 2 - (9 : F) * lambda * a5 * h ^ 5 := by
    have hscale : (27 : F) * a5 * b9 / h ^ 4 =
        (9 : F) * a5 * (3 * b9) / h ^ 4 := by
      ring
    rw [hscale, hb9]
    field_simp [hh, hh4]
    ring
  rw [hdiff, h18P, h30A, hfrac]
  ring

end Depression610

/-! ## Degree-`13` depressed Jacobian coefficient -/

section DepressedRow610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`13` Jacobian coefficient is
exactly `10 A' - 6 P'`. -/
theorem differentialJacobian_coeff_13_monicSexticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 13 =
      (10 : F) * d (f.coeff 4) - (6 : F) * d (g.coeff 8) := by
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
  have hmem49 : ((4, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (13 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem58 : ((5, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (13 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 13 =
        (10 : F) * d (f.coeff 4) := by
    have hprod :
        (coefficientDeriv d f * g.derivative).coeff 13 =
          (coefficientDeriv d f).coeff 4 * g.derivative.coeff 9 := by
      rw [Polynomial.coeff_mul]
      refine Finset.sum_eq_single_of_mem _ hmem49 ?_
      intro b hb hne
      have hij : b.1 + b.2 = 13 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hi : b.1 ≠ 4 := by
        intro h4eq
        apply hne
        ext
        · exact h4eq
        · omega
      by_cases hige : 5 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hder : g.derivative.coeff 9 = (10 : F) := by
      rw [Polynomial.coeff_derivative, hg10]
      norm_num
    rw [hprod, coeff_coefficientDeriv, hder, mul_comm]
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 13 =
        (6 : F) * d (g.coeff 8) := by
    have hprod :
        (f.derivative * coefficientDeriv d g).coeff 13 =
          f.derivative.coeff 5 * (coefficientDeriv d g).coeff 8 := by
      rw [Polynomial.coeff_mul]
      refine Finset.sum_eq_single_of_mem _ hmem58 ?_
      intro b hb hne
      have hij : b.1 + b.2 = 13 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hi : b.1 ≠ 5 := by
        intro h5eq
        apply hne
        ext
        · exact h5eq
        · omega
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · have hj : 9 ≤ b.2 := by omega
        simp [hgd'_high b.2 hj]
    have hder : f.derivative.coeff 5 = (6 : F) := by
      rw [Polynomial.coeff_derivative, hf6]
      norm_num
    rw [hprod, coeff_coefficientDeriv, hder]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]

/-- The first residual `P - (5/3) A` of the degree-`13` row. -/
def alphaResidual610 (A P : F) : F := P - (5 / 3 : F) * A

theorem alphaResidual610_deriv_zero
    (d : Derivation k F F) (A P : F)
    (hrow : (10 : F) * d A - (6 : F) * d P = 0) :
    d (alphaResidual610 A P) = 0 := by
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h53 : d (5 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h5]
  simp only [alphaResidual610, map_sub, Derivation.leibniz, h53, zero_mul,
    add_zero]
  linear_combination (-1 / 6 : F) * hrow

end DepressedRow610

/-! ## Source-facing second-face packet -/

section NonzeroSecondFace610

variable {k : Type*} [Field k] [CharZero k]

/-- The first sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h¹⁰`. -/
theorem nonzeroFace610_secondDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ alpha : k,
      localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4) (q.coeff 8)
          lambda =
        Polynomial.C alpha * h0 ^ 10 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
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
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
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
      (differentialJacobian ratFuncDerivation68 f g).coeff 13 =
        (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) := by
    exact differentialJacobian_coeff_13_monicSexticDecic
      ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
  have hrow0 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf4 : f.coeff 4 = depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
    dsimp only [f, depressedA610, a5, a4]
    rw [hpDep, coeff_depressedSextic68_four]
  have hg8' : g.coeff 8 =
      depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP610, depressedP810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have halpha0 :
      ratFuncDerivation68
        (alphaResidual610 (f.coeff 4) (g.coeff 8)) = 0 :=
    alphaResidual610_deriv_zero ratFuncDerivation68 (f.coeff 4) (g.coeff 8)
      hrow0
  obtain ⟨alpha, halpha⟩ :
      ∃ a : k,
        alphaResidual610 (f.coeff 4) (g.coeff 8) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using halpha0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4)
            (q.coeff 8) lambda) =
        (18 : RatFunc k) * hRF ^ 10 *
          alphaResidual610 (f.coeff 4) (g.coeff 8) := by
    have hF := secondDefect_eq_clearedAlpha610 hRF a5 a4 b9 b8
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [localClearedSecondDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, RatFunc.algebraMap_C, hRF, a5, a4, b8, alphaResidual610,
      hf4, hg8'] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4)
            (q.coeff 8) lambda) =
        algebraMap k[X] (RatFunc k) (Polynomial.C (18 * alpha) * h0 ^ 10) := by
    rw [hclear, halpha]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨18 * alpha, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: at a root of the degree-one scale, the
subleading sextic coefficient vanishes. -/
theorem nonzeroFace610_linearRoot_p5_zero
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    (p.coeff 5).eval a = 0 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace610_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have heval := congrArg (fun t : k[X] => t.eval a) hM
  have h10 : (10 : k) ≠ 0 := by norm_num
  have hM0 : (localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4)
      (q.coeff 8) lambda).eval a = 0 := by
    rw [heval]
    simp [hroot]
  have hform :
      (localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4)
          (q.coeff 8) lambda).eval a =
        -((10 : k) * ((p.coeff 5).eval a) ^ 2) := by
    simp [localClearedSecondDefect610, hroot]
  have hsq : ((p.coeff 5).eval a) ^ 2 = 0 := by
    have h := hform.symm.trans hM0
    apply (mul_eq_zero.mp ?_).resolve_left h10
    linear_combination -h
  exact sq_eq_zero_iff.mp hsq

/-- Combined with the ninth-power first face, the same root kills `q₉`. -/
theorem nonzeroFace610_linearRoot_q9_zero
    (p q : k[X][X]) (H h0 : k[X]) (lambda a : k)
    (hH : H = h0 ^ 2)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hroot : h0.eval a = 0) :
    (q.coeff 9).eval a = 0 := by
  have h3 : (3 : k) ≠ 0 := by norm_num
  have hNeval := congrArg (fun t : k[X] => t.eval a) hN
  have hform :
      ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9).eval a =
        -((3 : k) * (q.coeff 9).eval a) := by
    simp [hH, hroot]
  have hrhs : (Polynomial.C lambda * h0 ^ 9).eval a = 0 := by
    simp [hroot]
  have h := hform.symm.trans (hNeval.trans hrhs)
  apply (mul_eq_zero.mp ?_).resolve_left h3
  linear_combination -h

/-- Source-facing second integral for a normalized scale-two `(6,10)`
nonzero face. -/
theorem normalized610ScaleTwo_nonzeroFace_secondDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda alpha : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4)
            (q.coeff 8) lambda =
          Polynomial.C alpha * h0 ^ 10 := by
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
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace610_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6' hq10' hN' hD
  exact ⟨h0, lambda, alpha, hh0, hlambda, hh0degree, hH, hN', hM⟩

/-- Finite local initial packet of a normalized scale-two `(6,10)`
nonzero face: the degree-one scale divides the subleading sextic
coefficient, and the first-face relation then kills `q₉` at the same
root. -/
theorem normalized610ScaleTwo_nonzeroFace_p5_vanishes_at_root
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
        h0.eval a = 0 ∧ (p.coeff 5).eval a = 0 ∧ (q.coeff 9).eval a = 0 ∧
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
  have hp5 : (p.coeff 5).eval a = 0 :=
    nonzeroFace610_linearRoot_p5_zero p q H h0 j lambda a
      hp hq hh0 hH hp6' hq10' hN' hD hroot
  have hq9 : (q.coeff 9).eval a = 0 :=
    nonzeroFace610_linearRoot_q9_zero p q H h0 lambda a hH hN' hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp5, hq9, hN'⟩

end NonzeroSecondFace610

#print axioms secondCoefficientJacobianRow_610
#print axioms depressedL610_eq_of_ninthPower
#print axioms differentialJacobian_coeff_13_monicSexticDecic
#print axioms nonzeroFace610_secondDefectPowerRelation
#print axioms nonzeroFace610_linearRoot_p5_zero
#print axioms nonzeroFace610_linearRoot_q9_zero
#print axioms normalized610ScaleTwo_nonzeroFace_secondDefectPowerRelation
#print axioms normalized610ScaleTwo_nonzeroFace_p5_vanishes_at_root

end Max11DegreeRoutes
