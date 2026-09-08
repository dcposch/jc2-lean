import LowScale810ScaleTwoSourceFace

/-! # Scale-two second face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the next Keller coefficient is the degree-`15` Jacobian
row.  After the octic affine depression that kills `z⁷`, that row is the
weighted derivative `10 A' - 8 P' = 0` of the first new octic/decic pair.
The resulting first integral clears to a polynomial defect `M` of weight
fourteen, and evaluating at the root of `h` forces `p₇(a) = 0`.

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
degrees `(8,10)`.  It is the source of the first octic/decic defect after
the nonic discriminator. -/
theorem secondCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 7).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 6).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 8).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 9).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 15) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (15 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 15 :
      Finset (ℕ × ℕ)) =
      ({(0, 15), (1, 14), (2, 13), (3, 12), (4, 11), (5, 10), (6, 9),
        (7, 8), (8, 7), (9, 6), (10, 5), (11, 4), (12, 3), (13, 2),
        (14, 1), (15, 0)} : Finset (ℕ × ℕ)) := by decide
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
  rw [hC8, hC9, hC10, hC7, hC6]
  linear_combination hcoeff

/-! ## Octic/decic depression and the cleared defect -/

section Depression810

variable {F : Type*} [Field F] [CharZero F]

/-- Octic linear depression that kills the `z⁷` coefficient of a monic
degree-eight source with leading coefficient `h⁸`. -/
def octicDepressionR810 (h a7 : F) : F := a7 / (8 * h ^ 7)

/-- Depressed octic `z⁶` coefficient.  This is the first new octic
coordinate after the source discriminator. -/
def depressedA810 (h r a7 a6 : F) : F :=
  depressedP68 h r a7 a6

/-- Depressed decic `z⁹` coefficient. -/
def depressedL810 (h r b9 : F) : F := -10 * r + b9 / h ^ 9

/-- Depressed decic `z⁸` coefficient. -/
def depressedP810 (h r b9 b8 : F) : F :=
  45 * r ^ 2 - 9 * (b9 / h ^ 9) * r + b8 / h ^ 8

/-- Polynomial numerator of `16 h¹⁴ A`. -/
def localClearedA810 (h a7 a6 : F[X]) : F[X] :=
  (16 : F[X]) * a6 * h ^ 8 - (7 : F[X]) * a7 ^ 2

/-- Polynomial numerator of `32 h¹⁴ (P - (5/4) A)` on the ninth-power
face.  This is the sharpest cleared next defect. -/
def localClearedSecondDefect810 (h a7 a6 b8 : F[X]) (lambda : F) : F[X] :=
  (32 : F[X]) * b8 * h ^ 6 - (40 : F[X]) * a6 * h ^ 8 +
    (9 : F[X]) * Polynomial.C lambda * a7 * h ^ 7 - (5 : F[X]) * a7 ^ 2

/-- The selected center kills the octic `z⁷` coefficient. -/
theorem depressedL68_eq_zero_of_octicCenter
    (h a7 : F) (hh : h ≠ 0) :
    depressedL68 h (octicDepressionR810 h a7) a7 = 0 := by
  simp only [depressedL68, octicDepressionR810]
  field_simp [hh]
  ring

/-- On the nonzero first face the depressed decic `z⁹` coefficient is the
ground constant `-λ/4`. -/
theorem depressedL810_eq_of_ninthPower
    (h a7 b9 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    depressedL810 h (octicDepressionR810 h a7) b9 = -lambda / 4 := by
  have hh7 : 8 * h ^ 7 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 7 hh)
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  simp only [depressedL810, octicDepressionR810]
  have hrewrite :
      -10 * (a7 / (8 * h ^ 7)) + b9 / h ^ 9 =
        (-10 * a7 * h ^ 2 + 8 * b9) / (8 * h ^ 9) := by
    field_simp [hh, hh7, hh9]
  rw [hrewrite]
  have hnum : -10 * a7 * h ^ 2 + 8 * b9 = -2 * (5 * a7 * h ^ 2 - 4 * b9) := by
    ring
  rw [hnum, hN]
  field_simp [hh, hh9]
  ring

/-- Exact denominator clearing for the first octic coordinate. -/
theorem natDegree_depressedOctic68_le_eight
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).natDegree ≤ 8 := by
  have add8 {p q : F[X]} (hp : p.natDegree ≤ 8) (hq : q.natDegree ≤ 8) :
      (p + q).natDegree ≤ 8 :=
    (natDegree_add_le p q).trans (max_le hp hq)
  have term (c : F) (k : ℕ) (hk : k ≤ 8) :
      (C c * X ^ k : F[X]).natDegree ≤ 8 :=
    (natDegree_C_mul_X_pow_le c k).trans hk
  simp only [depressedOctic68]
  have h0 : (X ^ 8 : F[X]).natDegree ≤ 8 := natDegree_X_pow_le (R := F) 8
  have h1 : (X ^ 8 + C L * X ^ 7).natDegree ≤ 8 :=
    add8 h0 (term L 7 (by omega))
  have h2 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6).natDegree ≤ 8 :=
    add8 h1 (term P 6 (by omega))
  have h3 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5).natDegree ≤ 8 :=
    add8 h2 (term Q 5 (by omega))
  have h4 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5 +
      C R * X ^ 4).natDegree ≤ 8 :=
    add8 h3 (term R 4 (by omega))
  have h5 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5 +
      C R * X ^ 4 + C S * X ^ 3).natDegree ≤ 8 :=
    add8 h4 (term S 3 (by omega))
  have h6 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5 +
      C R * X ^ 4 + C S * X ^ 3 + C T * X ^ 2).natDegree ≤ 8 :=
    add8 h5 (term T 2 (by omega))
  have h7 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5 +
      C R * X ^ 4 + C S * X ^ 3 + C T * X ^ 2 + C U * X).natDegree ≤ 8 :=
    add8 h6 ((natDegree_C_mul_le U X).trans
      ((natDegree_X_le).trans (by omega)))
  exact add8 h7 ((natDegree_C V).trans_le (by omega))

theorem coeff_depressedOctic68_of_gt_eight
    (L P Q R S T U V : F) {n : ℕ} (hn : 8 < n) :
    (depressedOctic68 L P Q R S T U V).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (natDegree_depressedOctic68_le_eight L P Q R S T U V) hn)

theorem coeff_depressedOctic68_eight
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 8 = 1 := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem coeff_depressedOctic68_seven
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 7 = L := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem coeff_depressedOctic68_six
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 6 = P := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the first octic coordinate. -/
theorem depressedA810_eq_cleared
    (h a7 a6 : F) (hh : h ≠ 0) :
    depressedA810 h (octicDepressionR810 h a7) a7 a6 =
      (16 * a6 * h ^ 8 - 7 * a7 ^ 2) / (16 * h ^ 14) := by
  simp only [depressedA810, depressedP68, octicDepressionR810]
  field_simp [hh]
  ring

/-- Clearing the first integral `P - (5/4) A` against `h¹⁴` on the ninth-power
face. -/
theorem secondDefect_eq_clearedAlpha810
    (h a7 a6 b9 b8 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (32 : F) * h ^ 14 *
        (depressedP810 h (octicDepressionR810 h a7) b9 b8 -
          (5 / 4 : F) *
            depressedA810 h (octicDepressionR810 h a7) a7 a6) =
      (32 : F) * b8 * h ^ 6 - (40 : F) * a6 * h ^ 8 +
        (9 : F) * lambda * a7 * h ^ 7 - (5 : F) * a7 ^ 2 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hb9 : 4 * b9 = 5 * a7 * h ^ 2 - lambda * h ^ 9 := by
    linear_combination -hN
  have hA :
      depressedA810 h (octicDepressionR810 h a7) a7 a6 =
        (16 * a6 * h ^ 8 - 7 * a7 ^ 2) / (16 * h ^ 14) :=
    depressedA810_eq_cleared h a7 a6 hh
  have h40A :
      (40 : F) * h ^ 14 *
          depressedA810 h (octicDepressionR810 h a7) a7 a6 =
        (40 : F) * a6 * h ^ 8 - (35 / 2 : F) * a7 ^ 2 := by
    rw [hA]
    field_simp [hh, h16, hh14]
    ring
  have h32P :
      (32 : F) * h ^ 14 *
          depressedP810 h (octicDepressionR810 h a7) b9 b8 =
        (45 / 2 : F) * a7 ^ 2 - (36 : F) * a7 * b9 / h ^ 2 +
          (32 : F) * b8 * h ^ 6 := by
    simp only [depressedP810, octicDepressionR810]
    field_simp [hh, h8, hh2, hh7, hh8pow, hh9, hh14]
    ring
  have hdiff :
      (32 : F) * h ^ 14 *
          (depressedP810 h (octicDepressionR810 h a7) b9 b8 -
            (5 / 4 : F) *
              depressedA810 h (octicDepressionR810 h a7) a7 a6) =
        (32 : F) * h ^ 14 *
            depressedP810 h (octicDepressionR810 h a7) b9 b8 -
          (40 : F) * h ^ 14 *
            depressedA810 h (octicDepressionR810 h a7) a7 a6 := by
    ring
  have hfrac :
      (36 : F) * a7 * b9 / h ^ 2 =
        (45 : F) * a7 ^ 2 - (9 : F) * lambda * a7 * h ^ 7 := by
    have hscale : (36 : F) * a7 * b9 / h ^ 2 =
        (9 : F) * a7 * (4 * b9) / h ^ 2 := by
      ring
    rw [hscale, hb9]
    field_simp [hh, hh2]
    ring
  rw [hdiff, h32P, h40A, hfrac]
  ring

end Depression810

/-! ## Degree-`15` depressed Jacobian coefficient -/

section DepressedRow810

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`15` Jacobian coefficient is
exactly `10 A' - 8 P'`. -/
theorem differentialJacobian_coeff_15_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 15 =
      (10 : F) * d (f.coeff 6) - (8 : F) * d (g.coeff 8) := by
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
  have hmem69 : ((6, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (15 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem78 : ((7, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (15 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 15 =
        (10 : F) * d (f.coeff 6) := by
    have hprod :
        (coefficientDeriv d f * g.derivative).coeff 15 =
          (coefficientDeriv d f).coeff 6 * g.derivative.coeff 9 := by
      rw [Polynomial.coeff_mul]
      refine Finset.sum_eq_single_of_mem _ hmem69 ?_
      intro b hb hne
      have hij : b.1 + b.2 = 15 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hi : b.1 ≠ 6 := by
        intro h6
        apply hne
        ext
        · exact h6
        · omega
      by_cases hige : 7 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hder : g.derivative.coeff 9 = (10 : F) := by
      rw [Polynomial.coeff_derivative, hg10]
      norm_num
    rw [hprod, coeff_coefficientDeriv, hder, mul_comm]
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 15 =
        (8 : F) * d (g.coeff 8) := by
    have hprod :
        (f.derivative * coefficientDeriv d g).coeff 15 =
          f.derivative.coeff 7 * (coefficientDeriv d g).coeff 8 := by
      rw [Polynomial.coeff_mul]
      refine Finset.sum_eq_single_of_mem _ hmem78 ?_
      intro b hb hne
      have hij : b.1 + b.2 = 15 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hi : b.1 ≠ 7 := by
        intro h7
        apply hne
        ext
        · exact h7
        · omega
      by_cases hige : 8 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · have hj : 9 ≤ b.2 := by omega
        simp [hgd'_high b.2 hj]
    have hder : f.derivative.coeff 7 = (8 : F) := by
      rw [Polynomial.coeff_derivative, hf8]
      norm_num
    rw [hprod, coeff_coefficientDeriv, hder]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]

/-- The first residual `P - (5/4) A` of the degree-`15` row. -/
def alphaResidual810 (A P : F) : F := P - (5 / 4 : F) * A

theorem alphaResidual810_deriv_zero
    (d : Derivation k F F) (A P : F)
    (hrow : (10 : F) * d A - (8 : F) * d P = 0) :
    d (alphaResidual810 A P) = 0 := by
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  simp only [alphaResidual810, map_sub, Derivation.leibniz, h54, zero_mul,
    add_zero]
  linear_combination (-1 / 8 : F) * hrow

end DepressedRow810

/-! ## Affine depression of a degree-ten source -/

section AffineDecic810

variable {k : Type*} [Field k] [CharZero k]

/-- The affine scale `(X - r)/h` has degree one. -/
theorem natDegree_affineScale810 (h r : RatFunc k) (hh : h ≠ 0) :
    (((X - C r) * C h⁻¹ : (RatFunc k)[X]).natDegree) = 1 := by
  have hinv : h⁻¹ ≠ 0 := inv_ne_zero hh
  rw [mul_comm, natDegree_C_mul hinv, natDegree_X_sub_C]

/-- Coefficient of a scaled monomial after the affine substitution. -/
theorem coeff_comp_C_mul_X_pow_affineScale810
    (c h r : RatFunc k) (n m : ℕ) (hh : h ≠ 0) :
    ((C c * X ^ n).comp ((X - C r) * C h⁻¹)).coeff m =
      if m ≤ n then
        c * h⁻¹ ^ n * (-r) ^ (n - m) * (n.choose m : RatFunc k)
      else 0 := by
  have hpow :
      ((X - C r) * C h⁻¹ : (RatFunc k)[X]) ^ n =
        C (h⁻¹ ^ n) * (X - C r) ^ n := by
    calc
      ((X - C r) * C h⁻¹) ^ n
          = (X - C r) ^ n * (C h⁻¹) ^ n := mul_pow _ _ n
      _ = (X - C r) ^ n * C (h⁻¹ ^ n) := by rw [← C_pow]
      _ = C (h⁻¹ ^ n) * (X - C r) ^ n := mul_comm _ _
  rw [C_mul_comp, X_pow_comp, hpow, ← mul_assoc, ← C_mul]
  by_cases hle : m ≤ n
  · simp only [hle, ite_true]
    have hsub : X - C r = X + C (-r) := by
      simp [sub_eq_add_neg]
    rw [hsub, coeff_C_mul, coeff_X_add_C_pow]
    ring
  · simp only [hle, ite_false]
    have hsub : X - C r = X + C (-r) := by
      simp [sub_eq_add_neg]
    rw [hsub, coeff_C_mul, coeff_X_add_C_pow]
    have hlt : n < m := Nat.not_le.mp hle
    simp [Nat.choose_eq_zero_of_lt hlt]

/-- High coefficients of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_highCoeffs810
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    let q := affineDepress68 h r p
    q.coeff 10 = 1 ∧
      q.coeff 9 = -10 * r + p.coeff 9 / h ^ 9 ∧
      q.coeff 8 =
        45 * r ^ 2 - 9 * (p.coeff 9 / h ^ 9) * r + p.coeff 8 / h ^ 8 ∧
      (∀ n, 10 < n → q.coeff n = 0) := by
  dsimp only
  let qscale : (RatFunc k)[X] := (X - C r) * C h⁻¹
  have hqdeg : qscale.natDegree = 1 := natDegree_affineScale810 h r hh
  let plow : (RatFunc k)[X] :=
    p - C (p.coeff 10) * X ^ 10 - C (p.coeff 9) * X ^ 9 -
      C (p.coeff 8) * X ^ 8
  have hplow : ∀ n, 8 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h8 | hlt8
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
            show n ≠ 9 by omega, show n ≠ 8 by omega]
  have hplowDeg : plow.natDegree ≤ 7 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = C (p.coeff 10) * X ^ 10 + C (p.coeff 9) * X ^ 9 +
        C (p.coeff 8) * X ^ 8 + plow := by
    simp only [plow]
    ring
  have hq :
      affineDepress68 h r p =
        (C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹) +
          plow.comp ((X - C r) * C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((X - C r) * C h⁻¹) := rfl
    have hsum (A B D E s : (RatFunc k)[X]) :
        (A + B + D + E).comp s =
          A.comp s + B.comp s + D.comp s + E.comp s := by
      have h1 : (A + B + D + E).comp s =
          (A + B + D).comp s + E.comp s := add_comp
      have h2 : (A + B + D).comp s =
          (A + B).comp s + D.comp s := add_comp
      have h3 : (A + B).comp s = A.comp s + B.comp s := add_comp
      rw [h1, h2, h3]
    exact hdef.trans ((congrArg (fun t => t.comp ((X - C r) * C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _))
  have hlow (n : ℕ) (hn : 8 ≤ n) :
      (plow.comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤
          plow.natDegree * ((X - C r) * C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((X - C r) * C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((X - C r) * C h⁻¹).natDegree ≤ 7 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤ 7 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 8 ≤ n))
  have hzero {c : RatFunc k} {n m : ℕ} (hmn : ¬ m ≤ n) :
      ((C c * X ^ n).comp ((X - C r) * C h⁻¹)).coeff m = 0 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 c h r n m hh]
    simp [hmn]
  have h10_10 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 10 = 1 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 10 hh]
    simp [hp10, Nat.choose_self, pow_zero]
    field_simp [hh]
  have h10_9 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 9 =
        -10 * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 9 hh]
    have hle : (9 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 9 = 10 := by decide
    simp [hp10, hle, hbin, pow_one]
    field_simp [hh]
  have h10_8 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 8 =
        45 * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 8 hh]
    have hle : (8 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 8 = 45 := by decide
    simp [hp10, hle, hbin, pow_two]
    field_simp [hh]
  have h9_9 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 9 =
        p.coeff 9 / h ^ 9 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 9 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  have h9_8 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 8 =
        -9 * (p.coeff 9 / h ^ 9) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 8 hh]
    have hle : (8 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 8 = 9 := by decide
    simp [hle, hbin, pow_one]
    field_simp [hh]
  have h8_8 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 8 =
        p.coeff 8 / h ^ 8 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 8 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq, coeff_add, coeff_add, coeff_add, h10_10,
      hzero (by omega : ¬ (10 : ℕ) ≤ 9),
      hzero (by omega : ¬ (10 : ℕ) ≤ 8), hlow 10 (by omega)]
    simp
  · rw [hq, coeff_add, coeff_add, coeff_add, h10_9, h9_9,
      hzero (by omega : ¬ (9 : ℕ) ≤ 8), hlow 9 (by omega)]
    ring
  · rw [hq, coeff_add, coeff_add, coeff_add, h10_8, h9_8, h8_8,
      hlow 8 (by omega)]
    ring
  · intro n hn
    rw [hq, coeff_add, coeff_add, coeff_add,
      hzero (by omega : ¬ n ≤ 10), hzero (by omega : ¬ n ≤ 9),
      hzero (by omega : ¬ n ≤ 8), hlow n (by omega)]
    simp

end AffineDecic810

/-! ## Source-facing second-face packet -/

section NonzeroSecondFace810

variable {k : Type*} [Field k] [CharZero k]

/-- The first octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h¹⁴`. -/
theorem nonzeroFace810_secondDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ alpha : k,
      localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6) (q.coeff 8)
          lambda =
        Polynomial.C alpha * h0 ^ 14 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
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
  have hqSrc : sourceToRatFunc68 q = sourceToRatFunc46 q := rfl
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = h ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src
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
      (differentialJacobian ratFuncDerivation68 f g).coeff 15 =
        (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 6) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) := by
    exact differentialJacobian_coeff_15_monicOcticDecic
      ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
  have hrow0 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 15) hbracket
    simpa [f, g, Polynomial.coeff_C, show (15 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf6 : f.coeff 6 = depressedA810 h (octicDepressionR810 h a7) a7 a6 := by
    dsimp only [f, depressedA810, a7, a6]
    rw [hpDep, coeff_depressedOctic68_six]
  have hg8' : g.coeff 8 =
      depressedP810 h (octicDepressionR810 h a7) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8]
  have halpha0 :
      ratFuncDerivation68
        (alphaResidual810 (f.coeff 6) (g.coeff 8)) = 0 :=
    alphaResidual810_deriv_zero ratFuncDerivation68 (f.coeff 6) (g.coeff 8)
      hrow0
  obtain ⟨alpha, halpha⟩ :
      ∃ a : k,
        alphaResidual810 (f.coeff 6) (g.coeff 8) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using halpha0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
            (q.coeff 8) lambda) =
        (32 : RatFunc k) * h ^ 14 *
          alphaResidual810 (f.coeff 6) (g.coeff 8) := by
    have hF := secondDefect_eq_clearedAlpha810 h a7 a6 b9 b8
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [localClearedSecondDefect810, map_sub, map_add, map_mul, map_pow,
      map_ofNat, RatFunc.algebraMap_C, h, a7, a6, b8, alphaResidual810,
      hf6, hg8'] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
            (q.coeff 8) lambda) =
        algebraMap k[X] (RatFunc k) (Polynomial.C (32 * alpha) * h0 ^ 14) := by
    rw [hclear, halpha]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨32 * alpha, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: at a root of the degree-one scale, the
subleading octic coefficient vanishes. -/
theorem nonzeroFace810_linearRoot_p7_zero
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    (p.coeff 7).eval a = 0 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace810_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  have heval := congrArg (fun t : k[X] => t.eval a) hM
  have h5 : (5 : k) ≠ 0 := by norm_num
  have hM0 : (localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
      (q.coeff 8) lambda).eval a = 0 := by
    rw [heval]
    simp [hroot]
  have hform :
      (localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
          (q.coeff 8) lambda).eval a =
        -((5 : k) * ((p.coeff 7).eval a) ^ 2) := by
    simp [localClearedSecondDefect810, hroot]
  have hsq : ((p.coeff 7).eval a) ^ 2 = 0 := by
    have h := hform.symm.trans hM0
    apply (mul_eq_zero.mp ?_).resolve_left h5
    linear_combination -h
  exact sq_eq_zero_iff.mp hsq

/-- Source-facing second integral for a normalized scale-two `(8,10)`
nonzero face. -/
theorem normalized810ScaleTwo_nonzeroFace_secondDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda alpha : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
            (q.coeff 8) lambda =
          Polynomial.C alpha * h0 ^ 14 := by
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
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace810_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8' hq10' hN' hD
  exact ⟨h0, lambda, alpha, hh0, hlambda, hh0degree, hH, hN', hM⟩

/-- Finite local initial packet of a normalized scale-two `(8,10)`
nonzero face: the degree-one scale divides the subleading octic
coefficient. -/
theorem normalized810ScaleTwo_nonzeroFace_p7_vanishes_at_root
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
        h0.eval a = 0 ∧ (p.coeff 7).eval a = 0 ∧
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
  have hp7 : (p.coeff 7).eval a = 0 :=
    nonzeroFace810_linearRoot_p7_zero p q H h0 j lambda a
      hp hq hh0 hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp7, hN'⟩

end NonzeroSecondFace810

#print axioms secondCoefficientJacobianRow_810
#print axioms depressedL810_eq_of_ninthPower
#print axioms differentialJacobian_coeff_15_monicOcticDecic
#print axioms nonzeroFace810_secondDefectPowerRelation
#print axioms nonzeroFace810_linearRoot_p7_zero
#print axioms normalized810ScaleTwo_nonzeroFace_secondDefectPowerRelation
#print axioms normalized810ScaleTwo_nonzeroFace_p7_vanishes_at_root

end Max11DegreeRoutes
