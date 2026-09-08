import LowScale410ScaleTwoSourceFace
import LowScale810ScaleTwoSecondFace

/-! # Scale-two second face for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the next Keller coefficient is the degree-`11` Jacobian
row.  After the quartic affine depression that kills `z³`, that row is the
weighted derivative `10 A' - 4 P' = 0` of the first new quartic/decic pair.
The resulting first integral clears to a polynomial defect `M` of weight
eight, and evaluating at the root of `h` forces `q₈(a) = 0`.

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
degrees `(4,10)`.  It is the source of the first quartic/decic defect after
the nonic discriminator. -/
theorem secondCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 9).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 11) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (11 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 11 :
      Finset (ℕ × ℕ)) =
      ({(0, 11), (1, 10), (2, 9), (3, 8), (4, 7), (5, 6), (6, 5),
        (7, 4), (8, 3), (9, 2), (10, 1), (11, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
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
  rw [hC8, hC9, hC10, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Quartic/decic depression and the cleared defect -/

section Depression410

variable {F : Type*} [Field F] [CharZero F]

/-- Quartic linear depression that kills the `z³` coefficient of a monic
degree-four source with leading coefficient `h⁴`. -/
abbrev quarticDepressionR410 (h a3 : F) : F :=
  quarticDepressionR46 h a3

/-- Depressed quartic `z²` coefficient.  This is the first new quartic
coordinate after the source discriminator. -/
abbrev depressedA410 (h r a3 a2 : F) : F :=
  depressedA46 h r a3 a2

/-- Depressed decic `z⁹` coefficient. -/
abbrev depressedL410 (h r b9 : F) : F :=
  depressedL810 h r b9

/-- Depressed decic `z⁸` coefficient. -/
abbrev depressedP410 (h r b9 b8 : F) : F :=
  depressedP810 h r b9 b8

/-- Polynomial numerator of `8 h⁶ A`. -/
def localClearedA410 (h a3 a2 : F[X]) : F[X] :=
  (8 : F[X]) * a2 * h ^ 4 - (3 : F[X]) * a3 ^ 2

/-- Polynomial numerator of `8 h⁸ (P - (5/2) A)` on the ninth-power
face.  This is the sharpest cleared next defect. -/
def localClearedSecondDefect410 (h a3 a2 b8 : F[X]) (lambda : F) : F[X] :=
  (8 : F[X]) * b8 - (20 : F[X]) * a2 * h ^ 6 +
    (9 : F[X]) * Polynomial.C lambda * a3 * h ^ 5 -
    (15 : F[X]) * a3 ^ 2 * h ^ 2

theorem natDegree_depressedQuartic46_le_four
    (A B C0 : F) :
    (depressedQuartic46 A B C0).natDegree ≤ 4 := by
  have add4 {p q : F[X]} (hp : p.natDegree ≤ 4) (hq : q.natDegree ≤ 4) :
      (p + q).natDegree ≤ 4 :=
    (natDegree_add_le p q).trans (max_le hp hq)
  have term (c : F) (k : ℕ) (hk : k ≤ 4) :
      (C c * X ^ k : F[X]).natDegree ≤ 4 :=
    (natDegree_C_mul_X_pow_le c k).trans hk
  simp only [depressedQuartic46]
  have h0 : (X ^ 4 : F[X]).natDegree ≤ 4 := natDegree_X_pow_le (R := F) 4
  have h1 : (X ^ 4 + C A * X ^ 2).natDegree ≤ 4 :=
    add4 h0 (term A 2 (by omega))
  have h2 : (X ^ 4 + C A * X ^ 2 + C B * X).natDegree ≤ 4 :=
    add4 h1 ((natDegree_C_mul_le B X).trans
      ((natDegree_X_le).trans (by omega)))
  exact add4 h2 ((natDegree_C C0).trans_le (by omega))

theorem coeff_depressedQuartic46_of_gt_four
    (A B C0 : F) {n : ℕ} (hn : 4 < n) :
    (depressedQuartic46 A B C0).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (natDegree_depressedQuartic46_le_four A B C0) hn)

theorem coeff_depressedQuartic46_four
    (A B C0 : F) :
    (depressedQuartic46 A B C0).coeff 4 = 1 := by
  simp [depressedQuartic46, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem coeff_depressedQuartic46_three
    (A B C0 : F) :
    (depressedQuartic46 A B C0).coeff 3 = 0 := by
  simp [depressedQuartic46, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem coeff_depressedQuartic46_two
    (A B C0 : F) :
    (depressedQuartic46 A B C0).coeff 2 = A := by
  simp [depressedQuartic46, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the first quartic coordinate. -/
theorem depressedA410_eq_cleared
    (h a3 a2 : F) (hh : h ≠ 0) :
    depressedA410 h (quarticDepressionR410 h a3) a3 a2 =
      (8 * a2 * h ^ 4 - 3 * a3 ^ 2) / (8 * h ^ 6) := by
  simp only [depressedA410, depressedA46, quarticDepressionR410,
    quarticDepressionR46]
  field_simp [hh]
  ring

/-- On the nonzero first face the depressed decic `z⁹` coefficient is the
ground constant `-λ/2`. -/
theorem depressedL410_eq_of_ninthPower
    (h a3 b9 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    depressedL410 h (quarticDepressionR410 h a3) b9 = -lambda / 2 := by
  have hh3 : 4 * h ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 3 hh)
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  simp only [depressedL410, depressedL810, quarticDepressionR410,
    quarticDepressionR46]
  have hrewrite :
      -10 * (a3 / (4 * h ^ 3)) + b9 / h ^ 9 =
        (-10 * a3 * h ^ 6 + 4 * b9) / (4 * h ^ 9) := by
    field_simp [hh, hh3, hh9]
  rw [hrewrite]
  have hnum : -10 * a3 * h ^ 6 + 4 * b9 = -2 * (5 * a3 * h ^ 6 - 2 * b9) := by
    ring
  rw [hnum, hN]
  field_simp [hh, hh9]
  ring

/-- Clearing the first integral `P - (5/2) A` against `h⁸` on the ninth-power
face. -/
theorem secondDefect_eq_clearedAlpha410
    (h a3 a2 b9 b8 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (8 : F) * h ^ 8 *
        (depressedP410 h (quarticDepressionR410 h a3) b9 b8 -
          (5 / 2 : F) *
            depressedA410 h (quarticDepressionR410 h a3) a3 a2) =
      (8 : F) * b8 - (20 : F) * a2 * h ^ 6 +
        (9 : F) * lambda * a3 * h ^ 5 - (15 : F) * a3 ^ 2 * h ^ 2 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hb9 : 2 * b9 = 5 * a3 * h ^ 6 - lambda * h ^ 9 := by
    linear_combination -hN
  have hb9div : b9 = (5 * a3 * h ^ 6 - lambda * h ^ 9) / 2 :=
    eq_div_of_mul_eq h2 (by rw [mul_comm]; exact hb9)
  rw [hb9div]
  simp only [depressedP410, depressedP810, depressedA410, depressedA46,
    quarticDepressionR410, quarticDepressionR46]
  field_simp [hh, h2, h4, h8, hh3, hh6, hh8pow, hh9]
  ring

end Depression410

/-! ## Degree-`11` depressed Jacobian coefficient -/

section DepressedRow410

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`11` Jacobian coefficient is
exactly `10 A' - 4 P'`. -/
theorem differentialJacobian_coeff_11_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 11 =
      (10 : F) * d (f.coeff 2) - (4 : F) * d (g.coeff 8) := by
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
  have hmem29 : ((2, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem38 : ((3, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 11 =
        (10 : F) * d (f.coeff 2) := by
    have hprod :
        (coefficientDeriv d f * g.derivative).coeff 11 =
          (coefficientDeriv d f).coeff 2 * g.derivative.coeff 9 := by
      rw [Polynomial.coeff_mul]
      refine Finset.sum_eq_single_of_mem _ hmem29 ?_
      intro b hb hne
      have hij : b.1 + b.2 = 11 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hi : b.1 ≠ 2 := by
        intro h2eq
        apply hne
        ext
        · exact h2eq
        · omega
      by_cases hige : 3 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hder : g.derivative.coeff 9 = (10 : F) := by
      rw [Polynomial.coeff_derivative, hg10]
      norm_num
    rw [hprod, coeff_coefficientDeriv, hder, mul_comm]
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 11 =
        (4 : F) * d (g.coeff 8) := by
    have hprod :
        (f.derivative * coefficientDeriv d g).coeff 11 =
          f.derivative.coeff 3 * (coefficientDeriv d g).coeff 8 := by
      rw [Polynomial.coeff_mul]
      refine Finset.sum_eq_single_of_mem _ hmem38 ?_
      intro b hb hne
      have hij : b.1 + b.2 = 11 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hi : b.1 ≠ 3 := by
        intro h3eq
        apply hne
        ext
        · exact h3eq
        · omega
      by_cases hige : 4 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · have hj : 9 ≤ b.2 := by omega
        simp [hgd'_high b.2 hj]
    have hder : f.derivative.coeff 3 = (4 : F) := by
      rw [Polynomial.coeff_derivative, hf4]
      norm_num
    rw [hprod, coeff_coefficientDeriv, hder]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]

/-- The first residual `P - (5/2) A` of the degree-`11` row. -/
def alphaResidual410 (A P : F) : F := P - (5 / 2 : F) * A

theorem alphaResidual410_deriv_zero
    (d : Derivation k F F) (A P : F)
    (hrow : (10 : F) * d A - (4 : F) * d P = 0) :
    d (alphaResidual410 A P) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  simp only [alphaResidual410, map_sub, Derivation.leibniz, h52, zero_mul,
    add_zero]
  linear_combination (-1 / 4 : F) * hrow

end DepressedRow410

/-! ## Linear divisibility at a simple root -/

section LinearDvd410

variable {k : Type*} [Field k]

/-- A degree-one polynomial divides every polynomial vanishing at its
unique root. -/
theorem linearPolynomial_dvd_of_eval_eq_zero_410
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

end LinearDvd410

/-! ## Source-facing second-face packet -/

section NonzeroSecondFace410

variable {k : Type*} [Field k] [CharZero k]

/-- The first quartic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁸`. -/
theorem nonzeroFace410_secondDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ alpha : k,
      localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2) (q.coeff 8)
          lambda =
        Polynomial.C alpha * h0 ^ 8 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
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
          (depressedB46 hRF (quarticDepressionR410 hRF a3) a3 a2
            (algebraMap k[X] (RatFunc k) (p.coeff 1)))
          (depressedC46 hRF (quarticDepressionR410 hRF a3) a3 a2
            (algebraMap k[X] (RatFunc k) (p.coeff 1))
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
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src
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
      (differentialJacobian ratFuncDerivation68 f g).coeff 11 =
        (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) := by
    exact differentialJacobian_coeff_11_monicQuarticDecic
      ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
  have hrow0 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) -
        (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf2 : f.coeff 2 = depressedA410 hRF (quarticDepressionR410 hRF a3) a3 a2 := by
    dsimp only [f, depressedA410, a3, a2]
    rw [hpDep, coeff_depressedQuartic46_two]
  have hg8' : g.coeff 8 =
      depressedP410 hRF (quarticDepressionR410 hRF a3) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP410, depressedP810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have halpha0 :
      ratFuncDerivation68
        (alphaResidual410 (f.coeff 2) (g.coeff 8)) = 0 :=
    alphaResidual410_deriv_zero ratFuncDerivation68 (f.coeff 2) (g.coeff 8)
      hrow0
  obtain ⟨alpha, halpha⟩ :
      ∃ a : k,
        alphaResidual410 (f.coeff 2) (g.coeff 8) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using halpha0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2)
            (q.coeff 8) lambda) =
        (8 : RatFunc k) * hRF ^ 8 *
          alphaResidual410 (f.coeff 2) (g.coeff 8) := by
    have hF := secondDefect_eq_clearedAlpha410 hRF a3 a2 b9 b8
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [localClearedSecondDefect410, map_sub, map_add, map_mul, map_pow,
      map_ofNat, RatFunc.algebraMap_C, hRF, a3, a2, b8, alphaResidual410,
      hf2, hg8'] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2)
            (q.coeff 8) lambda) =
        algebraMap k[X] (RatFunc k) (Polynomial.C (8 * alpha) * h0 ^ 8) := by
    rw [hclear, halpha]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  refine ⟨8 * alpha, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: at a root of the degree-one scale, the
subleading decic coefficient `q₈` vanishes. -/
theorem nonzeroFace410_linearRoot_q8_zero
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    (q.coeff 8).eval a = 0 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace410_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  have heval := congrArg (fun t : k[X] => t.eval a) hM
  have h8 : (8 : k) ≠ 0 := by norm_num
  have hM0 : (localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2)
      (q.coeff 8) lambda).eval a = 0 := by
    rw [heval]
    simp [hroot]
  have hform :
      (localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2)
          (q.coeff 8) lambda).eval a =
        (8 : k) * (q.coeff 8).eval a := by
    simp [localClearedSecondDefect410, hroot]
  have h := hform.symm.trans hM0
  exact (mul_eq_zero.mp h).resolve_left h8

/-- Combined with the ninth-power first face, the same root kills `q₉`. -/
theorem nonzeroFace410_linearRoot_q9_zero
    (p q : k[X][X]) (H h0 : k[X]) (lambda a : k)
    (hH : H = h0 ^ 2)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hroot : h0.eval a = 0) :
    (q.coeff 9).eval a = 0 := by
  have h2 : (2 : k) ≠ 0 := by norm_num
  have hNeval := congrArg (fun t : k[X] => t.eval a) hN
  have hform :
      ((5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9).eval a =
        -((2 : k) * (q.coeff 9).eval a) := by
    simp [hH, hroot]
  have hrhs : (Polynomial.C lambda * h0 ^ 9).eval a = 0 := by
    simp [hroot]
  have h := hform.symm.trans (hNeval.trans hrhs)
  apply (mul_eq_zero.mp ?_).resolve_left h2
  linear_combination -h

/-- Exact first-face divisibility on the nonzero square core: `h⁶` divides
`q₉`. -/
theorem nonzeroFace410_h6_dvd_q9
    (p q : k[X][X]) (H h0 : k[X]) (lambda : k)
    (hH : H = h0 ^ 2)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9) :
    h0 ^ 6 ∣ q.coeff 9 := by
  have h2 : (2 : k) ≠ 0 := by norm_num
  have hN' :
      (5 : k[X]) * p.coeff 3 * h0 ^ 6 - (2 : k[X]) * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    have hH3 : H ^ 3 = h0 ^ 6 := by
      simp only [hH]
      ring
    simpa [hH3] using hN
  have hmul :
      (2 : k[X]) * q.coeff 9 =
        h0 ^ 6 * ((5 : k[X]) * p.coeff 3 - Polynomial.C lambda * h0 ^ 3) := by
    calc
      (2 : k[X]) * q.coeff 9 =
          (5 : k[X]) * p.coeff 3 * h0 ^ 6 -
            Polynomial.C lambda * h0 ^ 9 := by
        linear_combination -hN'
      _ = h0 ^ 6 * ((5 : k[X]) * p.coeff 3 - Polynomial.C lambda * h0 ^ 3) := by
        ring
  refine ⟨Polynomial.C (2 : k)⁻¹ *
      ((5 : k[X]) * p.coeff 3 - Polynomial.C lambda * h0 ^ 3), ?_⟩
  have hC2 : (2 : k[X]) = Polynomial.C (2 : k) := Polynomial.C_eq_natCast 2
  calc
    q.coeff 9 =
        Polynomial.C (2 : k)⁻¹ * ((2 : k[X]) * q.coeff 9) := by
      rw [hC2, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h2, map_one, one_mul]
    _ = Polynomial.C (2 : k)⁻¹ *
        (h0 ^ 6 * ((5 : k[X]) * p.coeff 3 - Polynomial.C lambda * h0 ^ 3)) := by
      rw [hmul]
    _ = h0 ^ 6 * (Polynomial.C (2 : k)⁻¹ *
        ((5 : k[X]) * p.coeff 3 - Polynomial.C lambda * h0 ^ 3)) := by
      ring

/-- Source-facing second integral for a normalized scale-two `(4,10)`
nonzero face. -/
theorem normalized410ScaleTwo_nonzeroFace_secondDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda alpha : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2)
            (q.coeff 8) lambda =
          Polynomial.C alpha * h0 ^ 8 := by
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
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace410_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4' hq10' hN' hD
  exact ⟨h0, lambda, alpha, hh0, hlambda, hh0degree, hH, hN', hM⟩

/-- Finite local initial packet of a normalized scale-two `(4,10)`
nonzero face: the degree-one scale divides `q₈`, and the first-face
relation supplies the exact sixth-power divisibility of `q₉`. -/
theorem normalized410ScaleTwo_nonzeroFace_q8_vanishes_at_root
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
        h0.eval a = 0 ∧ (q.coeff 8).eval a = 0 ∧ (q.coeff 9).eval a = 0 ∧
        h0 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 9 ∧
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
  have hq8 : (q.coeff 8).eval a = 0 :=
    nonzeroFace410_linearRoot_q8_zero p q H h0 j lambda a
      hp hq hh0 hH hp4' hq10' hN' hD hroot
  have hq9 : (q.coeff 9).eval a = 0 :=
    nonzeroFace410_linearRoot_q9_zero p q H h0 lambda a hH hN' hroot
  have hq8dvd : h0 ∣ q.coeff 8 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 (q.coeff 8) a
      hh0degree hroot hq8
  have hq9dvd : h0 ^ 6 ∣ q.coeff 9 :=
    nonzeroFace410_h6_dvd_q9 p q H h0 lambda hH hN'
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hq8, hq9,
    hq8dvd, hq9dvd, hN'⟩

end NonzeroSecondFace410

#print axioms secondCoefficientJacobianRow_410
#print axioms depressedL410_eq_of_ninthPower
#print axioms differentialJacobian_coeff_11_monicQuarticDecic
#print axioms nonzeroFace410_secondDefectPowerRelation
#print axioms nonzeroFace410_linearRoot_q8_zero
#print axioms nonzeroFace410_linearRoot_q9_zero
#print axioms nonzeroFace410_h6_dvd_q9
#print axioms normalized410ScaleTwo_nonzeroFace_secondDefectPowerRelation
#print axioms normalized410ScaleTwo_nonzeroFace_q8_vanishes_at_root

end Max11DegreeRoutes
