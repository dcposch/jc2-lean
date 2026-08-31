import LowScale410ScaleTwoEighthFace

/-! # Scale-two ninth face for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the eighth-face packet supplies the degree-`5`
integral of weight twenty-six and the one-parameter jet `h² ∣ p₃`,
`h⁶ ∣ q₈`, `h⁴ ∣ q₇`, `h² ∣ q₆`, `h⁸ ∣ q₉` together with
`2 (q₈/h⁶)(a) = 5 t₁²`, `4 (q₇/h⁴)(a) = 5 t₁³`, `16 (q₆/h²)(a) = 5 t₁⁴`,
`32 q₅(a) = t₁⁵` on `p₃ = t₁ h²` and `4 p₂(a) = t₁²`.

The next unused Keller coefficient is the degree-`4` Jacobian row.  After
the same quartic depression that kills `z³`, that row is
`5 S C' + 4 T B' + 3 U A' - B T' - 2 A U' - 4 W' = 0`.  The corresponding
first integral is the residual `θ` below.  Clearing it against the
decic `z¹` coordinate produces a defect of weight twenty-nine, larger
than the remaining exact jet, so this file isolates that Jacobian
identity, the first integral, and the strongest exact refinement of the
eighth packet.

Evaluating the second through sixth defects on the eighth-face jet at
the next order of `h` is an inconsistent linear system unless `t₁(a) = 0`.
The one-parameter jet therefore collapses: `h³ ∣ p₃`, `h ∣ p₂`,
`h⁷ ∣ q₈`, `h⁶ ∣ q₇`, `h⁴ ∣ q₆`, `h² ∣ q₅`, together with
`2 (q₈/h⁷)(a) = 5 (p₂/h)(a)`.  No further individual vanishing of
`p₁, p₀, q₄, q₃, q₂` is claimed.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The ninth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  Unused Jacobian coefficients of the eighth face start
at degree `4`. -/
theorem ninthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 4) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (4 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 4 :
      Finset (ℕ × ℕ)) =
      ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)) :=
    by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  rw [hC2, hC3, hC4, hC5]
  linear_combination hcoeff

/-! ## Quartic constant and decic `z¹` coordinates -/

section Depression410Ninth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z¹` coefficient. -/
def depressedW410 (h r b9 b8 b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  -10 * r ^ 9 + 9 * (b9 / h ^ 9) * r ^ 8 -
    8 * (b8 / h ^ 8) * r ^ 7 + 7 * (b7 / h ^ 7) * r ^ 6 -
    6 * (b6 / h ^ 6) * r ^ 5 + 5 * (b5 / h ^ 5) * r ^ 4 -
    4 * (b4 / h ^ 4) * r ^ 3 + 3 * (b3 / h ^ 3) * r ^ 2 -
    2 * (b2 / h ^ 2) * r + b1 / h

/-- First residual of the degree-`4` row.  Equivalent to
`W - (3/4) ζ A - ε B - (5/4) δ C - (5/32) δ A² - (3/4) γ A B
- 2 α B C - (21/16) β A C - (21/32) β B² + (7/128) β A³
- (15/8) A B C - (5/16) B³ + (5/32) A³ B + (45/2048) L A⁴
- (45/128) L A² C - (45/128) L A B² - (45/32) L C²`
on the second- through seventh-face integrals. -/
def thetaResidual410 (L A B C0 P Q R S0 T0 U0 W0 : F) : F :=
  W0 - (3 / 4 : F) * zetaResidual410 L A B C0 P Q R S0 U0 * A -
    epsilonResidual410 L A B C0 P Q R T0 * B -
    (5 / 4 : F) * deltaResidual410 L A B C0 P Q S0 * C0 -
    (5 / 32 : F) * deltaResidual410 L A B C0 P Q S0 * A ^ 2 -
    (3 / 4 : F) * gammaResidual410 L A B C0 P R * A * B -
    (2 : F) * alphaResidual410 A P * B * C0 -
    (21 / 16 : F) * betaResidual410 L A B Q * A * C0 -
    (21 / 32 : F) * betaResidual410 L A B Q * B ^ 2 +
    (7 / 128 : F) * betaResidual410 L A B Q * A ^ 3 -
    (15 / 8 : F) * A * B * C0 - (5 / 16 : F) * B ^ 3 +
    (5 / 32 : F) * A ^ 3 * B + (45 / 2048 : F) * L * A ^ 4 -
    (45 / 128 : F) * L * A ^ 2 * C0 -
    (45 / 128 : F) * L * A * B ^ 2 - (45 / 32 : F) * L * C0 ^ 2

end Depression410Ninth

/-! ## Degree-`4` depressed Jacobian coefficient -/

section DepressedRow410Ninth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`4` Jacobian coefficient is
exactly `5 S C' + 4 T B' + 3 U A' - B T' - 2 A U' - 4 W'`. -/
theorem differentialJacobian_coeff_4_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 4 =
      (5 : F) * g.coeff 5 * d (f.coeff 0) +
        (4 : F) * g.coeff 4 * d (f.coeff 1) +
        (3 : F) * g.coeff 3 * d (f.coeff 2) -
          f.coeff 1 * d (g.coeff 4) -
          (2 : F) * f.coeff 2 * d (g.coeff 3) -
          (4 : F) * d (g.coeff 1) := by
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
  have hmem04 : ((0, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem13 : ((1, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem22 : ((2, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem31 : ((3, 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 4 =
        (5 : F) * g.coeff 5 * d (f.coeff 0) +
          (4 : F) * g.coeff 4 * d (f.coeff 1) +
          (3 : F) * g.coeff 3 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne01 : ((0, 4) : ℕ × ℕ) ≠ (1, 3) := by decide
    have hne02 : ((0, 4) : ℕ × ℕ) ≠ (2, 2) := by decide
    have hne12 : ((1, 3) : ℕ × ℕ) ≠ (2, 2) := by decide
    have hsubset : ({(0, 4), (1, 3), (2, 2)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (4 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b; exact hmem04
      · subst b; exact hmem13
      · subst b; exact hmem22
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 4), (1, 3), (2, 2)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 4 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne04 : b ≠ (0, 4) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne13 : b ≠ (1, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne22 : b ≠ (2, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 3 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne04
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne13
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne22
          ext
          · exact h2
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 4), (1, 3), (2, 2)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 2 := by
      rw [Finset.sum_insert (by simp [hne01, hne02]),
        Finset.sum_insert (by simp [hne12]), Finset.sum_singleton]
      ring
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder4, hder3, hder2]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 4 =
        f.coeff 1 * d (g.coeff 4) +
          (2 : F) * f.coeff 2 * d (g.coeff 3) +
          (4 : F) * d (g.coeff 1) := by
    rw [Polynomial.coeff_mul]
    have hne04_13 : ((0, 4) : ℕ × ℕ) ≠ (1, 3) := by decide
    have hne04_31 : ((0, 4) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne13_31 : ((1, 3) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hsubset : ({(0, 4), (1, 3), (3, 1)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (4 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b; exact hmem04
      · subst b; exact hmem13
      · subst b; exact hmem31
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 4), (1, 3), (3, 1)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 4 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne04 : b ≠ (0, 4) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne13 : b ≠ (1, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne31 : b ≠ (3, 1) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 4 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h2 : b.1 = 2
        · have hf2 : f.derivative.coeff b.1 = 0 := by
            rw [h2, Polynomial.coeff_derivative, hf3]
            simp
          simp [hf2]
        · have hne0 : b.1 ≠ 0 := by
            intro h0
            apply hne04
            ext
            · exact h0
            · omega
          have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne13
            ext
            · exact h1
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne31
            ext
            · exact h3
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 4), (1, 3), (3, 1)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 1 := by
      rw [Finset.sum_insert (by simp [hne04_13, hne04_31]),
        Finset.sum_insert (by simp [hne13_31]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : f.derivative.coeff 3 = (4 : F) := by
      rw [Polynomial.coeff_derivative, hf4]; norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder3]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

set_option maxHeartbeats 8000000 in
theorem thetaResidual410_deriv_zero
    (d : Derivation k F F) (L A B C0 P Q R S0 T0 U0 W0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual410 A P) = 0)
    (hbeta : d (betaResidual410 L A B Q) = 0)
    (hgamma : d (gammaResidual410 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual410 L A B C0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual410 L A B C0 P Q R T0) = 0)
    (hzeta : d (zetaResidual410 L A B C0 P Q R S0 U0) = 0)
    (hrow : (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A - B * d T0 - (2 : F) * A * d U0 -
        (4 : F) * d W0 = 0) :
    d (thetaResidual410 L A B C0 P Q R S0 T0 U0 W0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h21 : d (21 : F) = 0 := d.map_natCast 21
  have h25 : d (25 : F) = 0 := d.map_natCast 25
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h35 : d (35 : F) = 0 := d.map_natCast 35
  have h45 : d (45 : F) = 0 := d.map_natCast 45
  have h49 : d (49 : F) = 0 := d.map_natCast 49
  have h63 : d (63 : F) = 0 := d.map_natCast 63
  have h75 : d (75 : F) = 0 := d.map_natCast 75
  have h105 : d (105 : F) = 0 := d.map_natCast 105
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h225 : d (225 : F) = 0 := d.map_natCast 225
  have h231 : d (231 : F) = 0 := d.map_natCast 231
  have h385 : d (385 : F) = 0 := d.map_natCast 385
  have h405 : d (405 : F) = 0 := d.map_natCast 405
  have h975 : d (975 : F) = 0 := d.map_natCast 975
  have h1755 : d (1755 : F) = 0 := d.map_natCast 1755
  have h2048 : d (2048 : F) = 0 := d.map_natCast 2048
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h94 : d (9 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h9]
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h32div : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h74 : d (7 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h7]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h72 : d (7 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h7]
  have h92 : d (9 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h9]
  have h158 : d (15 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h15]
  have h1516 : d (15 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h15]
  have h2116 : d (21 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h21]
  have h2132 : d (21 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h21]
  have h532 : d (5 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h5]
  have h7128 : d (7 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h7]
  have h45128 : d (45 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h45]
  have h452048 : d (45 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h45]
  have h4532 : d (45 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h45]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h5]
  have h258 : d (25 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h25]
  have h2532 : d (25 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h25]
  have h3516 : d (35 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h35]
  have h3532 : d (35 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h35]
  have h105128 : d (105 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h105]
  have h4516 : d (45 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h45]
  have h7564 : d (75 / 64 : F) = 0 := by
    have h64 : d (64 : F) = 0 := d.map_natCast 64
    simp [Derivation.leibniz_div, h64, h75]
  have h975256 : d (975 / 256 : F) = 0 := by
    have h256 : d (256 : F) = 0 := d.map_natCast 256
    simp [Derivation.leibniz_div, h256, h975]
  have h17552048 : d (1755 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h1755]
  have h405128 : d (405 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h405]
  have h22532 : d (225 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h225]
  have h4932 : d (49 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h49]
  have h6316 : d (63 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h63]
  have h6332 : d (63 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h63]
  have h358 : d (35 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h35]
  have h231128 : d (231 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h231]
  have h38564 : d (385 / 64 : F) = 0 := by
    have h64 : d (64 : F) = 0 := d.map_natCast 64
    simp [Derivation.leibniz_div, h64, h385]
  have hP0 : d P - (5 / 2 : F) * d A = 0 := by
    simpa [alphaResidual410, map_sub, Derivation.leibniz, h52, zero_mul,
      add_zero] using halpha
  have hQ0 : d Q - (5 / 2 : F) * d B - (9 / 4 : F) * L * d A = 0 := by
    simpa [betaResidual410, map_sub, Derivation.leibniz, h52, h94, hL,
      zero_mul, add_zero, mul_zero] using hbeta
  have hsqA : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]; ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz]; ring
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz]; ring
  have hcube : d (A * A * A) = (3 : F) * (A * A) * d A := by
    simp [Derivation.leibniz]; ring
  have hfourth : d (A * A * A * A) = (4 : F) * (A * A * A) * d A := by
    simp [Derivation.leibniz]; ring
  have hR0 :
      d R - (5 / 2 : F) * d C0 - (9 / 4 : F) * L * d B -
          (2 : F) * A * d P - (2 : F) * P * d A +
          (25 / 4 : F) * A * d A = 0 := by
    have hexp :
        gammaResidual410 L A B C0 P R =
          R - (5 / 2 : F) * C0 - (9 / 4 : F) * L * B -
            (2 : F) * P * A + (25 / 8 : F) * (A * A) := by
      simp only [gammaResidual410, pow_two]
    have hdg :
        d (R - (5 / 2 : F) * C0 - (9 / 4 : F) * L * B -
            (2 : F) * P * A + (25 / 8 : F) * (A * A)) = 0 := by
      simpa [hexp] using hgamma
    simp [map_sub, map_add, Derivation.leibniz, h2, h52, h94, h258, hL,
      hsqA, zero_mul, add_zero, mul_zero] at hdg
    linear_combination hdg
  have hS0 :
      d S0 - (9 / 4 : F) * L * d C0 - (2 : F) * B * d P -
          (2 : F) * P * d B - (7 / 4 : F) * A * d Q -
          (7 / 4 : F) * Q * d A + (45 / 8 : F) * B * d A +
          (45 / 8 : F) * A * d B + (81 / 16 : F) * L * A * d A = 0 := by
    have hexp :
        deltaResidual410 L A B C0 P Q S0 =
          S0 - (9 / 4 : F) * L * C0 - (2 : F) * P * B -
            (7 / 4 : F) * Q * A + (45 / 8 : F) * A * B +
            (81 / 32 : F) * L * (A * A) := by
      simp only [deltaResidual410, alphaResidual410, betaResidual410,
        pow_two]
      ring
    have h458 : d (45 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h45]
    have h8132 : d (81 / 32 : F) = 0 := by
      have h81 : d (81 : F) = 0 := d.map_natCast 81
      simp [Derivation.leibniz_div, h32, h81]
    have hdg :
        d (S0 - (9 / 4 : F) * L * C0 - (2 : F) * P * B -
            (7 / 4 : F) * Q * A + (45 / 8 : F) * A * B +
            (81 / 32 : F) * L * (A * A)) = 0 := by
      simpa [hexp] using hdelta
    simp [map_sub, map_add, Derivation.leibniz, h2, h94, h74, h458, h8132,
      hL, hsqA, zero_mul, add_zero, mul_zero] at hdg
    linear_combination hdg
  have hT0 :
      d T0 - (2 : F) * C0 * d P - (2 : F) * P * d C0 -
          (7 / 4 : F) * B * d Q - (7 / 4 : F) * Q * d B -
          (3 / 2 : F) * A * d R - (3 / 2 : F) * R * d A +
          (2 : F) * (A * A) * d P + (4 : F) * P * A * d A +
          (9 / 2 : F) * L * B * d A + (9 / 2 : F) * L * A * d B +
          (5 : F) * C0 * d A + (5 : F) * A * d C0 +
          (5 : F) * B * d B - (15 / 2 : F) * (A * A) * d A = 0 := by
    have hexp :
        epsilonResidual410 L A B C0 P Q R T0 =
          T0 - (2 : F) * P * C0 - (7 / 4 : F) * Q * B -
            (3 / 2 : F) * R * A + (2 : F) * P * (A * A) +
            (9 / 2 : F) * L * A * B + (5 : F) * A * C0 +
            (5 / 2 : F) * (B * B) - (5 / 2 : F) * (A * A * A) := by
      simp only [epsilonResidual410, alphaResidual410, betaResidual410,
        gammaResidual410, pow_two, pow_three]
      ring
    have hdg :
        d (T0 - (2 : F) * P * C0 - (7 / 4 : F) * Q * B -
            (3 / 2 : F) * R * A + (2 : F) * P * (A * A) +
            (9 / 2 : F) * L * A * B + (5 : F) * A * C0 +
            (5 / 2 : F) * (B * B) - (5 / 2 : F) * (A * A * A)) = 0 := by
      simpa [hexp] using hepsilon
    simp [map_sub, map_add, Derivation.leibniz, h2, h3, h5, h52, h74,
      h32div, h92, hL, hsqA, hsqB, hcube, zero_mul, add_zero,
      mul_zero] at hdg
    linear_combination hdg
  have hU0 :
      d U0 - (5 / 4 : F) * S0 * d A - (5 / 4 : F) * A * d S0 -
          (3 / 2 : F) * R * d B - (3 / 2 : F) * B * d R -
          (7 / 4 : F) * Q * d C0 - (7 / 4 : F) * C0 * d Q +
          (7 / 2 : F) * B * P * d A + (7 / 2 : F) * A * P * d B +
          (7 / 2 : F) * A * B * d P + (49 / 16 : F) * A * Q * d A +
          (49 / 32 : F) * (A * A) * d Q +
          (63 / 16 : F) * L * C0 * d A + (63 / 16 : F) * L * A * d C0 +
          (63 / 16 : F) * L * B * d B +
          (35 / 8 : F) * C0 * d B + (35 / 8 : F) * B * d C0 -
          (693 / 128 : F) * L * (A * A) * d A -
          (385 / 32 : F) * A * B * d A -
          (385 / 64 : F) * (A * A) * d B = 0 := by
    have hexp :
        zetaResidual410 L A B C0 P Q R S0 U0 =
          U0 - (5 / 4 : F) * A * S0 - (3 / 2 : F) * B * R -
            (7 / 4 : F) * C0 * Q + (7 / 2 : F) * A * B * P +
            (49 / 32 : F) * (A * A) * Q + (63 / 16 : F) * L * A * C0 +
            (63 / 32 : F) * L * (B * B) + (35 / 8 : F) * B * C0 -
            (231 / 128 : F) * L * (A * A * A) -
            (385 / 64 : F) * (A * A) * B := by
      simp only [zetaResidual410, alphaResidual410, betaResidual410,
        gammaResidual410, deltaResidual410, pow_two, pow_three]
      ring
    have hdg :
        d (U0 - (5 / 4 : F) * A * S0 - (3 / 2 : F) * B * R -
            (7 / 4 : F) * C0 * Q + (7 / 2 : F) * A * B * P +
            (49 / 32 : F) * (A * A) * Q + (63 / 16 : F) * L * A * C0 +
            (63 / 32 : F) * L * (B * B) + (35 / 8 : F) * B * C0 -
            (231 / 128 : F) * L * (A * A * A) -
            (385 / 64 : F) * (A * A) * B) = 0 := by
      simpa [hexp] using hzeta
    have h693128 : d (693 / 128 : F) = 0 := by
      have h693 : d (693 : F) = 0 := d.map_natCast 693
      simp [Derivation.leibniz_div, h128, h693]
    simp [map_sub, map_add, Derivation.leibniz, h2, h3, h4, h5, h7, h8,
      h16, h32, h54, h32div, h74, h72, h4932, h6316, h6332, h358,
      h231128, h38564, hL, hsqA, hsqB, hcube, zero_mul, add_zero,
      mul_zero] at hdg
    linear_combination hdg
  have hexp :
      thetaResidual410 L A B C0 P Q R S0 T0 U0 W0 =
        W0 - (3 / 4 : F) * A * U0 - B * T0 +
          (25 / 32 : F) * (A * A) * S0 - (5 / 4 : F) * C0 * S0 +
          (15 / 8 : F) * A * B * R -
          (105 / 128 : F) * (A * A * A) * Q +
          (35 / 16 : F) * A * C0 * Q + (35 / 32 : F) * (B * B) * Q -
          (45 / 16 : F) * (A * A) * B * P + (5 / 2 : F) * B * C0 * P +
          (1755 / 2048 : F) * L * (A * A * A * A) +
          (975 / 256 : F) * (A * A * A) * B -
          (405 / 128 : F) * L * (A * A) * C0 -
          (405 / 128 : F) * L * A * (B * B) -
          (225 / 32 : F) * A * B * C0 - (75 / 64 : F) * (B * B * B) +
          (45 / 32 : F) * L * (C0 * C0) := by
    simp only [thetaResidual410, alphaResidual410, betaResidual410,
      gammaResidual410, deltaResidual410, epsilonResidual410,
      zetaResidual410, pow_two, pow_three]
    ring
  have hPderiv : d P = (5 / 2 : F) * d A := by linear_combination hP0
  have hQderiv : d Q = (5 / 2 : F) * d B + (9 / 4 : F) * L * d A := by
    linear_combination hQ0
  have hRderiv :
      d R = (5 / 2 : F) * d C0 + (9 / 4 : F) * L * d B +
        (2 : F) * A * d P + (2 : F) * P * d A -
        (25 / 4 : F) * A * d A := by
    linear_combination hR0
  have hSderiv :
      d S0 = (9 / 4 : F) * L * d C0 + (2 : F) * B * d P +
        (2 : F) * P * d B + (7 / 4 : F) * A * d Q +
        (7 / 4 : F) * Q * d A - (45 / 8 : F) * B * d A -
        (45 / 8 : F) * A * d B - (81 / 16 : F) * L * A * d A := by
    linear_combination hS0
  have hTderiv :
      d T0 = (2 : F) * C0 * d P + (2 : F) * P * d C0 +
        (7 / 4 : F) * B * d Q + (7 / 4 : F) * Q * d B +
        (3 / 2 : F) * A * d R + (3 / 2 : F) * R * d A -
        (2 : F) * (A * A) * d P - (4 : F) * P * A * d A -
        (9 / 2 : F) * L * B * d A - (9 / 2 : F) * L * A * d B -
        (5 : F) * C0 * d A - (5 : F) * A * d C0 -
        (5 : F) * B * d B + (15 / 2 : F) * (A * A) * d A := by
    linear_combination hT0
  have hUderiv :
      d U0 = (5 / 4 : F) * S0 * d A + (5 / 4 : F) * A * d S0 +
        (3 / 2 : F) * R * d B + (3 / 2 : F) * B * d R +
        (7 / 4 : F) * Q * d C0 + (7 / 4 : F) * C0 * d Q -
        (7 / 2 : F) * B * P * d A - (7 / 2 : F) * A * P * d B -
        (7 / 2 : F) * A * B * d P - (49 / 16 : F) * A * Q * d A -
        (49 / 32 : F) * (A * A) * d Q -
        (63 / 16 : F) * L * C0 * d A - (63 / 16 : F) * L * A * d C0 -
        (63 / 16 : F) * L * B * d B -
        (35 / 8 : F) * C0 * d B - (35 / 8 : F) * B * d C0 +
        (693 / 128 : F) * L * (A * A) * d A +
        (385 / 32 : F) * A * B * d A +
        (385 / 64 : F) * (A * A) * d B := by
    linear_combination hU0
  have hWderiv :
      d W0 = (5 / 4 : F) * S0 * d C0 + T0 * d B +
        (3 / 4 : F) * U0 * d A - (1 / 4 : F) * B * d T0 -
        (1 / 2 : F) * A * d U0 := by
    linear_combination (-1 / 4 : F) * hrow
  have htarget :
      d W0 - (3 / 4 : F) * U0 * d A - (3 / 4 : F) * A * d U0 -
          T0 * d B - B * d T0 +
          (25 / 32 : F) * S0 * ((2 : F) * A * d A) +
          (25 / 32 : F) * (A * A) * d S0 -
          (5 / 4 : F) * S0 * d C0 - (5 / 4 : F) * C0 * d S0 +
          (15 / 8 : F) * B * R * d A + (15 / 8 : F) * A * R * d B +
          (15 / 8 : F) * A * B * d R -
          (105 / 128 : F) * Q * ((3 : F) * (A * A) * d A) -
          (105 / 128 : F) * (A * A * A) * d Q +
          (35 / 16 : F) * C0 * Q * d A + (35 / 16 : F) * A * Q * d C0 +
          (35 / 16 : F) * A * C0 * d Q +
          (35 / 32 : F) * Q * ((2 : F) * B * d B) +
          (35 / 32 : F) * (B * B) * d Q -
          (45 / 16 : F) * B * P * ((2 : F) * A * d A) -
          (45 / 16 : F) * (A * A) * P * d B -
          (45 / 16 : F) * (A * A) * B * d P +
          (5 / 2 : F) * C0 * P * d B + (5 / 2 : F) * B * P * d C0 +
          (5 / 2 : F) * B * C0 * d P +
          (1755 / 2048 : F) * L * ((4 : F) * (A * A * A) * d A) +
          (975 / 256 : F) * B * ((3 : F) * (A * A) * d A) +
          (975 / 256 : F) * (A * A * A) * d B -
          (405 / 128 : F) * L * C0 * ((2 : F) * A * d A) -
          (405 / 128 : F) * L * (A * A) * d C0 -
          (405 / 128 : F) * L * (B * B) * d A -
          (405 / 128 : F) * L * A * ((2 : F) * B * d B) -
          (225 / 32 : F) * B * C0 * d A -
          (225 / 32 : F) * A * C0 * d B -
          (225 / 32 : F) * A * B * d C0 -
          (75 / 64 : F) * ((3 : F) * (B * B) * d B) +
          (45 / 32 : F) * L * ((2 : F) * C0 * d C0) = 0 := by
    rw [hWderiv, hUderiv, hTderiv, hSderiv, hRderiv, hQderiv, hPderiv]
    ring
  rw [hexp]
  have hcubeB : d (B * B * B) = (3 : F) * (B * B) * d B := by
    simp [Derivation.leibniz]; ring
  simp [map_sub, map_add, Derivation.leibniz, h2, h3, h4, h5, h8, h16,
    h32, h128, h2048, h52, h54, h32div, h74, h34, h72, h92, h158, h1516,
    h2116, h2132, h532, h7128, h45128, h452048, h4532, h516, h258, h2532,
    h3516, h3532, h105128, h4516, h7564, h975256, h17552048, h405128,
    h22532, hL, hsqA, hsqB, hsqC, hcube, hfourth, hcubeB, zero_mul,
    add_zero, mul_zero]
  linear_combination htarget

end DepressedRow410Ninth

/-! ## Next-order eighth-jet parentheticals -/

section NinthFaceScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- Linear combination of the next-order second through sixth defect
cofactors on the eighth-face jet. -/
theorem ninthFace_nextOrderCombo_410
    (t1 m1 s1 v1 w1 b1 lam : F) :
    (128 : F) * t1 ^ 4 *
          ((4 : F) * s1 + (5 : F) * m1 + (9 : F) * lam * t1) +
        (70 : F) * t1 ^ 3 *
          ((16 : F) * v1 - (64 : F) * t1 * s1 -
            (20 : F) * t1 * m1 - (81 : F) * lam * t1 ^ 2) +
        (96 : F) * t1 ^ 2 *
          ((8 : F) * w1 + (128 : F) * s1 * t1 ^ 2 -
            (56 : F) * t1 * v1 + (10 : F) * m1 * t1 ^ 2 +
            (120 : F) * lam * t1 ^ 3) +
        (5 : F) * t1 *
          ((128 : F) * b1 - (2688 : F) * s1 * t1 ^ 3 +
            (1568 : F) * t1 ^ 2 * v1 - (384 : F) * t1 * w1 -
            (40 : F) * m1 * t1 ^ 3 - (2079 : F) * lam * t1 ^ 4) +
        (8 : F) *
          (-(80 : F) * b1 * t1 + (640 : F) * s1 * t1 ^ 4 -
            (448 : F) * t1 ^ 3 * v1 + (144 : F) * t1 ^ 2 * w1 +
            (432 : F) * lam * t1 ^ 5) =
      (63 : F) * lam * t1 ^ 5 := by
  ring

/-- The next-order second through sixth defects force `t₁ = 0` on the
nonzero face `λ ≠ 0`. -/
theorem ninthFace_t1_zero_410 (t1 m1 s1 v1 w1 b1 lam : F)
    (hlambda : lam ≠ 0)
    (hM : (4 : F) * s1 + (5 : F) * m1 + (9 : F) * lam * t1 = 0)
    (hT : (16 : F) * v1 - (64 : F) * t1 * s1 -
      (20 : F) * t1 * m1 - (81 : F) * lam * t1 ^ 2 = 0)
    (hU : (8 : F) * w1 + (128 : F) * s1 * t1 ^ 2 -
      (56 : F) * t1 * v1 + (10 : F) * m1 * t1 ^ 2 +
      (120 : F) * lam * t1 ^ 3 = 0)
    (hV : (128 : F) * b1 - (2688 : F) * s1 * t1 ^ 3 +
      (1568 : F) * t1 ^ 2 * v1 - (384 : F) * t1 * w1 -
      (40 : F) * m1 * t1 ^ 3 - (2079 : F) * lam * t1 ^ 4 = 0)
    (hW : -(80 : F) * b1 * t1 + (640 : F) * s1 * t1 ^ 4 -
      (448 : F) * t1 ^ 3 * v1 + (144 : F) * t1 ^ 2 * w1 +
      (432 : F) * lam * t1 ^ 5 = 0) :
    t1 = 0 := by
  have hcomb :=
    ninthFace_nextOrderCombo_410 t1 m1 s1 v1 w1 b1 lam
  have hzero : (63 : F) * lam * t1 ^ 5 = 0 := by
    rw [← hcomb]
    linear_combination (128 : F) * t1 ^ 4 * hM +
      (70 : F) * t1 ^ 3 * hT + (96 : F) * t1 ^ 2 * hU +
      (5 : F) * t1 * hV + (8 : F) * hW
  have h63 : (63 : F) ≠ 0 := by norm_num
  have hpow : t1 ^ 5 = 0 := by
    have hlam63 : (63 : F) * lam ≠ 0 := mul_ne_zero h63 hlambda
    exact (mul_eq_zero.mp hzero).resolve_left hlam63
  have hlin : t1 * t1 ^ 4 = 0 := by simpa [pow_succ] using hpow
  rcases mul_eq_zero.mp hlin with ht | h4
  · exact ht
  · have hlin2 : t1 * t1 ^ 3 = 0 := by simpa [pow_succ] using h4
    rcases mul_eq_zero.mp hlin2 with ht | h3
    · exact ht
    · have hlin3 : t1 * t1 ^ 2 = 0 := by simpa [pow_succ] using h3
      rcases mul_eq_zero.mp hlin3 with ht | h2
      · exact ht
      · exact (mul_eq_zero.mp (by simpa [pow_two] using h2)).elim id id

/-- After `t₁ = 0`, the next-order second through fifth cofactors force
`4 s₁ + 5 m₁ = 0`, `v₁ = 0`, `w₁ = 0`, and `b₁ = 0`. -/
theorem ninthFace_collapsedNext_410 (m1 s1 v1 w1 b1 : F)
    (hM : (4 : F) * s1 + (5 : F) * m1 = 0)
    (hT : (16 : F) * v1 = 0)
    (hU : (8 : F) * w1 = 0)
    (hV : (128 : F) * b1 = 0) :
    (4 : F) * s1 + (5 : F) * m1 = 0 ∧ v1 = 0 ∧ w1 = 0 ∧ b1 = 0 := by
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  exact ⟨hM, (mul_eq_zero.mp hT).resolve_left h16,
    (mul_eq_zero.mp hU).resolve_left h8,
    (mul_eq_zero.mp hV).resolve_left h128⟩

theorem ninthJet_secondLeading_410
    (t1 a2 s2 m1 s1 h : F[X])
    (hs : (2 : F[X]) * s2 - (5 : F[X]) * t1 ^ 2 = h * s1)
    (hm : t1 ^ 2 - (4 : F[X]) * a2 = h * m1) :
    (8 : F[X]) * s2 - (20 : F[X]) * a2 - (15 : F[X]) * t1 ^ 2 =
      h * ((4 : F[X]) * s1 + (5 : F[X]) * m1) := by
  linear_combination (4 : F[X]) * hs + (5 : F[X]) * hm

theorem ninthJet_thirdLeading_410
    (t1 a2 s2 v3 m1 s1 v1 h : F[X])
    (hs : (2 : F[X]) * s2 - (5 : F[X]) * t1 ^ 2 = h * s1)
    (hv : (4 : F[X]) * v3 - (5 : F[X]) * t1 ^ 3 = h * v1)
    (hm : t1 ^ 2 - (4 : F[X]) * a2 = h * m1) :
    (64 : F[X]) * v3 - (128 : F[X]) * s2 * t1 +
        (220 : F[X]) * t1 ^ 3 + (80 : F[X]) * a2 * t1 =
      h * ((16 : F[X]) * v1 - (64 : F[X]) * t1 * s1 -
        (20 : F[X]) * t1 * m1) := by
  linear_combination (16 : F[X]) * hv - (64 : F[X]) * t1 * hs -
    (20 : F[X]) * t1 * hm

theorem ninthJet_fourthId_410 (t1 a2 s2 v3 w7 : F[X]) :
    (128 : F[X]) * w7 - (224 : F[X]) * t1 * v3 +
        (320 : F[X]) * s2 * t1 ^ 2 - (525 : F[X]) * t1 ^ 4 -
      (256 : F[X]) * a2 * s2 + (400 : F[X]) * a2 * t1 ^ 2 +
      (400 : F[X]) * a2 ^ 2 =
      (8 : F[X]) * ((16 : F[X]) * w7 - (5 : F[X]) * t1 ^ 4) +
        (128 : F[X]) * t1 ^ 2 *
            ((2 : F[X]) * s2 - (5 : F[X]) * t1 ^ 2) -
          (56 : F[X]) * t1 * ((4 : F[X]) * v3 - (5 : F[X]) * t1 ^ 3) +
        (10 : F[X]) * t1 ^ 2 * (t1 ^ 2 - (4 : F[X]) * a2) +
          (32 : F[X]) * ((2 : F[X]) * s2 - (5 : F[X]) * t1 ^ 2) *
            (t1 ^ 2 - (4 : F[X]) * a2) +
        (25 : F[X]) * (t1 ^ 2 - (4 : F[X]) * a2) ^ 2 := by
  ring

theorem ninthJet_fifthId_410 (t1 a2 s2 v3 w7 b5 : F[X]) :
    (4096 : F[X]) * b5 - (11520 : F[X]) * a2 ^ 2 * t1 +
        (18432 : F[X]) * a2 * s2 * t1 - (31200 : F[X]) * a2 * t1 ^ 3 -
      (7168 : F[X]) * a2 * v3 - (9984 : F[X]) * s2 * t1 ^ 3 +
        (15912 : F[X]) * t1 ^ 5 + (8064 : F[X]) * t1 ^ 2 * v3 -
      (6144 : F[X]) * t1 * w7 =
      (128 : F[X]) * ((32 : F[X]) * b5 - t1 ^ 5) -
        (2688 : F[X]) * t1 ^ 3 *
            ((2 : F[X]) * s2 - (5 : F[X]) * t1 ^ 2) +
        (1568 : F[X]) * t1 ^ 2 *
            ((4 : F[X]) * v3 - (5 : F[X]) * t1 ^ 3) -
        (384 : F[X]) * t1 * ((16 : F[X]) * w7 - (5 : F[X]) * t1 ^ 4) -
        (40 : F[X]) * t1 ^ 3 * (t1 ^ 2 - (4 : F[X]) * a2) -
        (2304 : F[X]) * ((2 : F[X]) * s2 - (5 : F[X]) * t1 ^ 2) *
            (t1 ^ 2 - (4 : F[X]) * a2) * t1 +
        (448 : F[X]) * ((4 : F[X]) * v3 - (5 : F[X]) * t1 ^ 3) *
            (t1 ^ 2 - (4 : F[X]) * a2) -
        (720 : F[X]) * (t1 ^ 2 - (4 : F[X]) * a2) ^ 2 * t1 := by
  ring

set_option maxHeartbeats 4000000 in
theorem ninthJet_sixthId_410 (t1 a2 s2 v3 w7 b5 : F[X]) :
    -(5120 : F[X]) * a2 ^ 3 + (4096 : F[X]) * a2 ^ 2 * s2 -
        (3840 : F[X]) * a2 ^ 2 * t1 ^ 2 -
      (12288 : F[X]) * a2 * s2 * t1 ^ 2 +
        (20480 : F[X]) * a2 * t1 ^ 4 + (7168 : F[X]) * a2 * t1 * v3 -
      (3072 : F[X]) * a2 * w7 - (2560 : F[X]) * b5 * t1 +
        (4096 : F[X]) * s2 * t1 ^ 4 - (6400 : F[X]) * t1 ^ 6 -
      (3584 : F[X]) * t1 ^ 3 * v3 + (3072 : F[X]) * t1 ^ 2 * w7 =
      (640 : F[X]) * t1 ^ 4 *
            ((2 : F[X]) * s2 - (5 : F[X]) * t1 ^ 2) -
        (448 : F[X]) * t1 ^ 3 *
            ((4 : F[X]) * v3 - (5 : F[X]) * t1 ^ 3) -
        (80 : F[X]) * t1 * ((32 : F[X]) * b5 - t1 ^ 5) +
        (144 : F[X]) * t1 ^ 2 *
            ((16 : F[X]) * w7 - (5 : F[X]) * t1 ^ 4) +
        (128 : F[X]) * ((2 : F[X]) * s2 - (5 : F[X]) * t1 ^ 2) *
            (t1 ^ 2 - (4 : F[X]) * a2) ^ 2 +
        (1280 : F[X]) * ((2 : F[X]) * s2 - (5 : F[X]) * t1 ^ 2) *
            (t1 ^ 2 - (4 : F[X]) * a2) * t1 ^ 2 -
        (448 : F[X]) * ((4 : F[X]) * v3 - (5 : F[X]) * t1 ^ 3) *
            (t1 ^ 2 - (4 : F[X]) * a2) * t1 +
        (48 : F[X]) * ((16 : F[X]) * w7 - (5 : F[X]) * t1 ^ 4) *
            (t1 ^ 2 - (4 : F[X]) * a2) +
        (80 : F[X]) * (t1 ^ 2 - (4 : F[X]) * a2) ^ 3 +
        (160 : F[X]) * (t1 ^ 2 - (4 : F[X]) * a2) ^ 2 * t1 ^ 2 := by
  ring

theorem ninthJet_sixthFactor_410
    (h t1 s1 v1 w1 b1 m1 : F[X]) :
    (640 : F[X]) * t1 ^ 4 * (h * s1) -
        (448 : F[X]) * t1 ^ 3 * (h * v1) -
      (80 : F[X]) * t1 * (h * b1) + (144 : F[X]) * t1 ^ 2 * (h * w1) +
        (128 : F[X]) * (h * s1) * (h * m1) ^ 2 +
      (1280 : F[X]) * (h * s1) * (h * m1) * t1 ^ 2 -
        (448 : F[X]) * (h * v1) * (h * m1) * t1 +
      (48 : F[X]) * (h * w1) * (h * m1) + (80 : F[X]) * (h * m1) ^ 3 +
        (160 : F[X]) * (h * m1) ^ 2 * t1 ^ 2 =
      h * ((640 : F[X]) * t1 ^ 4 * s1 - (448 : F[X]) * t1 ^ 3 * v1 -
          (80 : F[X]) * t1 * b1 + (144 : F[X]) * t1 ^ 2 * w1 +
        h * ((1280 : F[X]) * s1 * m1 * t1 ^ 2 -
            (448 : F[X]) * v1 * m1 * t1 + (48 : F[X]) * w1 * m1 +
          (160 : F[X]) * m1 ^ 2 * t1 ^ 2 +
            h * ((128 : F[X]) * s1 * m1 ^ 2 +
              (80 : F[X]) * m1 ^ 3))) := by
  ring

theorem ninthFace_lambdaThird_410 (t1 a2 lam : F)
    (hm : t1 ^ 2 - (4 : F) * a2 = 0) :
    (72 : F) * lam * a2 - (99 : F) * lam * t1 ^ 2 =
      -(81 : F) * lam * t1 ^ 2 := by
  linear_combination -(18 : F) * lam * hm

theorem ninthFace_lambdaFourth_410 (t1 a2 lam : F)
    (hm : t1 ^ 2 - (4 : F) * a2 = 0) :
    (210 : F) * lam * t1 ^ 3 - (360 : F) * lam * a2 * t1 =
      (120 : F) * lam * t1 ^ 3 := by
  linear_combination (90 : F) * lam * t1 * hm

theorem ninthFace_lambdaFifth_410 (t1 a2 lam : F)
    (hm : t1 ^ 2 - (4 : F) * a2 = 0) :
    (16848 : F) * lam * a2 * t1 ^ 2 - (5184 : F) * lam * a2 ^ 2 -
        (5967 : F) * lam * t1 ^ 4 =
      -(2079 : F) * lam * t1 ^ 4 := by
  linear_combination
    ((1296 : F) * lam * a2 - (3888 : F) * lam * t1 ^ 2) * hm

theorem ninthFace_lambdaSixth_410 (t1 a2 lam : F)
    (hm : t1 ^ 2 - (4 : F) * a2 = 0) :
    (6912 : F) * lam * a2 ^ 2 * t1 - (9216 : F) * lam * a2 * t1 ^ 3 +
        (2304 : F) * lam * t1 ^ 5 =
      (432 : F) * lam * t1 ^ 5 := by
  linear_combination
    ((-(1728 : F) * lam * a2 * t1) + (1872 : F) * lam * t1 ^ 3) * hm

end NinthFaceScalars410

/-! ## Source-facing ninth-face packet -/

section NonzeroNinthFace410

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000 in
/-- Finite local ninth-face packet: the eighth-face one-parameter jet
collapses at the root of `h`. -/
theorem nonzeroFace410_linearRoot_ninthInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hlambda : lambda ≠ 0) :
    ∃ t1 s2 v3 w7 m1 s1 v1 w1 b1 : k[X],
      p.coeff 3 = h0 ^ 2 * t1 ∧ q.coeff 8 = h0 ^ 6 * s2 ∧
        q.coeff 7 = h0 ^ 4 * v3 ∧ q.coeff 6 = h0 ^ 2 * w7 ∧
        (2 : k[X]) * s2 - (5 : k[X]) * t1 ^ 2 = h0 * s1 ∧
        (4 : k[X]) * v3 - (5 : k[X]) * t1 ^ 3 = h0 * v1 ∧
        (16 : k[X]) * w7 - (5 : k[X]) * t1 ^ 4 = h0 * w1 ∧
        (32 : k[X]) * q.coeff 5 - t1 ^ 5 = h0 * b1 ∧
        t1 ^ 2 - (4 : k[X]) * p.coeff 2 = h0 * m1 ∧
        t1.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
        (q.coeff 5).eval a = 0 ∧ s2.eval a = 0 ∧ v3.eval a = 0 ∧
        w7.eval a = 0 ∧
        (4 : k) * s1.eval a + (5 : k) * m1.eval a = 0 ∧
        v1.eval a = 0 ∧ w1.eval a = 0 ∧ b1.eval a = 0 ∧
        h0 ^ 3 ∣ p.coeff 3 ∧ h0 ∣ p.coeff 2 ∧
        h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 7 ∧
        h0 ^ 4 ∣ q.coeff 6 ∧ h0 ^ 2 ∣ q.coeff 5 ∧
        h0 ^ 8 ∣ q.coeff 9 := by
  obtain ⟨alpha, hMrel⟩ :=
    nonzeroFace410_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨gamma, hTrel⟩ :=
    nonzeroFace410_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨delta, hUrel⟩ :=
    nonzeroFace410_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨eps, hVrel⟩ :=
    nonzeroFace410_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨zeta, hWrel⟩ :=
    nonzeroFace410_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨_hp3, _hq8, _hq7, _hq6, hq9, _hmix5, _hmix6, _hY, hjet⟩ :=
    nonzeroFace410_linearRoot_eighthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4 hq10 hN hD hroot
  obtain ⟨t1, s2, v3, w7, ht1, hs2, hv3, hw7, hsroot, hvroot, hwroot,
    hbroot, hmixroot, _hcompat⟩ := hjet
  have hs_eval :
      ((2 : k[X]) * s2 - (5 : k[X]) * t1 ^ 2).eval a = 0 := by
    simpa [eval_sub, eval_mul, eval_pow] using hsroot
  have hv_eval :
      ((4 : k[X]) * v3 - (5 : k[X]) * t1 ^ 3).eval a = 0 := by
    simpa [eval_sub, eval_mul, eval_pow] using hvroot
  have hw_eval :
      ((16 : k[X]) * w7 - (5 : k[X]) * t1 ^ 4).eval a = 0 := by
    simpa [eval_sub, eval_mul, eval_pow] using hwroot
  have hb_eval :
      ((32 : k[X]) * q.coeff 5 - t1 ^ 5).eval a = 0 := by
    simpa [eval_sub, eval_mul, eval_pow] using hbroot
  have hm_eval :
      (t1 ^ 2 - (4 : k[X]) * p.coeff 2).eval a = 0 := by
    simpa [eval_sub, eval_mul, eval_pow] using hmixroot
  obtain ⟨s1, hs1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0
      ((2 : k[X]) * s2 - (5 : k[X]) * t1 ^ 2) a hh0degree hroot hs_eval
  obtain ⟨v1, hv1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0
      ((4 : k[X]) * v3 - (5 : k[X]) * t1 ^ 3) a hh0degree hroot hv_eval
  obtain ⟨w1, hw1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0
      ((16 : k[X]) * w7 - (5 : k[X]) * t1 ^ 4) a hh0degree hroot hw_eval
  obtain ⟨b1, hb1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0
      ((32 : k[X]) * q.coeff 5 - t1 ^ 5) a hh0degree hroot hb_eval
  obtain ⟨m1, hm1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0
      (t1 ^ 2 - (4 : k[X]) * p.coeff 2) a hh0degree hroot hm_eval
  have hM0 :
      (8 : k[X]) * s2 - (20 : k[X]) * p.coeff 2 -
          (15 : k[X]) * t1 ^ 2 +
        (9 : k[X]) * Polynomial.C lambda * t1 * h0 =
        Polynomial.C alpha * h0 ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hh0)
    calc
      h0 ^ 6 *
            ((8 : k[X]) * s2 - (20 : k[X]) * p.coeff 2 -
                (15 : k[X]) * t1 ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * t1 * h0) =
          localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect410, ht1, hs2]
        ring
      _ = Polynomial.C alpha * h0 ^ 8 := hMrel
      _ = h0 ^ 6 * (Polynomial.C alpha * h0 ^ 2) := by ring
  have hT0 :
      (64 : k[X]) * v3 - (128 : k[X]) * s2 * t1 +
          (220 : k[X]) * t1 ^ 3 + (80 : k[X]) * p.coeff 2 * t1 +
        (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 -
          (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 -
        (160 : k[X]) * p.coeff 1 * h0 ^ 2 =
        Polynomial.C gamma * h0 ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 8 hh0)
    calc
      h0 ^ 8 *
            ((64 : k[X]) * v3 - (128 : k[X]) * s2 * t1 +
                (220 : k[X]) * t1 ^ 3 +
              (80 : k[X]) * p.coeff 2 * t1 +
                (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 -
              (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 -
                (160 : k[X]) * p.coeff 1 * h0 ^ 2) =
          localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect410, ht1, hs2, hv3]
        ring
      _ = Polynomial.C gamma * h0 ^ 11 := hTrel
      _ = h0 ^ 8 * (Polynomial.C gamma * h0 ^ 3) := by ring
  have hU0 :
      (128 : k[X]) * w7 - (224 : k[X]) * t1 * v3 +
          (320 : k[X]) * s2 * t1 ^ 2 - (525 : k[X]) * t1 ^ 4 -
        (256 : k[X]) * p.coeff 2 * s2 +
          (400 : k[X]) * p.coeff 2 * t1 ^ 2 +
        (400 : k[X]) * p.coeff 2 ^ 2 +
          (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 -
        (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 * h0 +
          (80 : k[X]) * p.coeff 1 * t1 * h0 ^ 2 +
        (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 3 -
          (320 : k[X]) * p.coeff 0 * h0 ^ 4 =
        Polynomial.C delta * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 10 hh0)
    calc
      h0 ^ 10 *
            ((128 : k[X]) * w7 - (224 : k[X]) * t1 * v3 +
                (320 : k[X]) * s2 * t1 ^ 2 - (525 : k[X]) * t1 ^ 4 -
              (256 : k[X]) * p.coeff 2 * s2 +
                (400 : k[X]) * p.coeff 2 * t1 ^ 2 +
              (400 : k[X]) * p.coeff 2 ^ 2 +
                (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 -
              (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 *
                  h0 +
                (80 : k[X]) * p.coeff 1 * t1 * h0 ^ 2 +
              (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 3 -
                (320 : k[X]) * p.coeff 0 * h0 ^ 4) =
          localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect410, ht1, hs2, hv3, hw7]
        ring
      _ = Polynomial.C delta * h0 ^ 14 := hUrel
      _ = h0 ^ 10 * (Polynomial.C delta * h0 ^ 4) := by ring
  have hV0 :
      (4096 : k[X]) * q.coeff 5 - (11520 : k[X]) * p.coeff 2 ^ 2 * t1 +
          (18432 : k[X]) * p.coeff 2 * s2 * t1 -
        (31200 : k[X]) * p.coeff 2 * t1 ^ 3 -
          (7168 : k[X]) * p.coeff 2 * v3 -
        (9984 : k[X]) * s2 * t1 ^ 3 + (15912 : k[X]) * t1 ^ 5 +
          (8064 : k[X]) * t1 ^ 2 * v3 - (6144 : k[X]) * t1 * w7 +
        (16848 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 ^ 2 *
            h0 -
          (5184 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 * h0 -
        (5967 : k[X]) * Polynomial.C lambda * t1 ^ 4 * h0 +
          (23040 : k[X]) * p.coeff 1 * p.coeff 2 * h0 ^ 2 +
        (14400 : k[X]) * p.coeff 1 * t1 ^ 2 * h0 ^ 2 -
          (8192 : k[X]) * p.coeff 1 * s2 * h0 ^ 2 -
        (10368 : k[X]) * Polynomial.C lambda * p.coeff 1 * t1 * h0 ^ 3 +
          (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 * h0 ^ 5 =
        Polynomial.C eps * h0 ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 12 hh0)
    calc
      h0 ^ 12 *
            ((4096 : k[X]) * q.coeff 5 -
                (11520 : k[X]) * p.coeff 2 ^ 2 * t1 +
              (18432 : k[X]) * p.coeff 2 * s2 * t1 -
                (31200 : k[X]) * p.coeff 2 * t1 ^ 3 -
              (7168 : k[X]) * p.coeff 2 * v3 -
                (9984 : k[X]) * s2 * t1 ^ 3 +
              (15912 : k[X]) * t1 ^ 5 +
                (8064 : k[X]) * t1 ^ 2 * v3 -
              (6144 : k[X]) * t1 * w7 +
                (16848 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                    t1 ^ 2 * h0 -
              (5184 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 *
                  h0 -
                (5967 : k[X]) * Polynomial.C lambda * t1 ^ 4 * h0 +
              (23040 : k[X]) * p.coeff 1 * p.coeff 2 * h0 ^ 2 +
                (14400 : k[X]) * p.coeff 1 * t1 ^ 2 * h0 ^ 2 -
              (8192 : k[X]) * p.coeff 1 * s2 * h0 ^ 2 -
                (10368 : k[X]) * Polynomial.C lambda * p.coeff 1 * t1 *
                    h0 ^ 3 +
              (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 *
                  h0 ^ 5) =
          localClearedFifthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) lambda := by
        simp only [localClearedFifthDefect410, ht1, hs2, hv3, hw7]
        ring
      _ = Polynomial.C eps * h0 ^ 17 := hVrel
      _ = h0 ^ 12 * (Polynomial.C eps * h0 ^ 5) := by ring
  have hW0 :
      -(5120 : k[X]) * p.coeff 2 ^ 3 +
          (4096 : k[X]) * p.coeff 2 ^ 2 * s2 -
        (3840 : k[X]) * p.coeff 2 ^ 2 * t1 ^ 2 -
          (12288 : k[X]) * p.coeff 2 * s2 * t1 ^ 2 +
        (20480 : k[X]) * p.coeff 2 * t1 ^ 4 +
          (7168 : k[X]) * p.coeff 2 * t1 * v3 -
        (3072 : k[X]) * p.coeff 2 * w7 -
          (2560 : k[X]) * q.coeff 5 * t1 +
        (4096 : k[X]) * s2 * t1 ^ 4 - (6400 : k[X]) * t1 ^ 6 -
          (3584 : k[X]) * t1 ^ 3 * v3 +
        (3072 : k[X]) * t1 ^ 2 * w7 +
          (6912 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 * t1 *
            h0 -
        (9216 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 ^ 3 *
            h0 +
          (2304 : k[X]) * Polynomial.C lambda * t1 ^ 5 * h0 -
        (7680 : k[X]) * p.coeff 1 * p.coeff 2 * t1 * h0 ^ 2 +
          (8192 : k[X]) * p.coeff 1 * s2 * t1 * h0 ^ 2 -
        (14080 : k[X]) * p.coeff 1 * t1 ^ 3 * h0 ^ 2 -
          (3584 : k[X]) * p.coeff 1 * v3 * h0 ^ 2 +
        (2048 : k[X]) * q.coeff 4 * h0 ^ 2 -
          (4608 : k[X]) * Polynomial.C lambda * p.coeff 1 * p.coeff 2 *
            h0 ^ 3 +
        (6912 : k[X]) * Polynomial.C lambda * p.coeff 1 * t1 ^ 2 *
            h0 ^ 3 +
          (10240 : k[X]) * p.coeff 0 * p.coeff 2 * h0 ^ 4 -
        (4096 : k[X]) * p.coeff 0 * s2 * h0 ^ 4 +
          (7680 : k[X]) * p.coeff 0 * t1 ^ 2 * h0 ^ 4 +
        (5120 : k[X]) * p.coeff 1 ^ 2 * h0 ^ 4 -
          (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 * t1 *
            h0 ^ 5 =
        Polynomial.C zeta * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 14 hh0)
    calc
      h0 ^ 14 *
            (-(5120 : k[X]) * p.coeff 2 ^ 3 +
                (4096 : k[X]) * p.coeff 2 ^ 2 * s2 -
              (3840 : k[X]) * p.coeff 2 ^ 2 * t1 ^ 2 -
                (12288 : k[X]) * p.coeff 2 * s2 * t1 ^ 2 +
              (20480 : k[X]) * p.coeff 2 * t1 ^ 4 +
                (7168 : k[X]) * p.coeff 2 * t1 * v3 -
              (3072 : k[X]) * p.coeff 2 * w7 -
                (2560 : k[X]) * q.coeff 5 * t1 +
              (4096 : k[X]) * s2 * t1 ^ 4 - (6400 : k[X]) * t1 ^ 6 -
                (3584 : k[X]) * t1 ^ 3 * v3 +
              (3072 : k[X]) * t1 ^ 2 * w7 +
                (6912 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 *
                    t1 * h0 -
              (9216 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                    t1 ^ 3 * h0 +
                (2304 : k[X]) * Polynomial.C lambda * t1 ^ 5 * h0 -
              (7680 : k[X]) * p.coeff 1 * p.coeff 2 * t1 * h0 ^ 2 +
                (8192 : k[X]) * p.coeff 1 * s2 * t1 * h0 ^ 2 -
              (14080 : k[X]) * p.coeff 1 * t1 ^ 3 * h0 ^ 2 -
                (3584 : k[X]) * p.coeff 1 * v3 * h0 ^ 2 +
              (2048 : k[X]) * q.coeff 4 * h0 ^ 2 -
                (4608 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                    p.coeff 2 * h0 ^ 3 +
              (6912 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                    t1 ^ 2 * h0 ^ 3 +
                (10240 : k[X]) * p.coeff 0 * p.coeff 2 * h0 ^ 4 -
              (4096 : k[X]) * p.coeff 0 * s2 * h0 ^ 4 +
                (7680 : k[X]) * p.coeff 0 * t1 ^ 2 * h0 ^ 4 +
              (5120 : k[X]) * p.coeff 1 ^ 2 * h0 ^ 4 -
                (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 * t1 *
                    h0 ^ 5) =
          localClearedSixthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda := by
        have hred :=
          sixthDefect_onFourthJet_410 h0 t1 (p.coeff 2) (p.coeff 1)
            (p.coeff 0) s2 v3 w7 (q.coeff 5) (q.coeff 4) lambda
        rw [← ht1, ← hs2, ← hv3, ← hw7] at hred
        exact hred.symm
      _ = Polynomial.C zeta * h0 ^ 20 := hWrel
      _ = h0 ^ 14 * (Polynomial.C zeta * h0 ^ 6) := by ring
  have hMlead :=
    ninthJet_secondLeading_410 t1 (p.coeff 2) s2 m1 s1 h0 hs1 hm1
  have hTlead :=
    ninthJet_thirdLeading_410 t1 (p.coeff 2) s2 v3 m1 s1 v1 h0 hs1 hv1
      hm1
  have hMcof :
      (4 : k[X]) * s1 + (5 : k[X]) * m1 +
          (9 : k[X]) * Polynomial.C lambda * t1 =
        Polynomial.C alpha * h0 := by
    apply mul_left_cancel₀ hh0
    have hsplit :
        h0 * ((4 : k[X]) * s1 + (5 : k[X]) * m1 +
              (9 : k[X]) * Polynomial.C lambda * t1) =
          h0 * ((4 : k[X]) * s1 + (5 : k[X]) * m1) +
            (9 : k[X]) * Polynomial.C lambda * t1 * h0 := by
      ring
    calc
      h0 * ((4 : k[X]) * s1 + (5 : k[X]) * m1 +
              (9 : k[X]) * Polynomial.C lambda * t1) =
          (8 : k[X]) * s2 - (20 : k[X]) * p.coeff 2 -
              (15 : k[X]) * t1 ^ 2 +
            (9 : k[X]) * Polynomial.C lambda * t1 * h0 := by
        rw [hsplit, ← hMlead]
      _ = Polynomial.C alpha * h0 ^ 2 := hM0
      _ = h0 * (Polynomial.C alpha * h0) := by ring
  have hTcof :
      (16 : k[X]) * v1 - (64 : k[X]) * t1 * s1 -
          (20 : k[X]) * t1 * m1 +
        (72 : k[X]) * Polynomial.C lambda * p.coeff 2 -
          (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 -
        (160 : k[X]) * p.coeff 1 * h0 =
        Polynomial.C gamma * h0 ^ 2 := by
    apply mul_left_cancel₀ hh0
    have hsplit :
        h0 * ((16 : k[X]) * v1 - (64 : k[X]) * t1 * s1 -
              (20 : k[X]) * t1 * m1 +
            (72 : k[X]) * Polynomial.C lambda * p.coeff 2 -
              (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 -
            (160 : k[X]) * p.coeff 1 * h0) =
          h0 * ((16 : k[X]) * v1 - (64 : k[X]) * t1 * s1 -
              (20 : k[X]) * t1 * m1) +
            (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 -
            (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 -
            (160 : k[X]) * p.coeff 1 * h0 ^ 2 := by
      ring
    calc
      h0 * ((16 : k[X]) * v1 - (64 : k[X]) * t1 * s1 -
              (20 : k[X]) * t1 * m1 +
            (72 : k[X]) * Polynomial.C lambda * p.coeff 2 -
              (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 -
            (160 : k[X]) * p.coeff 1 * h0) =
          (64 : k[X]) * v3 - (128 : k[X]) * s2 * t1 +
              (220 : k[X]) * t1 ^ 3 + (80 : k[X]) * p.coeff 2 * t1 +
            (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 -
              (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 -
            (160 : k[X]) * p.coeff 1 * h0 ^ 2 := by
        rw [hsplit, ← hTlead]
      _ = Polynomial.C gamma * h0 ^ 3 := hT0
      _ = h0 * (Polynomial.C gamma * h0 ^ 2) := by ring
  have hM1 :
      (4 : k) * s1.eval a + (5 : k) * m1.eval a +
          (9 : k) * lambda * t1.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hMcof
    simpa [hroot] using heval
  have hT1 :
      (16 : k) * v1.eval a - (64 : k) * t1.eval a * s1.eval a -
          (20 : k) * t1.eval a * m1.eval a +
        (72 : k) * lambda * (p.coeff 2).eval a -
          (99 : k) * lambda * (t1.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hTcof
    simpa [hroot] using heval
  have hT1' :
      (16 : k) * v1.eval a - (64 : k) * t1.eval a * s1.eval a -
          (20 : k) * t1.eval a * m1.eval a -
        (81 : k) * lambda * (t1.eval a) ^ 2 = 0 := by
    have h72 :=
      ninthFace_lambdaThird_410 (t1.eval a) ((p.coeff 2).eval a)
        lambda hmixroot
    linear_combination hT1 - h72
  have hU1 :
      (8 : k) * w1.eval a + (128 : k) * s1.eval a * (t1.eval a) ^ 2 -
          (56 : k) * t1.eval a * v1.eval a +
        (10 : k) * m1.eval a * (t1.eval a) ^ 2 +
        (120 : k) * lambda * (t1.eval a) ^ 3 = 0 := by
    have hUid := ninthJet_fourthId_410 t1 (p.coeff 2) s2 v3 w7
    have hUsub :
        (128 : k[X]) * w7 - (224 : k[X]) * t1 * v3 +
            (320 : k[X]) * s2 * t1 ^ 2 - (525 : k[X]) * t1 ^ 4 -
          (256 : k[X]) * p.coeff 2 * s2 +
            (400 : k[X]) * p.coeff 2 * t1 ^ 2 +
          (400 : k[X]) * p.coeff 2 ^ 2 =
          (8 : k[X]) * (h0 * w1) +
            (128 : k[X]) * t1 ^ 2 * (h0 * s1) -
          (56 : k[X]) * t1 * (h0 * v1) +
            (10 : k[X]) * t1 ^ 2 * (h0 * m1) +
          (32 : k[X]) * (h0 * s1) * (h0 * m1) +
            (25 : k[X]) * (h0 * m1) ^ 2 := by
      simpa [hs1, hv1, hw1, hm1] using hUid
    have hUsplit :
        h0 * ((8 : k[X]) * w1 + (128 : k[X]) * t1 ^ 2 * s1 -
              (56 : k[X]) * t1 * v1 + (10 : k[X]) * t1 ^ 2 * m1 +
            (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 -
              (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 +
            h0 * ((32 : k[X]) * s1 * m1 + (25 : k[X]) * m1 ^ 2 +
                (80 : k[X]) * p.coeff 1 * t1 +
                (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 -
                (320 : k[X]) * p.coeff 0 * h0 ^ 2)) =
          (128 : k[X]) * w7 - (224 : k[X]) * t1 * v3 +
              (320 : k[X]) * s2 * t1 ^ 2 - (525 : k[X]) * t1 ^ 4 -
            (256 : k[X]) * p.coeff 2 * s2 +
              (400 : k[X]) * p.coeff 2 * t1 ^ 2 +
            (400 : k[X]) * p.coeff 2 ^ 2 +
              (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 -
            (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 * h0 +
              (80 : k[X]) * p.coeff 1 * t1 * h0 ^ 2 +
            (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 3 -
              (320 : k[X]) * p.coeff 0 * h0 ^ 4 := by
      rw [hUsub]; ring
    have hUcof :
        (8 : k[X]) * w1 + (128 : k[X]) * t1 ^ 2 * s1 -
            (56 : k[X]) * t1 * v1 + (10 : k[X]) * t1 ^ 2 * m1 +
          (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 -
            (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 +
          h0 * ((32 : k[X]) * s1 * m1 + (25 : k[X]) * m1 ^ 2 +
              (80 : k[X]) * p.coeff 1 * t1 +
              (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 -
              (320 : k[X]) * p.coeff 0 * h0 ^ 2) =
          Polynomial.C delta * h0 ^ 3 := by
      apply mul_left_cancel₀ hh0
      calc
        h0 * ((8 : k[X]) * w1 + (128 : k[X]) * t1 ^ 2 * s1 -
                (56 : k[X]) * t1 * v1 + (10 : k[X]) * t1 ^ 2 * m1 +
              (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 -
                (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 +
              h0 * ((32 : k[X]) * s1 * m1 + (25 : k[X]) * m1 ^ 2 +
                  (80 : k[X]) * p.coeff 1 * t1 +
                  (144 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                    h0 -
                  (320 : k[X]) * p.coeff 0 * h0 ^ 2)) =
            Polynomial.C delta * h0 ^ 4 := hUsplit.trans hU0
        _ = h0 * (Polynomial.C delta * h0 ^ 3) := by ring
    have heval := congrArg (fun r : k[X] => r.eval a) hUcof
    have hraw :
        (8 : k) * w1.eval a +
            (128 : k) * (t1.eval a) ^ 2 * s1.eval a -
          (56 : k) * t1.eval a * v1.eval a +
            (10 : k) * (t1.eval a) ^ 2 * m1.eval a +
          (210 : k) * lambda * (t1.eval a) ^ 3 -
            (360 : k) * lambda * (p.coeff 2).eval a * t1.eval a = 0 := by
      simpa [hroot] using heval
    have hlam :=
      ninthFace_lambdaFourth_410 (t1.eval a) ((p.coeff 2).eval a)
        lambda hmixroot
    linear_combination hraw - hlam
  have hV1 :
      (128 : k) * b1.eval a - (2688 : k) * s1.eval a *
          (t1.eval a) ^ 3 +
        (1568 : k) * (t1.eval a) ^ 2 * v1.eval a -
          (384 : k) * t1.eval a * w1.eval a -
        (40 : k) * m1.eval a * (t1.eval a) ^ 3 -
          (2079 : k) * lambda * (t1.eval a) ^ 4 = 0 := by
    have hVid := ninthJet_fifthId_410 t1 (p.coeff 2) s2 v3 w7 (q.coeff 5)
    have hVsub :
        (4096 : k[X]) * q.coeff 5 - (11520 : k[X]) * p.coeff 2 ^ 2 * t1 +
            (18432 : k[X]) * p.coeff 2 * s2 * t1 -
          (31200 : k[X]) * p.coeff 2 * t1 ^ 3 -
            (7168 : k[X]) * p.coeff 2 * v3 -
          (9984 : k[X]) * s2 * t1 ^ 3 + (15912 : k[X]) * t1 ^ 5 +
            (8064 : k[X]) * t1 ^ 2 * v3 - (6144 : k[X]) * t1 * w7 =
          (128 : k[X]) * (h0 * b1) -
            (2688 : k[X]) * t1 ^ 3 * (h0 * s1) +
          (1568 : k[X]) * t1 ^ 2 * (h0 * v1) -
            (384 : k[X]) * t1 * (h0 * w1) -
          (40 : k[X]) * t1 ^ 3 * (h0 * m1) -
            (2304 : k[X]) * (h0 * s1) * (h0 * m1) * t1 +
          (448 : k[X]) * (h0 * v1) * (h0 * m1) -
            (720 : k[X]) * (h0 * m1) ^ 2 * t1 := by
      simpa [hs1, hv1, hw1, hb1, hm1] using hVid
    have hVsplit :
        h0 * ((128 : k[X]) * b1 - (2688 : k[X]) * t1 ^ 3 * s1 +
              (1568 : k[X]) * t1 ^ 2 * v1 - (384 : k[X]) * t1 * w1 -
            (40 : k[X]) * t1 ^ 3 * m1 +
              (16848 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                t1 ^ 2 -
            (5184 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 -
              (5967 : k[X]) * Polynomial.C lambda * t1 ^ 4 +
            h0 * (-(2304 : k[X]) * s1 * m1 * t1 +
                (448 : k[X]) * v1 * m1 -
                (720 : k[X]) * m1 ^ 2 * t1 +
                (23040 : k[X]) * p.coeff 1 * p.coeff 2 +
                (14400 : k[X]) * p.coeff 1 * t1 ^ 2 -
                (8192 : k[X]) * p.coeff 1 * s2 -
                (10368 : k[X]) * Polynomial.C lambda * p.coeff 1 * t1 *
                  h0 +
                (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 *
                  h0 ^ 3)) =
          (4096 : k[X]) * q.coeff 5 - (11520 : k[X]) * p.coeff 2 ^ 2 * t1 +
              (18432 : k[X]) * p.coeff 2 * s2 * t1 -
            (31200 : k[X]) * p.coeff 2 * t1 ^ 3 -
              (7168 : k[X]) * p.coeff 2 * v3 -
            (9984 : k[X]) * s2 * t1 ^ 3 + (15912 : k[X]) * t1 ^ 5 +
              (8064 : k[X]) * t1 ^ 2 * v3 - (6144 : k[X]) * t1 * w7 +
            (16848 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 ^ 2 *
                h0 -
              (5184 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 * h0 -
            (5967 : k[X]) * Polynomial.C lambda * t1 ^ 4 * h0 +
              (23040 : k[X]) * p.coeff 1 * p.coeff 2 * h0 ^ 2 +
            (14400 : k[X]) * p.coeff 1 * t1 ^ 2 * h0 ^ 2 -
              (8192 : k[X]) * p.coeff 1 * s2 * h0 ^ 2 -
            (10368 : k[X]) * Polynomial.C lambda * p.coeff 1 * t1 *
                h0 ^ 3 +
              (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 * h0 ^ 5 := by
      rw [hVsub]; ring
    have hVcof :
        (128 : k[X]) * b1 - (2688 : k[X]) * t1 ^ 3 * s1 +
            (1568 : k[X]) * t1 ^ 2 * v1 - (384 : k[X]) * t1 * w1 -
          (40 : k[X]) * t1 ^ 3 * m1 +
            (16848 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 ^ 2 -
          (5184 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 -
            (5967 : k[X]) * Polynomial.C lambda * t1 ^ 4 +
          h0 * (-(2304 : k[X]) * s1 * m1 * t1 +
              (448 : k[X]) * v1 * m1 - (720 : k[X]) * m1 ^ 2 * t1 +
              (23040 : k[X]) * p.coeff 1 * p.coeff 2 +
              (14400 : k[X]) * p.coeff 1 * t1 ^ 2 -
              (8192 : k[X]) * p.coeff 1 * s2 -
              (10368 : k[X]) * Polynomial.C lambda * p.coeff 1 * t1 *
                h0 +
              (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 *
                h0 ^ 3) =
          Polynomial.C eps * h0 ^ 4 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C eps * h0 ^ 5 =
          h0 * (Polynomial.C eps * h0 ^ 4) := by ring
      rw [hVsplit, ← hscale]
      convert hV0 using 1
      try ring
    have heval := congrArg (fun r : k[X] => r.eval a) hVcof
    have hraw :
        (128 : k) * b1.eval a -
            (2688 : k) * (t1.eval a) ^ 3 * s1.eval a +
          (1568 : k) * (t1.eval a) ^ 2 * v1.eval a -
            (384 : k) * t1.eval a * w1.eval a -
          (40 : k) * (t1.eval a) ^ 3 * m1.eval a +
            (16848 : k) * lambda * (p.coeff 2).eval a *
              (t1.eval a) ^ 2 -
          (5184 : k) * lambda * ((p.coeff 2).eval a) ^ 2 -
            (5967 : k) * lambda * (t1.eval a) ^ 4 = 0 := by
      simpa [hroot] using heval
    have hlam :=
      ninthFace_lambdaFifth_410 (t1.eval a) ((p.coeff 2).eval a)
        lambda hmixroot
    linear_combination hraw - hlam
  have hW1 :
      -(80 : k) * b1.eval a * t1.eval a +
          (640 : k) * s1.eval a * (t1.eval a) ^ 4 -
        (448 : k) * (t1.eval a) ^ 3 * v1.eval a +
          (144 : k) * (t1.eval a) ^ 2 * w1.eval a +
        (432 : k) * lambda * (t1.eval a) ^ 5 = 0 := by
    have hWid := ninthJet_sixthId_410 t1 (p.coeff 2) s2 v3 w7 (q.coeff 5)
    have hWsub :
        -(5120 : k[X]) * p.coeff 2 ^ 3 +
            (4096 : k[X]) * p.coeff 2 ^ 2 * s2 -
          (3840 : k[X]) * p.coeff 2 ^ 2 * t1 ^ 2 -
            (12288 : k[X]) * p.coeff 2 * s2 * t1 ^ 2 +
          (20480 : k[X]) * p.coeff 2 * t1 ^ 4 +
            (7168 : k[X]) * p.coeff 2 * t1 * v3 -
          (3072 : k[X]) * p.coeff 2 * w7 -
            (2560 : k[X]) * q.coeff 5 * t1 +
          (4096 : k[X]) * s2 * t1 ^ 4 - (6400 : k[X]) * t1 ^ 6 -
            (3584 : k[X]) * t1 ^ 3 * v3 +
          (3072 : k[X]) * t1 ^ 2 * w7 =
          (640 : k[X]) * t1 ^ 4 * (h0 * s1) -
            (448 : k[X]) * t1 ^ 3 * (h0 * v1) -
          (80 : k[X]) * t1 * (h0 * b1) +
            (144 : k[X]) * t1 ^ 2 * (h0 * w1) +
          (128 : k[X]) * (h0 * s1) * (h0 * m1) ^ 2 +
            (1280 : k[X]) * (h0 * s1) * (h0 * m1) * t1 ^ 2 -
          (448 : k[X]) * (h0 * v1) * (h0 * m1) * t1 +
            (48 : k[X]) * (h0 * w1) * (h0 * m1) +
          (80 : k[X]) * (h0 * m1) ^ 3 +
            (160 : k[X]) * (h0 * m1) ^ 2 * t1 ^ 2 := by
      simpa [hs1, hv1, hw1, hb1, hm1] using hWid
    have hWsplit :
        h0 * ((640 : k[X]) * t1 ^ 4 * s1 - (448 : k[X]) * t1 ^ 3 * v1 -
              (80 : k[X]) * t1 * b1 + (144 : k[X]) * t1 ^ 2 * w1 +
            (6912 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 * t1 -
              (9216 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 ^ 3 +
            (2304 : k[X]) * Polynomial.C lambda * t1 ^ 5 +
              h0 * ((1280 : k[X]) * s1 * m1 * t1 ^ 2 -
                (448 : k[X]) * v1 * m1 * t1 +
                (48 : k[X]) * w1 * m1 +
                (160 : k[X]) * m1 ^ 2 * t1 ^ 2 +
                h0 * ((128 : k[X]) * s1 * m1 ^ 2 +
                  (80 : k[X]) * m1 ^ 3) -
                (7680 : k[X]) * p.coeff 1 * p.coeff 2 * t1 +
                (8192 : k[X]) * p.coeff 1 * s2 * t1 -
                (14080 : k[X]) * p.coeff 1 * t1 ^ 3 -
                (3584 : k[X]) * p.coeff 1 * v3 +
                (2048 : k[X]) * q.coeff 4 -
                (4608 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                  p.coeff 2 * h0 +
                (6912 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                  t1 ^ 2 * h0 +
                (10240 : k[X]) * p.coeff 0 * p.coeff 2 * h0 ^ 2 -
                (4096 : k[X]) * p.coeff 0 * s2 * h0 ^ 2 +
                (7680 : k[X]) * p.coeff 0 * t1 ^ 2 * h0 ^ 2 +
                (5120 : k[X]) * p.coeff 1 ^ 2 * h0 ^ 2 -
                (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 * t1 *
                  h0 ^ 3)) =
          -(5120 : k[X]) * p.coeff 2 ^ 3 +
              (4096 : k[X]) * p.coeff 2 ^ 2 * s2 -
            (3840 : k[X]) * p.coeff 2 ^ 2 * t1 ^ 2 -
              (12288 : k[X]) * p.coeff 2 * s2 * t1 ^ 2 +
            (20480 : k[X]) * p.coeff 2 * t1 ^ 4 +
              (7168 : k[X]) * p.coeff 2 * t1 * v3 -
            (3072 : k[X]) * p.coeff 2 * w7 -
              (2560 : k[X]) * q.coeff 5 * t1 +
            (4096 : k[X]) * s2 * t1 ^ 4 - (6400 : k[X]) * t1 ^ 6 -
              (3584 : k[X]) * t1 ^ 3 * v3 +
            (3072 : k[X]) * t1 ^ 2 * w7 +
              (6912 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 * t1 *
                h0 -
            (9216 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 ^ 3 *
                h0 +
              (2304 : k[X]) * Polynomial.C lambda * t1 ^ 5 * h0 -
            (7680 : k[X]) * p.coeff 1 * p.coeff 2 * t1 * h0 ^ 2 +
              (8192 : k[X]) * p.coeff 1 * s2 * t1 * h0 ^ 2 -
            (14080 : k[X]) * p.coeff 1 * t1 ^ 3 * h0 ^ 2 -
              (3584 : k[X]) * p.coeff 1 * v3 * h0 ^ 2 +
            (2048 : k[X]) * q.coeff 4 * h0 ^ 2 -
              (4608 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                p.coeff 2 * h0 ^ 3 +
            (6912 : k[X]) * Polynomial.C lambda * p.coeff 1 * t1 ^ 2 *
                h0 ^ 3 +
              (10240 : k[X]) * p.coeff 0 * p.coeff 2 * h0 ^ 4 -
            (4096 : k[X]) * p.coeff 0 * s2 * h0 ^ 4 +
              (7680 : k[X]) * p.coeff 0 * t1 ^ 2 * h0 ^ 4 +
            (5120 : k[X]) * p.coeff 1 ^ 2 * h0 ^ 4 -
              (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 * t1 *
                h0 ^ 5 := by
      have hWf :=
        ninthJet_sixthFactor_410 h0 t1 s1 v1 w1 b1 m1
      rw [hWsub]
      linear_combination hWf
    have hWcof :
        (640 : k[X]) * t1 ^ 4 * s1 - (448 : k[X]) * t1 ^ 3 * v1 -
            (80 : k[X]) * t1 * b1 + (144 : k[X]) * t1 ^ 2 * w1 +
          (6912 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 * t1 -
            (9216 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 ^ 3 +
          (2304 : k[X]) * Polynomial.C lambda * t1 ^ 5 +
            h0 * ((1280 : k[X]) * s1 * m1 * t1 ^ 2 -
              (448 : k[X]) * v1 * m1 * t1 +
              (48 : k[X]) * w1 * m1 +
              (160 : k[X]) * m1 ^ 2 * t1 ^ 2 +
              h0 * ((128 : k[X]) * s1 * m1 ^ 2 +
                (80 : k[X]) * m1 ^ 3) -
              (7680 : k[X]) * p.coeff 1 * p.coeff 2 * t1 +
              (8192 : k[X]) * p.coeff 1 * s2 * t1 -
              (14080 : k[X]) * p.coeff 1 * t1 ^ 3 -
              (3584 : k[X]) * p.coeff 1 * v3 +
              (2048 : k[X]) * q.coeff 4 -
              (4608 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                p.coeff 2 * h0 +
              (6912 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                t1 ^ 2 * h0 +
              (10240 : k[X]) * p.coeff 0 * p.coeff 2 * h0 ^ 2 -
              (4096 : k[X]) * p.coeff 0 * s2 * h0 ^ 2 +
              (7680 : k[X]) * p.coeff 0 * t1 ^ 2 * h0 ^ 2 +
              (5120 : k[X]) * p.coeff 1 ^ 2 * h0 ^ 2 -
              (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 * t1 *
                h0 ^ 3) =
          Polynomial.C zeta * h0 ^ 5 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C zeta * h0 ^ 6 =
          h0 * (Polynomial.C zeta * h0 ^ 5) := by ring
      rw [hWsplit, ← hscale]
      convert hW0 using 1
      try ring
    have heval := congrArg (fun r : k[X] => r.eval a) hWcof
    have hraw :
        (640 : k) * (t1.eval a) ^ 4 * s1.eval a -
            (448 : k) * (t1.eval a) ^ 3 * v1.eval a -
          (80 : k) * t1.eval a * b1.eval a +
            (144 : k) * (t1.eval a) ^ 2 * w1.eval a +
          (6912 : k) * lambda * ((p.coeff 2).eval a) ^ 2 * t1.eval a -
            (9216 : k) * lambda * (p.coeff 2).eval a *
              (t1.eval a) ^ 3 +
          (2304 : k) * lambda * (t1.eval a) ^ 5 = 0 := by
      simpa [hroot] using heval
    have hlam :=
      ninthFace_lambdaSixth_410 (t1.eval a) ((p.coeff 2).eval a)
        lambda hmixroot
    linear_combination hraw - hlam
  have ht1z :=
    ninthFace_t1_zero_410 (t1.eval a) (m1.eval a) (s1.eval a)
      (v1.eval a) (w1.eval a) (b1.eval a) lambda hlambda hM1 hT1' hU1
      hV1 hW1
  have hM1z : (4 : k) * s1.eval a + (5 : k) * m1.eval a = 0 := by
    simpa [ht1z] using hM1
  have hT1z : (16 : k) * v1.eval a = 0 := by simpa [ht1z] using hT1'
  have hU1z : (8 : k) * w1.eval a = 0 := by simpa [ht1z] using hU1
  have hV1z : (128 : k) * b1.eval a = 0 := by simpa [ht1z] using hV1
  obtain ⟨hsm, hv1z, hw1z, hb1z⟩ :=
    ninthFace_collapsedNext_410 (m1.eval a) (s1.eval a) (v1.eval a)
      (w1.eval a) (b1.eval a) hM1z hT1z hU1z hV1z
  have ha2z : (p.coeff 2).eval a = 0 := by
    have h4 : (4 : k) ≠ 0 := by norm_num
    have hm0 : (t1.eval a) ^ 2 - (4 : k) * (p.coeff 2).eval a = 0 :=
      hmixroot
    have : (4 : k) * (p.coeff 2).eval a = 0 := by
      simpa [ht1z] using hm0.symm
    exact (mul_eq_zero.mp this).resolve_left h4
  have hs2z : s2.eval a = 0 := by
    have h2 : (2 : k) ≠ 0 := by norm_num
    have : (2 : k) * s2.eval a = 0 := by simpa [ht1z] using hsroot
    exact (mul_eq_zero.mp this).resolve_left h2
  have hv3z : v3.eval a = 0 := by
    have h4 : (4 : k) ≠ 0 := by norm_num
    have : (4 : k) * v3.eval a = 0 := by simpa [ht1z] using hvroot
    exact (mul_eq_zero.mp this).resolve_left h4
  have hw7z : w7.eval a = 0 := by
    have h16 : (16 : k) ≠ 0 := by norm_num
    have : (16 : k) * w7.eval a = 0 := by simpa [ht1z] using hwroot
    exact (mul_eq_zero.mp this).resolve_left h16
  have hb5z : (q.coeff 5).eval a = 0 := by
    have h32 : (32 : k) ≠ 0 := by norm_num
    have : (32 : k) * (q.coeff 5).eval a = 0 := by
      simpa [ht1z] using hbroot
    exact (mul_eq_zero.mp this).resolve_left h32
  obtain ⟨t2, ht2⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 t1 a hh0degree hroot ht1z
  obtain ⟨a2s, ha2s'⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 (p.coeff 2) a hh0degree
      hroot ha2z
  obtain ⟨s2s, hs2s'⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 s2 a hh0degree hroot hs2z
  have hq7_6 : h0 ^ 6 ∣ q.coeff 7 := by
    have hform :
        (4 : k[X]) * v3 = h0 * v1 + (5 : k[X]) * t1 ^ 3 := by
      linear_combination hv1
    obtain ⟨v32, hv32⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_410 h0 v1 a hh0degree hroot
        hv1z
    have : (4 : k[X]) * v3 =
        h0 ^ 2 * (v32 + (5 : k[X]) * t2 ^ 3 * h0) := by
      calc
        (4 : k[X]) * v3 = h0 * v1 + (5 : k[X]) * t1 ^ 3 := hform
        _ = h0 * (h0 * v32) + (5 : k[X]) * (h0 * t2) ^ 3 := by
          rw [hv32, ht2]
        _ = h0 ^ 2 * (v32 + (5 : k[X]) * t2 ^ 3 * h0) := by ring
    have h4ne : (4 : k) ≠ 0 := by norm_num
    have hv3div : h0 ^ 2 ∣ v3 := by
      refine ⟨C (4 : k)⁻¹ * (v32 + (5 : k[X]) * t2 ^ 3 * h0), ?_⟩
      have h4C : (C (4 : k) : k[X]) * C (4 : k)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ h4ne, map_one]
      calc
        v3 = C (4 : k)⁻¹ * ((4 : k[X]) * v3) := by
          have : (4 : k[X]) = C (4 : k) :=
            (Polynomial.C_eq_natCast 4).symm
          rw [this]
          calc
            v3 = 1 * v3 := by ring
            _ = (C (4 : k) * C (4 : k)⁻¹) * v3 := by rw [h4C]
            _ = C (4 : k)⁻¹ * (C (4 : k) * v3) := by ring
        _ = C (4 : k)⁻¹ *
              (h0 ^ 2 * (v32 + (5 : k[X]) * t2 ^ 3 * h0)) := by
          rw [this]
        _ = h0 ^ 2 * (C (4 : k)⁻¹ *
              (v32 + (5 : k[X]) * t2 ^ 3 * h0)) := by ring
    have ⟨r7, hr7⟩ := hv3div
    refine ⟨r7, ?_⟩
    calc
      q.coeff 7 = h0 ^ 4 * v3 := hv3
      _ = h0 ^ 4 * (h0 ^ 2 * r7) := by rw [hr7]
      _ = h0 ^ 6 * r7 := by ring
  have hq6_4 : h0 ^ 4 ∣ q.coeff 6 := by
    have hform :
        (16 : k[X]) * w7 = h0 * w1 + (5 : k[X]) * t1 ^ 4 := by
      linear_combination hw1
    obtain ⟨w32, hw32⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_410 h0 w1 a hh0degree hroot
        hw1z
    have : (16 : k[X]) * w7 =
        h0 ^ 2 * (w32 + (5 : k[X]) * t2 ^ 4 * h0 ^ 2) := by
      calc
        (16 : k[X]) * w7 =
            h0 * (h0 * w32) + (5 : k[X]) * (h0 * t2) ^ 4 := by
          rw [← hw32, ← ht2]
          exact hform
        _ = h0 ^ 2 * (w32 + (5 : k[X]) * t2 ^ 4 * h0 ^ 2) := by ring
    have h16ne : (16 : k) ≠ 0 := by norm_num
    have hw7div : h0 ^ 2 ∣ w7 := by
      refine ⟨C (16 : k)⁻¹ * (w32 + (5 : k[X]) * t2 ^ 4 * h0 ^ 2), ?_⟩
      have h16C : (C (16 : k) : k[X]) * C (16 : k)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ h16ne, map_one]
      calc
        w7 = C (16 : k)⁻¹ * ((16 : k[X]) * w7) := by
          have : (16 : k[X]) = C (16 : k) :=
            (Polynomial.C_eq_natCast 16).symm
          rw [this]
          calc
            w7 = 1 * w7 := by ring
            _ = (C (16 : k) * C (16 : k)⁻¹) * w7 := by rw [h16C]
            _ = C (16 : k)⁻¹ * (C (16 : k) * w7) := by ring
        _ = C (16 : k)⁻¹ *
              (h0 ^ 2 * (w32 + (5 : k[X]) * t2 ^ 4 * h0 ^ 2)) := by
          rw [this]
        _ = h0 ^ 2 * (C (16 : k)⁻¹ *
              (w32 + (5 : k[X]) * t2 ^ 4 * h0 ^ 2)) := by ring
    obtain ⟨r6, hr6⟩ := hw7div
    refine ⟨r6, ?_⟩
    calc
      q.coeff 6 = h0 ^ 2 * w7 := hw7
      _ = h0 ^ 2 * (h0 ^ 2 * r6) := by rw [hr6]
      _ = h0 ^ 4 * r6 := by ring
  have hq5_2 : h0 ^ 2 ∣ q.coeff 5 := by
    have hform :
        (32 : k[X]) * q.coeff 5 = h0 * b1 + t1 ^ 5 := by
      linear_combination hb1
    obtain ⟨b32, hb32⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_410 h0 b1 a hh0degree hroot
        hb1z
    have : (32 : k[X]) * q.coeff 5 =
        h0 ^ 2 * (b32 + t2 ^ 5 * h0 ^ 3) := by
      calc
        (32 : k[X]) * q.coeff 5 =
            h0 * (h0 * b32) + (h0 * t2) ^ 5 := by
          rw [← hb32, ← ht2]
          exact hform
        _ = h0 ^ 2 * (b32 + t2 ^ 5 * h0 ^ 3) := by ring
    have h32ne : (32 : k) ≠ 0 := by norm_num
    refine ⟨C (32 : k)⁻¹ * (b32 + t2 ^ 5 * h0 ^ 3), ?_⟩
    have h32C : (C (32 : k) : k[X]) * C (32 : k)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h32ne, map_one]
    calc
      q.coeff 5 = C (32 : k)⁻¹ * ((32 : k[X]) * q.coeff 5) := by
        have : (32 : k[X]) = C (32 : k) :=
          (Polynomial.C_eq_natCast 32).symm
        rw [this]
        calc
          q.coeff 5 = 1 * q.coeff 5 := by ring
          _ = (C (32 : k) * C (32 : k)⁻¹) * q.coeff 5 := by rw [h32C]
          _ = C (32 : k)⁻¹ * (C (32 : k) * q.coeff 5) := by ring
      _ = C (32 : k)⁻¹ * (h0 ^ 2 * (b32 + t2 ^ 5 * h0 ^ 3)) := by
        rw [this]
      _ = h0 ^ 2 * (C (32 : k)⁻¹ * (b32 + t2 ^ 5 * h0 ^ 3)) := by ring
  have hp3_3 : h0 ^ 3 ∣ p.coeff 3 := by
    refine ⟨t2, ?_⟩
    calc
      p.coeff 3 = h0 ^ 2 * t1 := ht1
      _ = h0 ^ 2 * (h0 * t2) := by rw [ht2]
      _ = h0 ^ 3 * t2 := by ring
  have hq8_7 : h0 ^ 7 ∣ q.coeff 8 := by
    refine ⟨s2s, ?_⟩
    calc
      q.coeff 8 = h0 ^ 6 * s2 := hs2
      _ = h0 ^ 6 * (h0 * s2s) := by rw [hs2s']
      _ = h0 ^ 7 * s2s := by ring
  exact ⟨t1, s2, v3, w7, m1, s1, v1, w1, b1, ht1, hs2, hv3, hw7, hs1, hv1,
    hw1, hb1, hm1, ht1z, ha2z, hb5z, hs2z, hv3z, hw7z, hsm, hv1z, hw1z,
    hb1z, hp3_3, ⟨a2s, ha2s'⟩, hq8_7, hq7_6, hq6_4, hq5_2, hq9⟩

/-- Source-facing ninth-face packet of a normalized scale-two `(4,10)`
nonzero face: the eighth-face jet collapses at the root of `h`. -/
theorem normalized410ScaleTwo_nonzeroFace_ninthInitialPacket
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
        h0 ^ 3 ∣ p.coeff 3 ∧ h0 ∣ p.coeff 2 ∧
        h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 7 ∧
        h0 ^ 4 ∣ q.coeff 6 ∧ h0 ^ 2 ∣ q.coeff 5 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        (p.coeff 2).eval a = 0 ∧ (q.coeff 5).eval a = 0 ∧
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
  obtain ⟨t1, s2, v3, w7, m1, s1, v1, w1, b1, ht1, hs2, hv3, hw7, hs1,
    hv1, hw1, hb1, hm1, ht1z, ha2z, hb5z, hs2z, hv3z, hw7z, hsm, hv1z,
    hw1z, hb1z, hp3_3, hp2_1, hq8_7, hq7_6, hq6_4, hq5_2, hq9⟩ :=
    nonzeroFace410_linearRoot_ninthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot hlambda
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp3_3, hp2_1,
    hq8_7, hq7_6, hq6_4, hq5_2, hq9, ha2z, hb5z, hN'⟩

end NonzeroNinthFace410

#print axioms ninthCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_4_monicQuarticDecic
#print axioms thetaResidual410_deriv_zero
#print axioms ninthFace_nextOrderCombo_410
#print axioms ninthFace_t1_zero_410
#print axioms ninthFace_collapsedNext_410
#print axioms ninthJet_secondLeading_410
#print axioms ninthJet_fourthId_410
#print axioms ninthFace_lambdaThird_410
#print axioms nonzeroFace410_linearRoot_ninthInitialPacket
#print axioms normalized410ScaleTwo_nonzeroFace_ninthInitialPacket

end Max11DegreeRoutes
