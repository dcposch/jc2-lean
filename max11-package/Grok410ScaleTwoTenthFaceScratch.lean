import Grok410ScaleTwoNinthFaceScratch

/-! # Scale-two tenth face for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the ninth-face packet supplies the degree-`4`
integral of weight twenty-nine (larger than the remaining exact jet) and
the collapsed jet `h³ ∣ p₃`, `h ∣ p₂`, `h⁷ ∣ q₈`, `h⁶ ∣ q₇`,
`h⁴ ∣ q₆`, `h² ∣ q₅`, `h⁸ ∣ q₉` together with
`2 (q₈/h⁷)(a) = 5 (p₂/h)(a)`.

The next unused Keller coefficient is the degree-`3` Jacobian row.  After
the same quartic depression that kills `z³`, that row is
`4 T C' + 3 U B' + 2 V A' - B U' - 2 A V' - 4 Z' = 0`.  The corresponding
first integral is the residual `ι` below.  Clearing it against the
decic `z⁰` coordinate produces a defect larger than the remaining exact
jet, so this file isolates that Jacobian identity, the first integral,
and the strongest exact next-order refinement of the collapsed
ninth-face jet.

Evaluating the second through sixth and eighth defects on the collapsed
jet forces `(p₂/h)(a) = 0`, hence `h² ∣ p₂`, `h⁸ ∣ q₈`, `h⁵ ∣ q₆`,
`h³ ∣ q₅`, `h² ∣ q₄`, together with the source-facing identity
`2 (q₇/h⁶)(a) = 5 p₁(a)`.  No further individual vanishing of
`p₁, p₀, q₃, q₂` or of `(p₃/h³)(a)` is claimed.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The tenth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  Unused Jacobian coefficients of the ninth face start
at degree `3`. -/
theorem tenthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 3) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (3 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 3 :
      Finset (ℕ × ℕ)) =
      ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  rw [hC2, hC3, hC4]
  linear_combination hcoeff

/-! ## Quartic constant and decic `z⁰` coordinates -/

section Depression410Tenth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z⁰` coefficient. -/
def depressedZ410 (h r b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F) : F :=
  r ^ 10 - (b9 / h ^ 9) * r ^ 9 + (b8 / h ^ 8) * r ^ 8 -
    (b7 / h ^ 7) * r ^ 7 + (b6 / h ^ 6) * r ^ 6 -
    (b5 / h ^ 5) * r ^ 5 + (b4 / h ^ 4) * r ^ 4 -
    (b3 / h ^ 3) * r ^ 3 + (b2 / h ^ 2) * r ^ 2 -
    (b1 / h) * r + b0

/-- First residual of the degree-`3` row.  Equivalent to
`Z - (1/2) η A - (3/4) ζ B - ε C - (3/256) A⁵ + (45/512) L A³ B
+ (5/32) A³ C + (1/16) γ A³ + (15/64) A² B² + (21/128) β A² B
- (45/64) L A B C - (15/128) L B³ - (5/16) δ A B - (15/16) A C²
- (3/4) γ A C - (15/16) B² C - (3/8) γ B² - (21/16) β B C - α C²`
on the second- through ninth-face integrals. -/
def iotaResidual410 (L A B C0 P Q R S0 T0 U0 V0 Z0 : F) : F :=
  Z0 - (1 / 2 : F) * etaResidual410 L A B C0 P Q R S0 T0 V0 * A -
    (3 / 4 : F) * zetaResidual410 L A B C0 P Q R S0 U0 * B -
    epsilonResidual410 L A B C0 P Q R T0 * C0 -
    (3 / 256 : F) * A ^ 5 +
    (45 / 512 : F) * L * A ^ 3 * B +
    (5 / 32 : F) * A ^ 3 * C0 +
    (1 / 16 : F) * gammaResidual410 L A B C0 P R * A ^ 3 +
    (15 / 64 : F) * A ^ 2 * B ^ 2 +
    (21 / 128 : F) * betaResidual410 L A B Q * A ^ 2 * B -
    (45 / 64 : F) * L * A * B * C0 -
    (15 / 128 : F) * L * B ^ 3 -
    (5 / 16 : F) * deltaResidual410 L A B C0 P Q S0 * A * B -
    (15 / 16 : F) * A * C0 ^ 2 -
    (3 / 4 : F) * gammaResidual410 L A B C0 P R * A * C0 -
    (15 / 16 : F) * B ^ 2 * C0 -
    (3 / 8 : F) * gammaResidual410 L A B C0 P R * B ^ 2 -
    (21 / 16 : F) * betaResidual410 L A B Q * B * C0 -
    alphaResidual410 A P * C0 ^ 2

end Depression410Tenth

/-! ## Degree-`3` depressed Jacobian coefficient -/

section DepressedRow410Tenth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`3` Jacobian coefficient is
exactly `4 T C' + 3 U B' + 2 V A' - B U' - 2 A V' - 4 Z'`. -/
theorem differentialJacobian_coeff_3_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 3 =
      (4 : F) * g.coeff 4 * d (f.coeff 0) +
        (3 : F) * g.coeff 3 * d (f.coeff 1) +
        (2 : F) * g.coeff 2 * d (f.coeff 2) -
          f.coeff 1 * d (g.coeff 3) -
          (2 : F) * f.coeff 2 * d (g.coeff 2) -
          (4 : F) * d (g.coeff 0) := by
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
  have hmem03 : ((0, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (3 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem12 : ((1, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (3 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem21 : ((2, 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (3 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem30 : ((3, 0) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (3 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 3 =
        (4 : F) * g.coeff 4 * d (f.coeff 0) +
          (3 : F) * g.coeff 3 * d (f.coeff 1) +
          (2 : F) * g.coeff 2 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne01 : ((0, 3) : ℕ × ℕ) ≠ (1, 2) := by decide
    have hne02 : ((0, 3) : ℕ × ℕ) ≠ (2, 1) := by decide
    have hne12 : ((1, 2) : ℕ × ℕ) ≠ (2, 1) := by decide
    have hsubset : ({(0, 3), (1, 2), (2, 1)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (3 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b; exact hmem03
      · subst b; exact hmem12
      · subst b; exact hmem21
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (3 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 3), (1, 2), (2, 1)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 3 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne03 : b ≠ (0, 3) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne12 : b ≠ (1, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne21 : b ≠ (2, 1) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 3 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne03
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne12
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne21
          ext
          · exact h2
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 3), (1, 2), (2, 1)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 1 := by
      rw [Finset.sum_insert (by simp [hne01, hne02]),
        Finset.sum_insert (by simp [hne12]), Finset.sum_singleton]
      ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder3, hder2, hder1]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 3 =
        f.coeff 1 * d (g.coeff 3) +
          (2 : F) * f.coeff 2 * d (g.coeff 2) +
          (4 : F) * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul]
    have hne03_12 : ((0, 3) : ℕ × ℕ) ≠ (1, 2) := by decide
    have hne03_30 : ((0, 3) : ℕ × ℕ) ≠ (3, 0) := by decide
    have hne12_30 : ((1, 2) : ℕ × ℕ) ≠ (3, 0) := by decide
    have hsubset : ({(0, 3), (1, 2), (3, 0)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (3 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b; exact hmem03
      · subst b; exact hmem12
      · subst b; exact hmem30
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (3 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 3), (1, 2), (3, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 3 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne03 : b ≠ (0, 3) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne12 : b ≠ (1, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne30 : b ≠ (3, 0) := by
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
            apply hne03
            ext
            · exact h0
            · omega
          have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne12
            ext
            · exact h1
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne30
            ext
            · exact h3
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 3), (1, 2), (3, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne03_12, hne03_30]),
        Finset.sum_insert (by simp [hne12_30]), Finset.sum_singleton]
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

theorem iotaResidual410_eq_expanded
    (L A B C0 P Q R S0 T0 U0 V0 Z0 : F) :
    iotaResidual410 L A B C0 P Q R S0 T0 U0 V0 Z0 =
      Z0 - (1 / 2 : F) * A * V0 - (3 / 4 : F) * B * U0 - C0 * T0 +
        (1 / 2 : F) * (A * A) * T0 + (5 / 4 : F) * A * B * S0 +
        (3 / 2 : F) * A * C0 * R + (3 / 4 : F) * (B * B) * R +
        (7 / 4 : F) * B * C0 * Q + P * (C0 * C0) +
        (1 / 2 : F) * (A * A * A * A) * P -
        (1 / 2 : F) * (A * A * A) * R -
        (7 / 4 : F) * (A * A) * B * Q -
        (2 : F) * (A * A) * C0 * P -
        (2 : F) * A * (B * B) * P +
        (9 / 4 : F) * L * (A * A * A) * B -
        (9 / 2 : F) * L * A * B * C0 -
        (3 / 4 : F) * L * (B * B * B) -
        (1 / 2 : F) * (A * A * A * A * A) +
        (5 / 2 : F) * (A * A * A) * C0 +
        (15 / 4 : F) * (A * A) * (B * B) -
        (5 / 2 : F) * A * (C0 * C0) -
        (5 / 2 : F) * (B * B) * C0 := by
  simp only [iotaResidual410, alphaResidual410, betaResidual410,
    gammaResidual410, deltaResidual410, epsilonResidual410,
    zetaResidual410, etaResidual410, pow_two, pow_three]
  ring


end DepressedRow410Tenth

/-! ## Order-one scalar algebra on the collapsed ninth-face jet -/

section TenthFaceScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- The second defect at the next order on the collapsed jet is
`2 s₂₁ = 5 a₂₁`. -/
theorem tenthFace_M_nextOrder410 (a21 s21 : F)
    (hM : (8 : F) * s21 - (20 : F) * a21 = 0) :
    (2 : F) * s21 = (5 : F) * a21 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have hid : (4 : F) * ((2 : F) * s21 - (5 : F) * a21) =
      (8 : F) * s21 - (20 : F) * a21 := by ring
  have : (4 : F) * ((2 : F) * s21 - (5 : F) * a21) = 0 := by
    rw [hid, hM]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h4)

/-- The fourth defect at the next order forces
`8 (q₆/h⁴)(a) = 15 (p₂/h)(a)²`. -/
theorem tenthFace_U_nextOrder410 (a21 s21 w72 : F)
    (hM : (8 : F) * s21 - (20 : F) * a21 = 0)
    (hU : (128 : F) * w72 - (256 : F) * a21 * s21 +
      (400 : F) * a21 ^ 2 = 0) :
    (8 : F) * w72 = (15 : F) * a21 ^ 2 := by
  have hs := tenthFace_M_nextOrder410 a21 s21 hM
  have h16 : (16 : F) ≠ 0 := by norm_num
  have hid :
      (16 : F) * ((8 : F) * w72 - (15 : F) * a21 ^ 2) =
        (128 : F) * w72 - (256 : F) * a21 * s21 +
          (400 : F) * a21 ^ 2 +
        (32 : F) * a21 * ((8 : F) * s21 - (20 : F) * a21) := by
    ring
  have hcomb :
      (16 : F) * ((8 : F) * w72 - (15 : F) * a21 ^ 2) = 0 := by
    rw [hid]
    linear_combination hU + (32 : F) * a21 * hM
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcomb).resolve_left h16)

/-- The fifth defect at the next order on the collapsed jet forces
`(q₅/h²)(a) = 0`. -/
theorem tenthFace_V_nextOrder410 (q52 : F)
    (hV : (4096 : F) * q52 = 0) :
    q52 = 0 := by
  have h4096 : (4096 : F) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hV).resolve_left h4096

/-- The sixth defect at the next order on the collapsed jet forces
`q₄(a) = 0`. -/
theorem tenthFace_W_nextOrder410 (q4 : F)
    (hW : (2048 : F) * q4 = 0) :
    q4 = 0 := by
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hW).resolve_left h2048

/-- After `q₄(a) = 0`, the sixth defect's next coefficient is
`16 (q₄/h)(a) = 5 (p₂/h)(a)³`. -/
theorem tenthFace_W17_nextOrder410 (a21 s21 w72 b41 : F)
    (hM : (8 : F) * s21 - (20 : F) * a21 = 0)
    (hU : (128 : F) * w72 - (256 : F) * a21 * s21 +
      (400 : F) * a21 ^ 2 = 0)
    (hW : (4096 : F) * a21 ^ 2 * s21 - (5120 : F) * a21 ^ 3 -
      (3072 : F) * a21 * w72 + (2048 : F) * b41 = 0) :
    (16 : F) * b41 = (5 : F) * a21 ^ 3 := by
  have hs := tenthFace_M_nextOrder410 a21 s21 hM
  have hw := tenthFace_U_nextOrder410 a21 s21 w72 hM hU
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have hs1 : s21 = (5 / 2 : F) * a21 := by
    have hid : (2 : F) * (s21 - (5 / 2 : F) * a21) =
        (2 : F) * s21 - (5 : F) * a21 := by ring
    have : (2 : F) * (s21 - (5 / 2 : F) * a21) = 0 := by
      rw [hid]; linear_combination hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
  have hw1 : w72 = (15 / 8 : F) * a21 ^ 2 := by
    have hid : (8 : F) * (w72 - (15 / 8 : F) * a21 ^ 2) =
        (8 : F) * w72 - (15 : F) * a21 ^ 2 := by ring
    have : (8 : F) * (w72 - (15 / 8 : F) * a21 ^ 2) = 0 := by
      rw [hid]; linear_combination hw
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h8)
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have : (2048 : F) * ((16 : F) * b41 - (5 : F) * a21 ^ 3) = 0 := by
    simp only [hs1, hw1] at hW
    linear_combination (16 : F) * hW
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2048)

/-- The eighth defect's leading cofactor on the collapsed jet, together
with the second, fourth, and sixth identities, forces `(p₂/h)(a) = 0`. -/
theorem tenthFace_Y_a21_zero410 (a21 s21 w72 b41 : F)
    (hM : (8 : F) * s21 - (20 : F) * a21 = 0)
    (hU : (128 : F) * w72 - (256 : F) * a21 * s21 +
      (400 : F) * a21 ^ 2 = 0)
    (hW : (4096 : F) * a21 ^ 2 * s21 - (5120 : F) * a21 ^ 3 -
      (3072 : F) * a21 * w72 + (2048 : F) * b41 = 0)
    (hY : -(40960 : F) * a21 ^ 3 * s21 + (44800 : F) * a21 ^ 4 +
      (36864 : F) * a21 ^ 2 * w72 - (32768 : F) * a21 * b41 = 0) :
    a21 = 0 := by
  have hs := tenthFace_M_nextOrder410 a21 s21 hM
  have hw := tenthFace_U_nextOrder410 a21 s21 w72 hM hU
  have hb := tenthFace_W17_nextOrder410 a21 s21 w72 b41 hM hU hW
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have hs1 : s21 = (5 / 2 : F) * a21 := by
    have hid : (2 : F) * (s21 - (5 / 2 : F) * a21) =
        (2 : F) * s21 - (5 : F) * a21 := by ring
    have : (2 : F) * (s21 - (5 / 2 : F) * a21) = 0 := by
      rw [hid]; linear_combination hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
  have hw1 : w72 = (15 / 8 : F) * a21 ^ 2 := by
    have hid : (8 : F) * (w72 - (15 / 8 : F) * a21 ^ 2) =
        (8 : F) * w72 - (15 : F) * a21 ^ 2 := by ring
    have : (8 : F) * (w72 - (15 / 8 : F) * a21 ^ 2) = 0 := by
      rw [hid]; linear_combination hw
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h8)
  have hb1 : b41 = (5 / 16 : F) * a21 ^ 3 := by
    have hid : (16 : F) * (b41 - (5 / 16 : F) * a21 ^ 3) =
        (16 : F) * b41 - (5 : F) * a21 ^ 3 := by ring
    have : (16 : F) * (b41 - (5 / 16 : F) * a21 ^ 3) = 0 := by
      rw [hid]; linear_combination hb
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h16)
  have h1280 : (1280 : F) ≠ 0 := by norm_num
  have hpow : (1280 : F) * a21 ^ 4 = 0 := by
    simp only [hs1, hw1, hb1] at hY
    linear_combination hY
  have h4 : a21 ^ 4 = 0 :=
    (mul_eq_zero.mp hpow).resolve_left h1280
  have hlin : a21 * a21 ^ 3 = 0 := by simpa [pow_succ] using h4
  rcases mul_eq_zero.mp hlin with ht | h3
  · exact ht
  · have hlin2 : a21 * a21 ^ 2 = 0 := by simpa [pow_succ] using h3
    rcases mul_eq_zero.mp hlin2 with ht | h2
    · exact ht
    · exact (mul_eq_zero.mp (by simpa [pow_two] using h2)).elim id id

/-- After `(p₂/h)(a) = 0`, the third defect forces
`2 (q₇/h⁶)(a) = 5 p₁(a)`. -/
theorem tenthFace_T_collapsed410 (v32 a1 : F)
    (hT : (64 : F) * v32 - (160 : F) * a1 = 0) :
    (2 : F) * v32 = (5 : F) * a1 := by
  have h32 : (32 : F) ≠ 0 := by norm_num
  have hid : (32 : F) * ((2 : F) * v32 - (5 : F) * a1) =
      (64 : F) * v32 - (160 : F) * a1 := by ring
  have : (32 : F) * ((2 : F) * v32 - (5 : F) * a1) = 0 := by
    rw [hid, hT]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h32)

/-- After `(p₂/h)(a) = 0`, the fourth defect forces
`8 (q₆/h⁵)(a) = p₁(a) (30 t₂(a) - 9 λ)`. -/
theorem tenthFace_U_collapsed410 (t2 v32 w73 a1 lam : F)
    (hT : (64 : F) * v32 - (160 : F) * a1 = 0)
    (hU : (144 : F) * a1 * lam + (80 : F) * t2 * a1 -
      (224 : F) * t2 * v32 + (128 : F) * w73 = 0) :
    (8 : F) * w73 = a1 * ((30 : F) * t2 - (9 : F) * lam) := by
  have hv := tenthFace_T_collapsed410 v32 a1 hT
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have hv1 : v32 = (5 / 2 : F) * a1 := by
    have hid : (2 : F) * (v32 - (5 / 2 : F) * a1) =
        (2 : F) * v32 - (5 : F) * a1 := by ring
    have : (2 : F) * (v32 - (5 / 2 : F) * a1) = 0 := by
      rw [hid]; linear_combination hv
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
  have : (16 : F) * ((8 : F) * w73 -
      a1 * ((30 : F) * t2 - (9 : F) * lam)) = 0 := by
    simp only [hv1] at hU
    linear_combination hU
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h16)

/-- After `(p₂/h)(a) = 0` and `(q₅/h³)(a) = 0`, the sixth defect forces
`8 (q₄/h²)(a) = 15 p₁(a)²`. -/
theorem tenthFace_W_collapsed410 (v32 a1 b42 : F)
    (hT : (64 : F) * v32 - (160 : F) * a1 = 0)
    (hW : (5120 : F) * a1 ^ 2 - (3584 : F) * v32 * a1 +
      (2048 : F) * b42 = 0) :
    (8 : F) * b42 = (15 : F) * a1 ^ 2 := by
  have hv := tenthFace_T_collapsed410 v32 a1 hT
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have hv1 : v32 = (5 / 2 : F) * a1 := by
    have hid : (2 : F) * (v32 - (5 / 2 : F) * a1) =
        (2 : F) * v32 - (5 : F) * a1 := by ring
    have : (2 : F) * (v32 - (5 / 2 : F) * a1) = 0 := by
      rw [hid]; linear_combination hv
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
  have : (256 : F) * ((8 : F) * b42 - (15 : F) * a1 ^ 2) = 0 := by
    simp only [hv1] at hW
    linear_combination hW
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h256)

/-- Combined next-order identities of the collapsed ninth-face jet. -/
theorem tenthFace_collapsedNextOrder410 (a21 s21 w72 q52 q4 b41 t2 v32
    w73 a1 b42 lam : F)
    (hM : (8 : F) * s21 - (20 : F) * a21 = 0)
    (hU : (128 : F) * w72 - (256 : F) * a21 * s21 +
      (400 : F) * a21 ^ 2 = 0)
    (hV : (4096 : F) * q52 = 0)
    (hW16 : (2048 : F) * q4 = 0)
    (hW17 : (4096 : F) * a21 ^ 2 * s21 - (5120 : F) * a21 ^ 3 -
      (3072 : F) * a21 * w72 + (2048 : F) * b41 = 0)
    (hY : -(40960 : F) * a21 ^ 3 * s21 + (44800 : F) * a21 ^ 4 +
      (36864 : F) * a21 ^ 2 * w72 - (32768 : F) * a21 * b41 = 0)
    (hT : (64 : F) * v32 - (160 : F) * a1 = 0)
    (hU2 : (144 : F) * a1 * lam + (80 : F) * t2 * a1 -
      (224 : F) * t2 * v32 + (128 : F) * w73 = 0)
    (hW18 : (5120 : F) * a1 ^ 2 - (3584 : F) * v32 * a1 +
      (2048 : F) * b42 = 0) :
    (2 : F) * s21 = (5 : F) * a21 ∧ q52 = 0 ∧ q4 = 0 ∧
      (8 : F) * w72 = (15 : F) * a21 ^ 2 ∧
      (16 : F) * b41 = (5 : F) * a21 ^ 3 ∧ a21 = 0 ∧
      (2 : F) * v32 = (5 : F) * a1 ∧
      (8 : F) * w73 = a1 * ((30 : F) * t2 - (9 : F) * lam) ∧
      (8 : F) * b42 = (15 : F) * a1 ^ 2 :=
  ⟨tenthFace_M_nextOrder410 a21 s21 hM,
    tenthFace_V_nextOrder410 q52 hV,
    tenthFace_W_nextOrder410 q4 hW16,
    tenthFace_U_nextOrder410 a21 s21 w72 hM hU,
    tenthFace_W17_nextOrder410 a21 s21 w72 b41 hM hU hW17,
    tenthFace_Y_a21_zero410 a21 s21 w72 b41 hM hU hW17 hY,
    tenthFace_T_collapsed410 v32 a1 hT,
    tenthFace_U_collapsed410 t2 v32 w73 a1 lam hT hU2,
    tenthFace_W_collapsed410 v32 a1 b42 hT hW18⟩

/-! ## Collapsed substitutions of the cleared defects -/

theorem tenthFace_clearedM_collapsed410 (h t2 a21 s21 : F[X])
    (lambda : F) :
    localClearedSecondDefect410 h (h ^ 3 * t2) (h * a21)
        (h ^ 7 * s21) lambda =
      h ^ 7 * ((8 : F[X]) * s21 - (20 : F[X]) * a21 +
        (9 : F[X]) * Polynomial.C lambda * t2 * h -
        (15 : F[X]) * t2 ^ 2 * h) := by
  simp only [localClearedSecondDefect410]
  ring

theorem tenthFace_clearedT_collapsed410 (h t2 a21 s21 v32 a1 : F[X])
    (lambda : F) :
    localClearedThirdDefect410 h (h ^ 3 * t2) (h * a21) a1
        (h ^ 7 * s21) (h ^ 6 * v32) lambda =
      h ^ 10 * ((64 : F[X]) * v32 - (160 : F[X]) * a1 +
        (72 : F[X]) * Polynomial.C lambda * a21 -
        (128 : F[X]) * t2 * s21 + (80 : F[X]) * t2 * a21 +
        (220 : F[X]) * t2 ^ 3 * h -
        (99 : F[X]) * Polynomial.C lambda * t2 ^ 2 * h) := by
  simp only [localClearedThirdDefect410]
  ring

theorem tenthFace_clearedU_collapsed410 (h t2 a21 s21 v32 w72 a1 a0 :
    F[X]) (lambda : F) :
    localClearedFourthDefect410 h (h ^ 3 * t2) (h * a21) a1 a0
        (h ^ 7 * s21) (h ^ 6 * v32) (h ^ 4 * w72) lambda =
      h ^ 12 * ((128 : F[X]) * w72 - (256 : F[X]) * a21 * s21 +
        (400 : F[X]) * a21 ^ 2 +
        (144 : F[X]) * Polynomial.C lambda * a1 * h +
        (80 : F[X]) * t2 * a1 * h - (224 : F[X]) * t2 * v32 * h +
        (320 : F[X]) * t2 ^ 2 * s21 * h +
        (400 : F[X]) * t2 ^ 2 * a21 * h -
        (360 : F[X]) * Polynomial.C lambda * t2 * a21 * h +
        (210 : F[X]) * Polynomial.C lambda * t2 ^ 3 * h ^ 2 -
        (525 : F[X]) * t2 ^ 4 * h ^ 2 -
        (320 : F[X]) * a0 * h ^ 2) := by
  simp only [localClearedFourthDefect410]
  ring

set_option maxHeartbeats 4000000 in
theorem tenthFace_clearedV_collapsed410 (h t2 a21 s21 v32 w72 q52 a1 a0 :
    F[X]) (lambda : F) :
    localClearedFifthDefect410 h (h ^ 3 * t2) (h * a21) a1 a0
        (h ^ 7 * s21) (h ^ 6 * v32) (h ^ 4 * w72) (h ^ 2 * q52)
        lambda =
      h ^ 14 * ((4096 : F[X]) * q52 +
        h * ((-5184 : F[X]) * a21 ^ 2 * Polynomial.C lambda +
          (18432 : F[X]) * t2 * a21 * s21 -
          (11520 : F[X]) * t2 * a21 ^ 2 -
          (8192 : F[X]) * s21 * a1 + (23040 : F[X]) * a21 * a1 -
          (7168 : F[X]) * a21 * v32 - (6144 : F[X]) * t2 * w72 +
          h * ((16848 : F[X]) * t2 ^ 2 * a21 * Polynomial.C lambda -
            (9984 : F[X]) * t2 ^ 3 * s21 -
            (31200 : F[X]) * t2 ^ 3 * a21 -
            (10368 : F[X]) * t2 * a1 * Polynomial.C lambda +
            (14400 : F[X]) * t2 ^ 2 * a1 +
            (8064 : F[X]) * t2 ^ 2 * v32 +
            h * ((-5967 : F[X]) * t2 ^ 4 * Polynomial.C lambda +
              (15912 : F[X]) * t2 ^ 5 +
              (4608 : F[X]) * a0 * Polynomial.C lambda)))) := by
  simp only [localClearedFifthDefect410]
  ring

set_option maxHeartbeats 8000000 in
theorem tenthFace_clearedW_collapsed410 (h t2 a21 s21 v32 w72 q52 a1 a0
    b4 : F[X]) (lambda : F) :
    localClearedSixthDefect410 h (h ^ 3 * t2) (h * a21) a1 a0
        (h ^ 7 * s21) (h ^ 6 * v32) (h ^ 4 * w72) (h ^ 2 * q52) b4
        lambda =
      h ^ 16 * ((2048 : F[X]) * b4 +
        h * ((4096 : F[X]) * a21 ^ 2 * s21 - (5120 : F[X]) * a21 ^ 3 -
          (3072 : F[X]) * a21 * w72 - (2560 : F[X]) * t2 * q52 +
          h * ((6912 : F[X]) * t2 * a21 ^ 2 * Polynomial.C lambda -
            (12288 : F[X]) * t2 ^ 2 * a21 * s21 -
            (3840 : F[X]) * t2 ^ 2 * a21 ^ 2 -
            (4608 : F[X]) * a21 * a1 * Polynomial.C lambda +
            (8192 : F[X]) * t2 * s21 * a1 -
            (7680 : F[X]) * t2 * a21 * a1 +
            (7168 : F[X]) * t2 * a21 * v32 +
            (3072 : F[X]) * t2 ^ 2 * w72 + (5120 : F[X]) * a1 ^ 2 -
            (3584 : F[X]) * v32 * a1 +
            h * ((-9216 : F[X]) * t2 ^ 3 * a21 * Polynomial.C lambda +
              (4096 : F[X]) * t2 ^ 4 * s21 +
              (20480 : F[X]) * t2 ^ 4 * a21 +
              (6912 : F[X]) * t2 ^ 2 * a1 * Polynomial.C lambda -
              (14080 : F[X]) * t2 ^ 3 * a1 -
              (3584 : F[X]) * t2 ^ 3 * v32 -
              (4096 : F[X]) * s21 * a0 + (10240 : F[X]) * a21 * a0 +
              h * ((2304 : F[X]) * t2 ^ 5 * Polynomial.C lambda -
                (6400 : F[X]) * t2 ^ 6 -
                (4608 : F[X]) * t2 * a0 * Polynomial.C lambda +
                (7680 : F[X]) * t2 ^ 2 * a0))))) := by
  simp only [localClearedSixthDefect410]
  ring

set_option maxHeartbeats 16000000 in
theorem tenthFace_clearedY_collapsed410 (h t2 a21 s21 v32 w72 q52 a1 a0
    b41 b3 b2 : F[X]) (lambda : F) :
    localClearedEighthDefect410 h (h ^ 3 * t2) (h * a21) a1 a0
        (h ^ 7 * s21) (h ^ 6 * v32) (h ^ 4 * w72) (h ^ 2 * q52)
        (h * b41) b3 b2 lambda =
      h ^ 22 * (-(40960 : F[X]) * q52 * a1 -
          (32768 : F[X]) * a21 * b41 +
          (36864 : F[X]) * a21 ^ 2 * w72 -
          (40960 : F[X]) * a21 ^ 3 * s21 +
          (44800 : F[X]) * a21 ^ 4 +
          (61440 : F[X]) * t2 * a21 * q52 +
          h * ((49152 : F[X]) * s21 * a1 ^ 2 -
            (153600 : F[X]) * a21 * a1 ^ 2 +
            (86016 : F[X]) * a21 * v32 * a1 +
            (69120 : F[X]) * a21 ^ 2 * a1 * Polynomial.C lambda -
            (24576 : F[X]) * t2 * b3 +
            (73728 : F[X]) * t2 * w72 * a1 -
            (245760 : F[X]) * t2 * a21 * s21 * a1 +
            (192000 : F[X]) * t2 * a21 ^ 2 * a1 -
            (107520 : F[X]) * t2 * a21 ^ 2 * v32 -
            (80640 : F[X]) * t2 * a21 ^ 3 * Polynomial.C lambda +
            (24576 : F[X]) * t2 ^ 2 * b41 -
            (92160 : F[X]) * t2 ^ 2 * a21 * w72 +
            (215040 : F[X]) * t2 ^ 2 * a21 ^ 2 * s21 -
            (25600 : F[X]) * t2 ^ 3 * q52 +
            h * ((32768 : F[X]) * b2 -
              (49152 : F[X]) * w72 * a0 +
              (98304 : F[X]) * a21 * s21 * a0 -
              (153600 : F[X]) * a21 ^ 2 * a0 +
              (69120 : F[X]) * t2 * a1 ^ 2 * Polynomial.C lambda -
              (76800 : F[X]) * t2 ^ 2 * a1 ^ 2 -
              (107520 : F[X]) * t2 ^ 2 * v32 * a1 -
              (241920 : F[X]) * t2 ^ 2 * a21 * a1 *
                Polynomial.C lambda +
              (143360 : F[X]) * t2 ^ 3 * s21 * a1 +
              (403200 : F[X]) * t2 ^ 3 * a21 * a1 +
              (125440 : F[X]) * t2 ^ 3 * a21 * v32 +
              (181440 : F[X]) * t2 ^ 3 * a21 ^ 2 *
                Polynomial.C lambda +
              (26880 : F[X]) * t2 ^ 4 * w72 -
              (161280 : F[X]) * t2 ^ 4 * a21 * s21 -
              (352800 : F[X]) * t2 ^ 4 * a21 ^ 2 +
              h * (-(55296 : F[X]) * a1 * a0 * Polynomial.C lambda -
                (30720 : F[X]) * t2 * a1 * a0 +
                (86016 : F[X]) * t2 * v32 * a0 +
                (138240 : F[X]) * t2 * a21 * a0 * Polynomial.C lambda -
                (122880 : F[X]) * t2 ^ 2 * s21 * a0 -
                (153600 : F[X]) * t2 ^ 2 * a21 * a0 +
                (90720 : F[X]) * t2 ^ 4 * a1 * Polynomial.C lambda -
                (231840 : F[X]) * t2 ^ 5 * a1 -
                (28224 : F[X]) * t2 ^ 5 * v32 -
                (99792 : F[X]) * t2 ^ 5 * a21 * Polynomial.C lambda +
                (29568 : F[X]) * t2 ^ 6 * s21 +
                (258720 : F[X]) * t2 ^ 6 * a21 +
                h * ((61440 : F[X]) * a0 ^ 2 -
                  (80640 : F[X]) * t2 ^ 3 * a0 * Polynomial.C lambda +
                  (201600 : F[X]) * t2 ^ 4 * a0 +
                  (15444 : F[X]) * t2 ^ 7 * Polynomial.C lambda -
                  (45045 : F[X]) * t2 ^ 8))))) := by
  simp only [localClearedEighthDefect410]
  ring

end TenthFaceScalars410

/-! ## Source-facing tenth-face packet -/

section NonzeroTenthFace410

variable {k : Type*} [Field k] [CharZero k]

/-- After the ninth-face collapse, `2 (q₈/h⁷)(a) = 5 (p₂/h)(a)`. -/
theorem tenthFace_s21_from_ninth410 (s21 a21 s1 m1 : k)
    (hs1 : s1 = (2 : k) * s21) (hm1 : m1 = -(4 : k) * a21)
    (hsm : (4 : k) * s1 + (5 : k) * m1 = 0) :
    (2 : k) * s21 = (5 : k) * a21 := by
  have hM : (8 : k) * s21 - (20 : k) * a21 = 0 := by
    rw [hs1, hm1] at hsm
    linear_combination hsm
  exact tenthFace_M_nextOrder410 a21 s21 hM

set_option maxHeartbeats 32000000 in
/-- Finite local tenth-face packet: the collapsed ninth-face jet together
with the next-order identities of the second through sixth and eighth
defects. -/
theorem nonzeroFace410_linearRoot_tenthInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ t2 a21 s21 vis w72 q52 : k[X],
      p.coeff 3 = h0 ^ 3 * t2 ∧ p.coeff 2 = h0 * a21 ∧
        q.coeff 8 = h0 ^ 7 * s21 ∧ q.coeff 7 = h0 ^ 6 * vis ∧
        q.coeff 6 = h0 ^ 4 * w72 ∧ q.coeff 5 = h0 ^ 2 * q52 ∧
        (2 : k) * s21.eval a = (5 : k) * a21.eval a ∧
        q52.eval a = 0 ∧ (q.coeff 4).eval a = 0 ∧
        (8 : k) * w72.eval a = (15 : k) * (a21.eval a) ^ 2 ∧
        a21.eval a = 0 ∧
        h0 ^ 3 ∣ p.coeff 3 ∧ h0 ^ 2 ∣ p.coeff 2 ∧
        h0 ^ 8 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 7 ∧
        h0 ^ 5 ∣ q.coeff 6 ∧ h0 ^ 3 ∣ q.coeff 5 ∧
        h0 ^ 2 ∣ q.coeff 4 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
        (2 : k) * vis.eval a = (5 : k) * (p.coeff 1).eval a := by
  obtain ⟨t1, s2, v3, w7, m1, s1, v1, w1, b1, ht1, hs2, hv3, hw7, hs1, hv1,
    hw1, hb1, hm1, ht1z, ha2z, hb5z, hs2z, hv3z, hw7z, hsm, hv1z, hw1z,
    hb1z, hp3_3, hp2_1, hq8_7, hq7_6, hq6_4, hq5_2, hq9⟩ :=
    nonzeroFace410_linearRoot_ninthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4 hq10 hN hD hroot hlambda
  obtain ⟨t2, ht2⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 t1 a hh0degree hroot ht1z
  obtain ⟨a21, ha21⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 (p.coeff 2) a hh0degree
      hroot ha2z
  obtain ⟨s21, hs21⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 s2 a hh0degree hroot hs2z
  obtain ⟨v11, hv11⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 v1 a hh0degree hroot hv1z
  obtain ⟨w11, hw11⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 w1 a hh0degree hroot hw1z
  obtain ⟨b11, hb11⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 b1 a hh0degree hroot hb1z
  have hp3 : p.coeff 3 = h0 ^ 3 * t2 := by
    calc
      p.coeff 3 = h0 ^ 2 * t1 := ht1
      _ = h0 ^ 2 * (h0 * t2) := by rw [ht2]
      _ = h0 ^ 3 * t2 := by ring
  have hq8 : q.coeff 8 = h0 ^ 7 * s21 := by
    calc
      q.coeff 8 = h0 ^ 6 * s2 := hs2
      _ = h0 ^ 6 * (h0 * s21) := by rw [hs21]
      _ = h0 ^ 7 * s21 := by ring
  have hp2 : p.coeff 2 = h0 * a21 := ha21
  have hs1a : s1.eval a = (2 : k) * s21.eval a := by
    have : ((2 : k[X]) * s2 - (5 : k[X]) * t1 ^ 2).eval a =
        (h0 * s1).eval a := by
      rw [hs1]
    have hform : s1.eval a =
        (2 : k) * s21.eval a - (5 : k) * (t2.eval a) ^ 2 * h0.eval a := by
      have hs1poly :
          s1 = (2 : k[X]) * s21 - (5 : k[X]) * t2 ^ 2 * h0 := by
        apply mul_left_cancel₀ hh0
        calc
          h0 * s1 = (2 : k[X]) * s2 - (5 : k[X]) * t1 ^ 2 := hs1.symm
          _ = (2 : k[X]) * (h0 * s21) - (5 : k[X]) * (h0 * t2) ^ 2 := by
            rw [hs21, ht2]
          _ = h0 * ((2 : k[X]) * s21 - (5 : k[X]) * t2 ^ 2 * h0) := by
            ring
      simpa [hroot, eval_sub, eval_mul, eval_pow] using
        congrArg (fun r : k[X] => r.eval a) hs1poly
    simpa [hroot] using hform
  have hm1a : m1.eval a = -(4 : k) * a21.eval a := by
    have hm1poly :
        m1 = h0 * t2 ^ 2 - (4 : k[X]) * a21 := by
      apply mul_left_cancel₀ hh0
      calc
        h0 * m1 = t1 ^ 2 - (4 : k[X]) * p.coeff 2 := hm1.symm
        _ = (h0 * t2) ^ 2 - (4 : k[X]) * (h0 * a21) := by
          rw [ht2, ha21]
        _ = h0 * (h0 * t2 ^ 2 - (4 : k[X]) * a21) := by ring
    simpa [hroot, eval_sub, eval_mul, eval_pow] using
      congrArg (fun r : k[X] => r.eval a) hm1poly
  have hsrel :=
    tenthFace_s21_from_ninth410 (s21.eval a) (a21.eval a) (s1.eval a)
      (m1.eval a) hs1a hm1a hsm
  have h4ne : (4 : k) ≠ 0 := by norm_num
  have hvis :
      ∃ vis : k[X], q.coeff 7 = h0 ^ 6 * vis := by
    have hform :
        (4 : k[X]) * v3 = h0 * v1 + (5 : k[X]) * t1 ^ 3 := by
      linear_combination hv1
    have h4v :
        (4 : k[X]) * v3 =
          h0 ^ 2 * (v11 + (5 : k[X]) * t2 ^ 3 * h0) := by
      calc
        (4 : k[X]) * v3 = h0 * v1 + (5 : k[X]) * t1 ^ 3 := hform
        _ = h0 * (h0 * v11) + (5 : k[X]) * (h0 * t2) ^ 3 := by
          rw [← hv11, ← ht2]
        _ = h0 ^ 2 * (v11 + (5 : k[X]) * t2 ^ 3 * h0) := by ring
    refine ⟨C (4 : k)⁻¹ * (v11 + (5 : k[X]) * t2 ^ 3 * h0), ?_⟩
    have h4C : (C (4 : k) : k[X]) * C (4 : k)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h4ne, map_one]
    have h4eq : (4 : k[X]) = C (4 : k) :=
      (Polynomial.C_eq_natCast 4).symm
    calc
      q.coeff 7 = h0 ^ 4 * v3 := hv3
      _ = h0 ^ 4 * (C (4 : k)⁻¹ * ((4 : k[X]) * v3)) := by
        calc
          h0 ^ 4 * v3 = h0 ^ 4 * (1 * v3) := by ring
          _ = h0 ^ 4 * ((C (4 : k) * C (4 : k)⁻¹) * v3) := by rw [h4C]
          _ = h0 ^ 4 * (C (4 : k)⁻¹ * (C (4 : k) * v3)) := by ring
          _ = h0 ^ 4 * (C (4 : k)⁻¹ * ((4 : k[X]) * v3)) := by
            rw [h4eq]
      _ = h0 ^ 4 * (C (4 : k)⁻¹ *
            (h0 ^ 2 * (v11 + (5 : k[X]) * t2 ^ 3 * h0))) := by
        rw [h4v]
      _ = h0 ^ 6 * (C (4 : k)⁻¹ * (v11 + (5 : k[X]) * t2 ^ 3 * h0)) := by
        ring
  obtain ⟨vis, hvis⟩ := hvis
  have hw72 :
      ∃ w72 : k[X], q.coeff 6 = h0 ^ 4 * w72 := hq6_4
  obtain ⟨w72, hw72⟩ := hw72
  have hq52 :
      ∃ q52 : k[X], q.coeff 5 = h0 ^ 2 * q52 := hq5_2
  obtain ⟨q52, hq52⟩ := hq52
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
  obtain ⟨eta, hYrel⟩ :=
    nonzeroFace410_eighthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  have hVclr :=
    tenthFace_clearedV_collapsed410 (F := k) h0 t2 a21 s21 vis w72 q52
      (p.coeff 1) (p.coeff 0) lambda
  have hVcof :
      (4096 : k[X]) * q52 +
          h0 * ((-5184 : k[X]) * a21 ^ 2 * Polynomial.C lambda +
            (18432 : k[X]) * t2 * a21 * s21 -
            (11520 : k[X]) * t2 * a21 ^ 2 -
            (8192 : k[X]) * s21 * (p.coeff 1) +
            (23040 : k[X]) * a21 * (p.coeff 1) -
            (7168 : k[X]) * a21 * vis - (6144 : k[X]) * t2 * w72 +
            h0 * ((16848 : k[X]) * t2 ^ 2 * a21 * Polynomial.C lambda -
              (9984 : k[X]) * t2 ^ 3 * s21 -
              (31200 : k[X]) * t2 ^ 3 * a21 -
              (10368 : k[X]) * t2 * (p.coeff 1) * Polynomial.C lambda +
              (14400 : k[X]) * t2 ^ 2 * (p.coeff 1) +
              (8064 : k[X]) * t2 ^ 2 * vis +
              h0 * ((-5967 : k[X]) * t2 ^ 4 * Polynomial.C lambda +
                (15912 : k[X]) * t2 ^ 5 +
                (4608 : k[X]) * (p.coeff 0) * Polynomial.C lambda))) =
        Polynomial.C eps * h0 ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 14 hh0)
    have hsub :
        localClearedFifthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) lambda =
          localClearedFifthDefect410 h0 (h0 ^ 3 * t2) (h0 * a21)
            (p.coeff 1) (p.coeff 0) (h0 ^ 7 * s21) (h0 ^ 6 * vis)
            (h0 ^ 4 * w72) (h0 ^ 2 * q52) lambda := by
      simp [hp3, hp2, hq8, hvis, hw72, hq52]
    rw [← hVclr, ← hsub, hVrel]
    ring
  have hq52z : q52.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hVcof
    have h4096 : (4096 : k) ≠ 0 := by norm_num
    have : (4096 : k) * q52.eval a = 0 := by
      simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub] using heval
    exact (mul_eq_zero.mp this).resolve_left h4096
  have hWclr :=
    tenthFace_clearedW_collapsed410 (F := k) h0 t2 a21 s21 vis w72 q52
      (p.coeff 1) (p.coeff 0) (q.coeff 4) lambda
  have hq4z : (q.coeff 4).eval a = 0 := by
    have hscale :
        localClearedSixthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
          h0 ^ 16 *
            ((2048 : k[X]) * q.coeff 4 +
              h0 * ((4096 : k[X]) * a21 ^ 2 * s21 -
                (5120 : k[X]) * a21 ^ 3 -
                (3072 : k[X]) * a21 * w72 - (2560 : k[X]) * t2 * q52 +
                h0 * ((6912 : k[X]) * t2 * a21 ^ 2 *
                    Polynomial.C lambda -
                  (12288 : k[X]) * t2 ^ 2 * a21 * s21 -
                  (3840 : k[X]) * t2 ^ 2 * a21 ^ 2 -
                  (4608 : k[X]) * a21 * (p.coeff 1) *
                    Polynomial.C lambda +
                  (8192 : k[X]) * t2 * s21 * (p.coeff 1) -
                  (7680 : k[X]) * t2 * a21 * (p.coeff 1) +
                  (7168 : k[X]) * t2 * a21 * vis +
                  (3072 : k[X]) * t2 ^ 2 * w72 +
                  (5120 : k[X]) * (p.coeff 1) ^ 2 -
                  (3584 : k[X]) * vis * (p.coeff 1) +
                  h0 * ((-9216 : k[X]) * t2 ^ 3 * a21 *
                      Polynomial.C lambda +
                    (4096 : k[X]) * t2 ^ 4 * s21 +
                    (20480 : k[X]) * t2 ^ 4 * a21 +
                    (6912 : k[X]) * t2 ^ 2 * (p.coeff 1) *
                      Polynomial.C lambda -
                    (14080 : k[X]) * t2 ^ 3 * (p.coeff 1) -
                    (3584 : k[X]) * t2 ^ 3 * vis -
                    (4096 : k[X]) * s21 * (p.coeff 0) +
                    (10240 : k[X]) * a21 * (p.coeff 0) +
                    h0 * ((2304 : k[X]) * t2 ^ 5 *
                        Polynomial.C lambda -
                      (6400 : k[X]) * t2 ^ 6 -
                      (4608 : k[X]) * t2 * (p.coeff 0) *
                        Polynomial.C lambda +
                      (7680 : k[X]) * t2 ^ 2 * (p.coeff 0)))))) := by
      simpa [hp3, hp2, hq8, hvis, hw72, hq52] using hWclr
    have hcof :
        (2048 : k[X]) * q.coeff 4 +
            h0 * ((4096 : k[X]) * a21 ^ 2 * s21 -
              (5120 : k[X]) * a21 ^ 3 - (3072 : k[X]) * a21 * w72 -
              (2560 : k[X]) * t2 * q52 +
              h0 * ((6912 : k[X]) * t2 * a21 ^ 2 * Polynomial.C lambda -
                (12288 : k[X]) * t2 ^ 2 * a21 * s21 -
                (3840 : k[X]) * t2 ^ 2 * a21 ^ 2 -
                (4608 : k[X]) * a21 * (p.coeff 1) * Polynomial.C lambda +
                (8192 : k[X]) * t2 * s21 * (p.coeff 1) -
                (7680 : k[X]) * t2 * a21 * (p.coeff 1) +
                (7168 : k[X]) * t2 * a21 * vis +
                (3072 : k[X]) * t2 ^ 2 * w72 +
                (5120 : k[X]) * (p.coeff 1) ^ 2 -
                (3584 : k[X]) * vis * (p.coeff 1) +
                h0 * ((-9216 : k[X]) * t2 ^ 3 * a21 *
                    Polynomial.C lambda +
                  (4096 : k[X]) * t2 ^ 4 * s21 +
                  (20480 : k[X]) * t2 ^ 4 * a21 +
                  (6912 : k[X]) * t2 ^ 2 * (p.coeff 1) *
                    Polynomial.C lambda -
                  (14080 : k[X]) * t2 ^ 3 * (p.coeff 1) -
                  (3584 : k[X]) * t2 ^ 3 * vis -
                  (4096 : k[X]) * s21 * (p.coeff 0) +
                  (10240 : k[X]) * a21 * (p.coeff 0) +
                  h0 * ((2304 : k[X]) * t2 ^ 5 * Polynomial.C lambda -
                    (6400 : k[X]) * t2 ^ 6 -
                    (4608 : k[X]) * t2 * (p.coeff 0) *
                      Polynomial.C lambda +
                    (7680 : k[X]) * t2 ^ 2 * (p.coeff 0))))) =
          Polynomial.C zeta * h0 ^ 4 := by
      apply mul_left_cancel₀ (pow_ne_zero 16 hh0)
      rw [← hscale, hWrel]
      ring
    have heval := congrArg (fun r : k[X] => r.eval a) hcof
    have h2048 : (2048 : k) ≠ 0 := by norm_num
    have : (2048 : k) * (q.coeff 4).eval a = 0 := by
      simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub] using heval
    exact (mul_eq_zero.mp this).resolve_left h2048
  obtain ⟨b41, hb41⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 (q.coeff 4) a hh0degree
      hroot hq4z
  have hUclr :=
    tenthFace_clearedU_collapsed410 (F := k) h0 t2 a21 s21 vis w72
      (p.coeff 1) (p.coeff 0) lambda
  have hUeval :
      (128 : k) * w72.eval a - (256 : k) * a21.eval a * s21.eval a +
        (400 : k) * (a21.eval a) ^ 2 = 0 := by
    have hsub :
        localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda =
          h0 ^ 12 * ((128 : k[X]) * w72 - (256 : k[X]) * a21 * s21 +
            (400 : k[X]) * a21 ^ 2 +
            (144 : k[X]) * Polynomial.C lambda * (p.coeff 1) * h0 +
            (80 : k[X]) * t2 * (p.coeff 1) * h0 -
            (224 : k[X]) * t2 * vis * h0 +
            (320 : k[X]) * t2 ^ 2 * s21 * h0 +
            (400 : k[X]) * t2 ^ 2 * a21 * h0 -
            (360 : k[X]) * Polynomial.C lambda * t2 * a21 * h0 +
            (210 : k[X]) * Polynomial.C lambda * t2 ^ 3 * h0 ^ 2 -
            (525 : k[X]) * t2 ^ 4 * h0 ^ 2 -
            (320 : k[X]) * (p.coeff 0) * h0 ^ 2) := by
      simpa [hp3, hp2, hq8, hvis, hw72] using hUclr
    have hcof :
        (128 : k[X]) * w72 - (256 : k[X]) * a21 * s21 +
            (400 : k[X]) * a21 ^ 2 +
            (144 : k[X]) * Polynomial.C lambda * (p.coeff 1) * h0 +
            (80 : k[X]) * t2 * (p.coeff 1) * h0 -
            (224 : k[X]) * t2 * vis * h0 +
            (320 : k[X]) * t2 ^ 2 * s21 * h0 +
            (400 : k[X]) * t2 ^ 2 * a21 * h0 -
            (360 : k[X]) * Polynomial.C lambda * t2 * a21 * h0 +
            (210 : k[X]) * Polynomial.C lambda * t2 ^ 3 * h0 ^ 2 -
            (525 : k[X]) * t2 ^ 4 * h0 ^ 2 -
            (320 : k[X]) * (p.coeff 0) * h0 ^ 2 =
          Polynomial.C delta * h0 ^ 2 := by
      apply mul_left_cancel₀ (pow_ne_zero 12 hh0)
      rw [← hsub, hUrel]
      ring
    have heval := congrArg (fun r : k[X] => r.eval a) hcof
    simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub] using heval
  have hW17eval :
      (4096 : k) * (a21.eval a) ^ 2 * s21.eval a -
          (5120 : k) * (a21.eval a) ^ 3 -
        (3072 : k) * a21.eval a * w72.eval a +
          (2048 : k) * b41.eval a = 0 := by
    have hscale :
        localClearedSixthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
          h0 ^ 16 *
            ((2048 : k[X]) * (h0 * b41) +
              h0 * ((4096 : k[X]) * a21 ^ 2 * s21 -
                (5120 : k[X]) * a21 ^ 3 -
                (3072 : k[X]) * a21 * w72 - (2560 : k[X]) * t2 * q52 +
                h0 * ((6912 : k[X]) * t2 * a21 ^ 2 *
                    Polynomial.C lambda -
                  (12288 : k[X]) * t2 ^ 2 * a21 * s21 -
                  (3840 : k[X]) * t2 ^ 2 * a21 ^ 2 -
                  (4608 : k[X]) * a21 * (p.coeff 1) *
                    Polynomial.C lambda +
                  (8192 : k[X]) * t2 * s21 * (p.coeff 1) -
                  (7680 : k[X]) * t2 * a21 * (p.coeff 1) +
                  (7168 : k[X]) * t2 * a21 * vis +
                  (3072 : k[X]) * t2 ^ 2 * w72 +
                  (5120 : k[X]) * (p.coeff 1) ^ 2 -
                  (3584 : k[X]) * vis * (p.coeff 1) +
                  h0 * ((-9216 : k[X]) * t2 ^ 3 * a21 *
                      Polynomial.C lambda +
                    (4096 : k[X]) * t2 ^ 4 * s21 +
                    (20480 : k[X]) * t2 ^ 4 * a21 +
                    (6912 : k[X]) * t2 ^ 2 * (p.coeff 1) *
                      Polynomial.C lambda -
                    (14080 : k[X]) * t2 ^ 3 * (p.coeff 1) -
                    (3584 : k[X]) * t2 ^ 3 * vis -
                    (4096 : k[X]) * s21 * (p.coeff 0) +
                    (10240 : k[X]) * a21 * (p.coeff 0) +
                    h0 * ((2304 : k[X]) * t2 ^ 5 *
                        Polynomial.C lambda -
                      (6400 : k[X]) * t2 ^ 6 -
                      (4608 : k[X]) * t2 * (p.coeff 0) *
                        Polynomial.C lambda +
                      (7680 : k[X]) * t2 ^ 2 * (p.coeff 0)))))) := by
      simpa [hp3, hp2, hq8, hvis, hw72, hq52, hb41] using hWclr
    have hcof :
        (2048 : k[X]) * b41 +
            ((4096 : k[X]) * a21 ^ 2 * s21 - (5120 : k[X]) * a21 ^ 3 -
              (3072 : k[X]) * a21 * w72 - (2560 : k[X]) * t2 * q52 +
              h0 * ((6912 : k[X]) * t2 * a21 ^ 2 * Polynomial.C lambda -
                (12288 : k[X]) * t2 ^ 2 * a21 * s21 -
                (3840 : k[X]) * t2 ^ 2 * a21 ^ 2 -
                (4608 : k[X]) * a21 * (p.coeff 1) * Polynomial.C lambda +
                (8192 : k[X]) * t2 * s21 * (p.coeff 1) -
                (7680 : k[X]) * t2 * a21 * (p.coeff 1) +
                (7168 : k[X]) * t2 * a21 * vis +
                (3072 : k[X]) * t2 ^ 2 * w72 +
                (5120 : k[X]) * (p.coeff 1) ^ 2 -
                (3584 : k[X]) * vis * (p.coeff 1) +
                h0 * ((-9216 : k[X]) * t2 ^ 3 * a21 *
                    Polynomial.C lambda +
                  (4096 : k[X]) * t2 ^ 4 * s21 +
                  (20480 : k[X]) * t2 ^ 4 * a21 +
                  (6912 : k[X]) * t2 ^ 2 * (p.coeff 1) *
                    Polynomial.C lambda -
                  (14080 : k[X]) * t2 ^ 3 * (p.coeff 1) -
                  (3584 : k[X]) * t2 ^ 3 * vis -
                  (4096 : k[X]) * s21 * (p.coeff 0) +
                  (10240 : k[X]) * a21 * (p.coeff 0) +
                  h0 * ((2304 : k[X]) * t2 ^ 5 * Polynomial.C lambda -
                    (6400 : k[X]) * t2 ^ 6 -
                    (4608 : k[X]) * t2 * (p.coeff 0) *
                      Polynomial.C lambda +
                    (7680 : k[X]) * t2 ^ 2 * (p.coeff 0))))) =
          Polynomial.C zeta * h0 ^ 3 := by
      apply mul_left_cancel₀ (pow_ne_zero 17 hh0)
      have hpow : h0 ^ 16 * (h0 *
            ((2048 : k[X]) * b41 +
              ((4096 : k[X]) * a21 ^ 2 * s21 - (5120 : k[X]) * a21 ^ 3 -
                (3072 : k[X]) * a21 * w72 - (2560 : k[X]) * t2 * q52 +
                h0 * ((6912 : k[X]) * t2 * a21 ^ 2 *
                    Polynomial.C lambda -
                  (12288 : k[X]) * t2 ^ 2 * a21 * s21 -
                  (3840 : k[X]) * t2 ^ 2 * a21 ^ 2 -
                  (4608 : k[X]) * a21 * (p.coeff 1) *
                    Polynomial.C lambda +
                  (8192 : k[X]) * t2 * s21 * (p.coeff 1) -
                  (7680 : k[X]) * t2 * a21 * (p.coeff 1) +
                  (7168 : k[X]) * t2 * a21 * vis +
                  (3072 : k[X]) * t2 ^ 2 * w72 +
                  (5120 : k[X]) * (p.coeff 1) ^ 2 -
                  (3584 : k[X]) * vis * (p.coeff 1) +
                  h0 * ((-9216 : k[X]) * t2 ^ 3 * a21 *
                      Polynomial.C lambda +
                    (4096 : k[X]) * t2 ^ 4 * s21 +
                    (20480 : k[X]) * t2 ^ 4 * a21 +
                    (6912 : k[X]) * t2 ^ 2 * (p.coeff 1) *
                      Polynomial.C lambda -
                    (14080 : k[X]) * t2 ^ 3 * (p.coeff 1) -
                    (3584 : k[X]) * t2 ^ 3 * vis -
                    (4096 : k[X]) * s21 * (p.coeff 0) +
                    (10240 : k[X]) * a21 * (p.coeff 0) +
                    h0 * ((2304 : k[X]) * t2 ^ 5 *
                        Polynomial.C lambda -
                      (6400 : k[X]) * t2 ^ 6 -
                      (4608 : k[X]) * t2 * (p.coeff 0) *
                        Polynomial.C lambda +
                      (7680 : k[X]) * t2 ^ 2 * (p.coeff 0))))))) =
          h0 ^ 17 *
            ((2048 : k[X]) * b41 +
              ((4096 : k[X]) * a21 ^ 2 * s21 - (5120 : k[X]) * a21 ^ 3 -
                (3072 : k[X]) * a21 * w72 - (2560 : k[X]) * t2 * q52 +
                h0 * ((6912 : k[X]) * t2 * a21 ^ 2 *
                    Polynomial.C lambda -
                  (12288 : k[X]) * t2 ^ 2 * a21 * s21 -
                  (3840 : k[X]) * t2 ^ 2 * a21 ^ 2 -
                  (4608 : k[X]) * a21 * (p.coeff 1) *
                    Polynomial.C lambda +
                  (8192 : k[X]) * t2 * s21 * (p.coeff 1) -
                  (7680 : k[X]) * t2 * a21 * (p.coeff 1) +
                  (7168 : k[X]) * t2 * a21 * vis +
                  (3072 : k[X]) * t2 ^ 2 * w72 +
                  (5120 : k[X]) * (p.coeff 1) ^ 2 -
                  (3584 : k[X]) * vis * (p.coeff 1) +
                  h0 * ((-9216 : k[X]) * t2 ^ 3 * a21 *
                      Polynomial.C lambda +
                    (4096 : k[X]) * t2 ^ 4 * s21 +
                    (20480 : k[X]) * t2 ^ 4 * a21 +
                    (6912 : k[X]) * t2 ^ 2 * (p.coeff 1) *
                      Polynomial.C lambda -
                    (14080 : k[X]) * t2 ^ 3 * (p.coeff 1) -
                    (3584 : k[X]) * t2 ^ 3 * vis -
                    (4096 : k[X]) * s21 * (p.coeff 0) +
                    (10240 : k[X]) * a21 * (p.coeff 0) +
                    h0 * ((2304 : k[X]) * t2 ^ 5 *
                        Polynomial.C lambda -
                      (6400 : k[X]) * t2 ^ 6 -
                      (4608 : k[X]) * t2 * (p.coeff 0) *
                        Polynomial.C lambda +
                      (7680 : k[X]) * t2 ^ 2 * (p.coeff 0)))))) := by
        ring
      have hlhs :
          localClearedSixthDefect410 h0 (p.coeff 3) (p.coeff 2)
              (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
              (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
            h0 ^ 16 * (h0 *
              ((2048 : k[X]) * b41 +
                ((4096 : k[X]) * a21 ^ 2 * s21 -
                  (5120 : k[X]) * a21 ^ 3 -
                  (3072 : k[X]) * a21 * w72 -
                  (2560 : k[X]) * t2 * q52 +
                  h0 * ((6912 : k[X]) * t2 * a21 ^ 2 *
                      Polynomial.C lambda -
                    (12288 : k[X]) * t2 ^ 2 * a21 * s21 -
                    (3840 : k[X]) * t2 ^ 2 * a21 ^ 2 -
                    (4608 : k[X]) * a21 * (p.coeff 1) *
                      Polynomial.C lambda +
                    (8192 : k[X]) * t2 * s21 * (p.coeff 1) -
                    (7680 : k[X]) * t2 * a21 * (p.coeff 1) +
                    (7168 : k[X]) * t2 * a21 * vis +
                    (3072 : k[X]) * t2 ^ 2 * w72 +
                    (5120 : k[X]) * (p.coeff 1) ^ 2 -
                    (3584 : k[X]) * vis * (p.coeff 1) +
                    h0 * ((-9216 : k[X]) * t2 ^ 3 * a21 *
                        Polynomial.C lambda +
                      (4096 : k[X]) * t2 ^ 4 * s21 +
                      (20480 : k[X]) * t2 ^ 4 * a21 +
                      (6912 : k[X]) * t2 ^ 2 * (p.coeff 1) *
                        Polynomial.C lambda -
                      (14080 : k[X]) * t2 ^ 3 * (p.coeff 1) -
                      (3584 : k[X]) * t2 ^ 3 * vis -
                      (4096 : k[X]) * s21 * (p.coeff 0) +
                      (10240 : k[X]) * a21 * (p.coeff 0) +
                      h0 * ((2304 : k[X]) * t2 ^ 5 *
                          Polynomial.C lambda -
                        (6400 : k[X]) * t2 ^ 6 -
                        (4608 : k[X]) * t2 * (p.coeff 0) *
                          Polynomial.C lambda +
                        (7680 : k[X]) * t2 ^ 2 * (p.coeff 0))))))) := by
        rw [hscale]
        ring
      rw [← hpow, ← hlhs, hWrel]
      ring
    have heval := congrArg (fun r : k[X] => r.eval a) hcof
    have hraw :
        (2048 : k) * b41.eval a +
            ((4096 : k) * (a21.eval a) ^ 2 * s21.eval a -
              (5120 : k) * (a21.eval a) ^ 3 -
              (3072 : k) * a21.eval a * w72.eval a -
              (2560 : k) * t2.eval a * q52.eval a) = 0 := by
      simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub] using heval
    have hraw' :
        (2048 : k) * b41.eval a +
            ((4096 : k) * (a21.eval a) ^ 2 * s21.eval a -
              (5120 : k) * (a21.eval a) ^ 3 -
              (3072 : k) * a21.eval a * w72.eval a) = 0 := by
      simpa [hq52z, mul_zero, add_zero, sub_zero] using hraw
    linear_combination hraw'
  have hYclr :=
    tenthFace_clearedY_collapsed410 (F := k) h0 t2 a21 s21 vis w72 q52
      (p.coeff 1) (p.coeff 0) b41 (q.coeff 3) (q.coeff 2) lambda
  have hYeval :
      -(40960 : k) * (a21.eval a) ^ 3 * s21.eval a +
          (44800 : k) * (a21.eval a) ^ 4 +
        (36864 : k) * (a21.eval a) ^ 2 * w72.eval a -
          (32768 : k) * a21.eval a * b41.eval a = 0 := by
    have hsub :
        localClearedEighthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) lambda =
          h0 ^ 22 * (-(40960 : k[X]) * q52 * (p.coeff 1) -
              (32768 : k[X]) * a21 * b41 +
              (36864 : k[X]) * a21 ^ 2 * w72 -
              (40960 : k[X]) * a21 ^ 3 * s21 +
              (44800 : k[X]) * a21 ^ 4 +
              (61440 : k[X]) * t2 * a21 * q52 +
              h0 * ((49152 : k[X]) * s21 * (p.coeff 1) ^ 2 -
                (153600 : k[X]) * a21 * (p.coeff 1) ^ 2 +
                (86016 : k[X]) * a21 * vis * (p.coeff 1) +
                (69120 : k[X]) * a21 ^ 2 * (p.coeff 1) *
                  Polynomial.C lambda -
                (24576 : k[X]) * t2 * (q.coeff 3) +
                (73728 : k[X]) * t2 * w72 * (p.coeff 1) -
                (245760 : k[X]) * t2 * a21 * s21 * (p.coeff 1) +
                (192000 : k[X]) * t2 * a21 ^ 2 * (p.coeff 1) -
                (107520 : k[X]) * t2 * a21 ^ 2 * vis -
                (80640 : k[X]) * t2 * a21 ^ 3 * Polynomial.C lambda +
                (24576 : k[X]) * t2 ^ 2 * b41 -
                (92160 : k[X]) * t2 ^ 2 * a21 * w72 +
                (215040 : k[X]) * t2 ^ 2 * a21 ^ 2 * s21 -
                (25600 : k[X]) * t2 ^ 3 * q52 +
                h0 * ((32768 : k[X]) * (q.coeff 2) -
                  (49152 : k[X]) * w72 * (p.coeff 0) +
                  (98304 : k[X]) * a21 * s21 * (p.coeff 0) -
                  (153600 : k[X]) * a21 ^ 2 * (p.coeff 0) +
                  (69120 : k[X]) * t2 * (p.coeff 1) ^ 2 *
                    Polynomial.C lambda -
                  (76800 : k[X]) * t2 ^ 2 * (p.coeff 1) ^ 2 -
                  (107520 : k[X]) * t2 ^ 2 * vis * (p.coeff 1) -
                  (241920 : k[X]) * t2 ^ 2 * a21 * (p.coeff 1) *
                    Polynomial.C lambda +
                  (143360 : k[X]) * t2 ^ 3 * s21 * (p.coeff 1) +
                  (403200 : k[X]) * t2 ^ 3 * a21 * (p.coeff 1) +
                  (125440 : k[X]) * t2 ^ 3 * a21 * vis +
                  (181440 : k[X]) * t2 ^ 3 * a21 ^ 2 *
                    Polynomial.C lambda +
                  (26880 : k[X]) * t2 ^ 4 * w72 -
                  (161280 : k[X]) * t2 ^ 4 * a21 * s21 -
                  (352800 : k[X]) * t2 ^ 4 * a21 ^ 2 +
                  h0 * (-(55296 : k[X]) * (p.coeff 1) * (p.coeff 0) *
                      Polynomial.C lambda -
                    (30720 : k[X]) * t2 * (p.coeff 1) * (p.coeff 0) +
                    (86016 : k[X]) * t2 * vis * (p.coeff 0) +
                    (138240 : k[X]) * t2 * a21 * (p.coeff 0) *
                      Polynomial.C lambda -
                    (122880 : k[X]) * t2 ^ 2 * s21 * (p.coeff 0) -
                    (153600 : k[X]) * t2 ^ 2 * a21 * (p.coeff 0) +
                    (90720 : k[X]) * t2 ^ 4 * (p.coeff 1) *
                      Polynomial.C lambda -
                    (231840 : k[X]) * t2 ^ 5 * (p.coeff 1) -
                    (28224 : k[X]) * t2 ^ 5 * vis -
                    (99792 : k[X]) * t2 ^ 5 * a21 *
                      Polynomial.C lambda +
                    (29568 : k[X]) * t2 ^ 6 * s21 +
                    (258720 : k[X]) * t2 ^ 6 * a21 +
                    h0 * ((61440 : k[X]) * (p.coeff 0) ^ 2 -
                      (80640 : k[X]) * t2 ^ 3 * (p.coeff 0) *
                        Polynomial.C lambda +
                      (201600 : k[X]) * t2 ^ 4 * (p.coeff 0) +
                      (15444 : k[X]) * t2 ^ 7 * Polynomial.C lambda -
                      (45045 : k[X]) * t2 ^ 8))))) := by
      simpa [hp3, hp2, hq8, hvis, hw72, hq52, hb41] using hYclr
    have hcof :
        -(40960 : k[X]) * q52 * (p.coeff 1) -
            (32768 : k[X]) * a21 * b41 +
          (36864 : k[X]) * a21 ^ 2 * w72 -
            (40960 : k[X]) * a21 ^ 3 * s21 +
          (44800 : k[X]) * a21 ^ 4 +
            (61440 : k[X]) * t2 * a21 * q52 +
          h0 * ((49152 : k[X]) * s21 * (p.coeff 1) ^ 2 -
              (153600 : k[X]) * a21 * (p.coeff 1) ^ 2 +
            (86016 : k[X]) * a21 * vis * (p.coeff 1) +
              (69120 : k[X]) * a21 ^ 2 * (p.coeff 1) *
                Polynomial.C lambda -
            (24576 : k[X]) * t2 * (q.coeff 3) +
              (73728 : k[X]) * t2 * w72 * (p.coeff 1) -
            (245760 : k[X]) * t2 * a21 * s21 * (p.coeff 1) +
              (192000 : k[X]) * t2 * a21 ^ 2 * (p.coeff 1) -
            (107520 : k[X]) * t2 * a21 ^ 2 * vis -
              (80640 : k[X]) * t2 * a21 ^ 3 * Polynomial.C lambda +
            (24576 : k[X]) * t2 ^ 2 * b41 -
              (92160 : k[X]) * t2 ^ 2 * a21 * w72 +
            (215040 : k[X]) * t2 ^ 2 * a21 ^ 2 * s21 -
              (25600 : k[X]) * t2 ^ 3 * q52 +
            h0 * ((32768 : k[X]) * (q.coeff 2) -
                (49152 : k[X]) * w72 * (p.coeff 0) +
              (98304 : k[X]) * a21 * s21 * (p.coeff 0) -
                (153600 : k[X]) * a21 ^ 2 * (p.coeff 0) +
              (69120 : k[X]) * t2 * (p.coeff 1) ^ 2 *
                  Polynomial.C lambda -
                (76800 : k[X]) * t2 ^ 2 * (p.coeff 1) ^ 2 -
              (107520 : k[X]) * t2 ^ 2 * vis * (p.coeff 1) -
                (241920 : k[X]) * t2 ^ 2 * a21 * (p.coeff 1) *
                  Polynomial.C lambda +
              (143360 : k[X]) * t2 ^ 3 * s21 * (p.coeff 1) +
                (403200 : k[X]) * t2 ^ 3 * a21 * (p.coeff 1) +
              (125440 : k[X]) * t2 ^ 3 * a21 * vis +
                (181440 : k[X]) * t2 ^ 3 * a21 ^ 2 *
                  Polynomial.C lambda +
              (26880 : k[X]) * t2 ^ 4 * w72 -
                (161280 : k[X]) * t2 ^ 4 * a21 * s21 -
              (352800 : k[X]) * t2 ^ 4 * a21 ^ 2 +
                h0 * (-(55296 : k[X]) * (p.coeff 1) * (p.coeff 0) *
                    Polynomial.C lambda -
                  (30720 : k[X]) * t2 * (p.coeff 1) * (p.coeff 0) +
                  (86016 : k[X]) * t2 * vis * (p.coeff 0) +
                  (138240 : k[X]) * t2 * a21 * (p.coeff 0) *
                    Polynomial.C lambda -
                  (122880 : k[X]) * t2 ^ 2 * s21 * (p.coeff 0) -
                  (153600 : k[X]) * t2 ^ 2 * a21 * (p.coeff 0) +
                  (90720 : k[X]) * t2 ^ 4 * (p.coeff 1) *
                    Polynomial.C lambda -
                  (231840 : k[X]) * t2 ^ 5 * (p.coeff 1) -
                  (28224 : k[X]) * t2 ^ 5 * vis -
                  (99792 : k[X]) * t2 ^ 5 * a21 * Polynomial.C lambda +
                  (29568 : k[X]) * t2 ^ 6 * s21 +
                  (258720 : k[X]) * t2 ^ 6 * a21 +
                  h0 * ((61440 : k[X]) * (p.coeff 0) ^ 2 -
                    (80640 : k[X]) * t2 ^ 3 * (p.coeff 0) *
                      Polynomial.C lambda +
                    (201600 : k[X]) * t2 ^ 4 * (p.coeff 0) +
                    (15444 : k[X]) * t2 ^ 7 * Polynomial.C lambda -
                    (45045 : k[X]) * t2 ^ 8)))) =
          Polynomial.C eta * h0 ^ 4 := by
      apply mul_left_cancel₀ (pow_ne_zero 22 hh0)
      rw [← hsub, hYrel]
      ring
    have heval := congrArg (fun r : k[X] => r.eval a) hcof
    have hraw :
        -(40960 : k) * q52.eval a * (p.coeff 1).eval a -
            (32768 : k) * a21.eval a * b41.eval a +
          (36864 : k) * (a21.eval a) ^ 2 * w72.eval a -
            (40960 : k) * (a21.eval a) ^ 3 * s21.eval a +
          (44800 : k) * (a21.eval a) ^ 4 +
            (61440 : k) * t2.eval a * a21.eval a * q52.eval a = 0 := by
      simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub, eval_neg]
        using heval
    have hraw' :
        -(32768 : k) * a21.eval a * b41.eval a +
            (36864 : k) * (a21.eval a) ^ 2 * w72.eval a -
          (40960 : k) * (a21.eval a) ^ 3 * s21.eval a +
            (44800 : k) * (a21.eval a) ^ 4 = 0 := by
      simpa [hq52z, mul_zero, add_zero, sub_zero, zero_mul] using hraw
    linear_combination hraw'
  have ha21z :=
    tenthFace_Y_a21_zero410 (a21.eval a) (s21.eval a) (w72.eval a)
      (b41.eval a)
      (by
        have : (8 : k) * s21.eval a - (20 : k) * a21.eval a = 0 := by
          linear_combination (4 : k) * hsrel
        exact this)
      hUeval hW17eval hYeval
  have hp2_2 : h0 ^ 2 ∣ p.coeff 2 := by
    obtain ⟨a22, ha22⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_410 h0 a21 a hh0degree hroot
        ha21z
    refine ⟨a22, ?_⟩
    calc
      p.coeff 2 = h0 * a21 := hp2
      _ = h0 * (h0 * a22) := by rw [ha22]
      _ = h0 ^ 2 * a22 := by ring
  have hq8_8 : h0 ^ 8 ∣ q.coeff 8 := by
    have hs21z : s21.eval a = 0 := by
      have h2 : (2 : k) ≠ 0 := by norm_num
      have : (2 : k) * s21.eval a = 0 := by
        rw [hsrel, ha21z, mul_zero]
      exact (mul_eq_zero.mp this).resolve_left h2
    obtain ⟨s22, hs22⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_410 h0 s21 a hh0degree hroot
        hs21z
    refine ⟨s22, ?_⟩
    calc
      q.coeff 8 = h0 ^ 7 * s21 := hq8
      _ = h0 ^ 7 * (h0 * s22) := by rw [hs22]
      _ = h0 ^ 8 * s22 := by ring
  have hq6_5 : h0 ^ 5 ∣ q.coeff 6 := by
    have hwz : w72.eval a = 0 := by
      have h8 : (8 : k) ≠ 0 := by norm_num
      have hw :=
        tenthFace_U_nextOrder410 (a21.eval a) (s21.eval a) (w72.eval a)
          (by
            have : (8 : k) * s21.eval a - (20 : k) * a21.eval a = 0 := by
              linear_combination (4 : k) * hsrel
            exact this)
          hUeval
      have : (8 : k) * w72.eval a = 0 := by
        rw [hw, ha21z]
        ring
      exact (mul_eq_zero.mp this).resolve_left h8
    obtain ⟨w73, hw73⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_410 h0 w72 a hh0degree hroot
        hwz
    refine ⟨w73, ?_⟩
    calc
      q.coeff 6 = h0 ^ 4 * w72 := hw72
      _ = h0 ^ 4 * (h0 * w73) := by rw [hw73]
      _ = h0 ^ 5 * w73 := by ring
  have hq5_3 : h0 ^ 3 ∣ q.coeff 5 := by
    obtain ⟨q53, hq53⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_410 h0 q52 a hh0degree hroot
        hq52z
    refine ⟨q53, ?_⟩
    calc
      q.coeff 5 = h0 ^ 2 * q52 := hq52
      _ = h0 ^ 2 * (h0 * q53) := by rw [hq53]
      _ = h0 ^ 3 * q53 := by ring
  have hq4_2 : h0 ^ 2 ∣ q.coeff 4 := by
    have hbz : b41.eval a = 0 := by
      have h16 : (16 : k) ≠ 0 := by norm_num
      have hb :=
        tenthFace_W17_nextOrder410 (a21.eval a) (s21.eval a)
          (w72.eval a) (b41.eval a)
          (by
            have : (8 : k) * s21.eval a - (20 : k) * a21.eval a = 0 := by
              linear_combination (4 : k) * hsrel
            exact this)
          hUeval hW17eval
      have : (16 : k) * b41.eval a = 0 := by
        rw [hb, ha21z]
        ring
      exact (mul_eq_zero.mp this).resolve_left h16
    obtain ⟨b42, hb42⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_410 h0 b41 a hh0degree hroot
        hbz
    refine ⟨b42, ?_⟩
    calc
      q.coeff 4 = h0 * b41 := hb41
      _ = h0 * (h0 * b42) := by rw [hb42]
      _ = h0 ^ 2 * b42 := by ring
  have hTclr :=
    tenthFace_clearedT_collapsed410 (F := k) h0 t2 a21 s21 vis
      (p.coeff 1) lambda
  have hTeval :
      (64 : k) * vis.eval a - (160 : k) * (p.coeff 1).eval a = 0 := by
    have hsub :
        localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda =
          h0 ^ 10 * ((64 : k[X]) * vis - (160 : k[X]) * p.coeff 1 +
            (72 : k[X]) * Polynomial.C lambda * a21 -
            (128 : k[X]) * t2 * s21 + (80 : k[X]) * t2 * a21 +
            (220 : k[X]) * t2 ^ 3 * h0 -
            (99 : k[X]) * Polynomial.C lambda * t2 ^ 2 * h0) := by
      simpa [hp3, hp2, hq8, hvis] using hTclr
    have hcof :
        (64 : k[X]) * vis - (160 : k[X]) * p.coeff 1 +
            (72 : k[X]) * Polynomial.C lambda * a21 -
            (128 : k[X]) * t2 * s21 + (80 : k[X]) * t2 * a21 +
            (220 : k[X]) * t2 ^ 3 * h0 -
            (99 : k[X]) * Polynomial.C lambda * t2 ^ 2 * h0 =
          Polynomial.C gamma * h0 := by
      apply mul_left_cancel₀ (pow_ne_zero 10 hh0)
      rw [← hsub, hTrel]
      ring
    have heval := congrArg (fun r : k[X] => r.eval a) hcof
    have hraw :
        (64 : k) * vis.eval a - (160 : k) * (p.coeff 1).eval a +
            (72 : k) * lambda * a21.eval a -
          (128 : k) * t2.eval a * s21.eval a +
            (80 : k) * t2.eval a * a21.eval a = 0 := by
      simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub] using heval
    have hs21z : s21.eval a = 0 := by
      have h2 : (2 : k) ≠ 0 := by norm_num
      have : (2 : k) * s21.eval a = 0 := by
        rw [hsrel, ha21z, mul_zero]
      exact (mul_eq_zero.mp this).resolve_left h2
    simpa [ha21z, hs21z, mul_zero, add_zero, sub_zero, zero_mul] using
      hraw
  have hTrel' := tenthFace_T_collapsed410 (vis.eval a) ((p.coeff 1).eval a)
    hTeval
  refine ⟨t2, a21, s21, vis, w72, q52, hp3, hp2, hq8, hvis, hw72, hq52,
    hsrel, hq52z, hq4z,
    tenthFace_U_nextOrder410 (a21.eval a) (s21.eval a) (w72.eval a)
      (by
        have : (8 : k) * s21.eval a - (20 : k) * a21.eval a = 0 := by
          linear_combination (4 : k) * hsrel
        exact this)
      hUeval,
    ha21z, hp3_3, hp2_2, hq8_8, hq7_6, hq6_5, hq5_3, hq4_2, hq9, hTrel'⟩

/-- Source-facing tenth-face packet of a normalized scale-two `(4,10)`
nonzero face: the collapsed ninth-face jet refines at the root of `h`. -/
theorem normalized410ScaleTwo_nonzeroFace_tenthInitialPacket
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
        h0 ^ 3 ∣ p.coeff 3 ∧ h0 ^ 2 ∣ p.coeff 2 ∧
        h0 ^ 8 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 7 ∧
        h0 ^ 5 ∣ q.coeff 6 ∧ h0 ^ 3 ∣ q.coeff 5 ∧
        h0 ^ 2 ∣ q.coeff 4 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
        (p.coeff 2).eval a = 0 ∧ (q.coeff 5).eval a = 0 ∧
        (q.coeff 4).eval a = 0 ∧
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
  obtain ⟨t2, a21, s21, vis, w72, q52, hp3, hp2, hq8, hq7, hq6, hq5, hsrel,
    hq52z, hq4z, hwrel, ha21z, hp3_3, hp2_2, hq8_8, hq7_6, hq6_5, hq5_3,
    hq4_2, hq9, _hT⟩ :=
    nonzeroFace410_linearRoot_tenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot hlambda
  have ha2z : (p.coeff 2).eval a = 0 := by
    have : (p.coeff 2).eval a = h0.eval a * a21.eval a := by
      simpa [eval_mul] using congrArg (fun r : K[X] => r.eval a) hp2
    simpa [hroot] using this
  have hb5z : (q.coeff 5).eval a = 0 := by
    have : (q.coeff 5).eval a = (h0.eval a) ^ 2 * q52.eval a := by
      simpa [eval_mul, eval_pow] using
        congrArg (fun r : K[X] => r.eval a) hq5
    simpa [hroot] using this
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp3_3, hp2_2,
    hq8_8, hq7_6, hq6_5, hq5_3, hq4_2, hq9, ha2z, hb5z, hq4z, hN'⟩

end NonzeroTenthFace410

#print axioms tenthCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_3_monicQuarticDecic
#print axioms iotaResidual410_eq_expanded
#print axioms tenthFace_M_nextOrder410
#print axioms tenthFace_Y_a21_zero410
#print axioms tenthFace_T_collapsed410
#print axioms tenthFace_clearedM_collapsed410
#print axioms tenthFace_clearedY_collapsed410
#print axioms nonzeroFace410_linearRoot_tenthInitialPacket
#print axioms normalized410ScaleTwo_nonzeroFace_tenthInitialPacket

end Max11DegreeRoutes


