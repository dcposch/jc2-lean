import Fable610ScaleTwoTerminalIntegralClosureScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z¹` coefficient. -/
def terminalDepressedW610 (h r b9 b8 b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  -10 * r ^ 9 + 9 * (b9 / h ^ 9) * r ^ 8 -
    8 * (b8 / h ^ 8) * r ^ 7 + 7 * (b7 / h ^ 7) * r ^ 6 -
    6 * (b6 / h ^ 6) * r ^ 5 + 5 * (b5 / h ^ 5) * r ^ 4 -
    4 * (b4 / h ^ 4) * r ^ 3 + 3 * (b3 / h ^ 3) * r ^ 2 -
    2 * (b2 / h ^ 2) * r + b1 / h

end BridgeKappaDepression610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- First residual of the degree-`6` row.  Equivalent to
`W - (7/6) β E - γ D - (5/6) δ C - (2/3) ε B - (1/2) ζ A
- (10/9) B E - (10/9) C D - (4/9) α B C - (7/72) β B² + (5/81) B³
- (4/9) α A D - (7/36) β A C + (10/27) A B C + (5/72) δ A²
+ (5/27) A² D + (4/27) α A² B + (35/1296) β A³ - (20/243) A³ B
- (3/8) L C² - (3/4) L B D - (3/4) L A E + (3/16) L A B²
+ (3/16) L A² C - (3/128) L A⁴`
on the second- through seventh-face integrals. -/
def bridgeThetaResidual610 (L A B C0 D0 E0 P Q R S0 T0 U0 W0 : F) : F :=
  W0 - (7 / 6 : F) * betaResidual610 L A B Q * E0 -
    gammaResidual610 L A B C0 P R * D0 -
    (5 / 6 : F) * deltaResidual610 L A B C0 D0 P Q S0 * C0 -
    (2 / 3 : F) * epsilonResidual610 L A B C0 D0 E0 P Q R T0 * B -
    (1 / 2 : F) * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 * A -
    (10 / 9 : F) * B * E0 - (10 / 9 : F) * C0 * D0 -
    (4 / 9 : F) * alphaResidual610 A P * B * C0 -
    (7 / 72 : F) * betaResidual610 L A B Q * B ^ 2 +
    (5 / 81 : F) * B ^ 3 -
    (4 / 9 : F) * alphaResidual610 A P * A * D0 -
    (7 / 36 : F) * betaResidual610 L A B Q * A * C0 +
    (10 / 27 : F) * A * B * C0 +
    (5 / 72 : F) * deltaResidual610 L A B C0 D0 P Q S0 * A ^ 2 +
    (5 / 27 : F) * A ^ 2 * D0 +
    (4 / 27 : F) * alphaResidual610 A P * A ^ 2 * B +
    (35 / 1296 : F) * betaResidual610 L A B Q * A ^ 3 -
    (20 / 243 : F) * A ^ 3 * B -
    (3 / 8 : F) * L * C0 ^ 2 -
    (3 / 4 : F) * L * B * D0 -
    (3 / 4 : F) * L * A * E0 +
    (3 / 16 : F) * L * A * B ^ 2 +
    (3 / 16 : F) * L * A ^ 2 * C0 -
    (3 / 128 : F) * L * A ^ 4

end BridgeKappaDepression610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepressedRows610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`6` Jacobian coefficient is
exactly `7 Q E' + 6 R D' + 5 S C' + 4 T B' + 3 U A' - D R' - 2 C S'
- 3 B T' - 4 A U' - 6 W'`. -/
theorem differentialJacobian_coeff_6_monicSexticDecic_bridge
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 6 =
      (7 : F) * g.coeff 7 * d (f.coeff 0) +
        (6 : F) * g.coeff 6 * d (f.coeff 1) +
        (5 : F) * g.coeff 5 * d (f.coeff 2) +
        (4 : F) * g.coeff 4 * d (f.coeff 3) +
        (3 : F) * g.coeff 3 * d (f.coeff 4) -
          (1 : F) * f.coeff 1 * d (g.coeff 6) -
          (2 : F) * f.coeff 2 * d (g.coeff 5) -
          (3 : F) * f.coeff 3 * d (g.coeff 4) -
          (4 : F) * f.coeff 4 * d (g.coeff 3) -
          (6 : F) * d (g.coeff 1) := by
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
  have hmem08 : ((0, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem17 : ((1, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem26 : ((2, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem35 : ((3, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem44 : ((4, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem53 : ((5, 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 6 =
        (7 : F) * g.coeff 7 * d (f.coeff 0) +
          (6 : F) * g.coeff 6 * d (f.coeff 1) +
          (5 : F) * g.coeff 5 * d (f.coeff 2) +
          (4 : F) * g.coeff 4 * d (f.coeff 3) +
          (3 : F) * g.coeff 3 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 6) : ℕ × ℕ) ≠ (1, 5) := by decide
    have hne08_26 : ((0, 6) : ℕ × ℕ) ≠ (2, 4) := by decide
    have hne08_35 : ((0, 6) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne08_44 : ((0, 6) : ℕ × ℕ) ≠ (4, 2) := by decide
    have hne17_26 : ((1, 5) : ℕ × ℕ) ≠ (2, 4) := by decide
    have hne17_35 : ((1, 5) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne17_44 : ((1, 5) : ℕ × ℕ) ≠ (4, 2) := by decide
    have hne26_35 : ((2, 4) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne26_44 : ((2, 4) : ℕ × ℕ) ≠ (4, 2) := by decide
    have hne35_44 : ((3, 3) : ℕ × ℕ) ≠ (4, 2) := by decide
    have hsubset :
        ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2)} : Finset (ℕ × ℕ)) ⊆
          Finset.HasAntidiagonal.antidiagonal (6 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem44
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 6 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 6) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne44 : b ≠ (4, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 5 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne08
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne17
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne26
          ext
          · exact h2
          · omega
        have hne3 : b.1 ≠ 3 := by
          intro h3
          apply hne35
          ext
          · exact h3
          · omega
        have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne44
          ext
          · exact h4
          · omega
        omega
    have hpair :
        (∑ p ∈ ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 2 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_26, hne08_35, hne08_44]),
        Finset.sum_insert (by simp [hne17_26, hne17_35, hne17_44]),
        Finset.sum_insert (by simp [hne26_35, hne26_44]),
        Finset.sum_insert (by simp [hne35_44]), Finset.sum_singleton]
      ring
    have hder6 : g.derivative.coeff 6 = (7 : F) * g.coeff 7 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder6, hder5, hder4, hder3, hder2]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 6 =
        (1 : F) * f.coeff 1 * d (g.coeff 6) +
          (2 : F) * f.coeff 2 * d (g.coeff 5) +
          (3 : F) * f.coeff 3 * d (g.coeff 4) +
          (4 : F) * f.coeff 4 * d (g.coeff 3) +
          (6 : F) * d (g.coeff 1) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 6) : ℕ × ℕ) ≠ (1, 5) := by decide
    have hne08_26 : ((0, 6) : ℕ × ℕ) ≠ (2, 4) := by decide
    have hne08_35 : ((0, 6) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne08_53 : ((0, 6) : ℕ × ℕ) ≠ (5, 1) := by decide
    have hne17_26 : ((1, 5) : ℕ × ℕ) ≠ (2, 4) := by decide
    have hne17_35 : ((1, 5) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne17_53 : ((1, 5) : ℕ × ℕ) ≠ (5, 1) := by decide
    have hne26_35 : ((2, 4) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne26_53 : ((2, 4) : ℕ × ℕ) ≠ (5, 1) := by decide
    have hne35_53 : ((3, 3) : ℕ × ℕ) ≠ (5, 1) := by decide
    have hsubset : ({(0, 6), (1, 5), (2, 4), (3, 3), (5, 1)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (6 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem53
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 6), (1, 5), (2, 4), (3, 3), (5, 1)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 6 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 6) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne53 : b ≠ (5, 1) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h4 : b.1 = 4
        · have hf4 : f.derivative.coeff b.1 = 0 := by
            rw [h4, Polynomial.coeff_derivative, hf5]
            simp
          simp [hf4]
        · have hne0 : b.1 ≠ 0 := by
            intro h0
            apply hne08
            ext
            · exact h0
            · omega
          have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne17
            ext
            · exact h1
            · omega
          have hne2 : b.1 ≠ 2 := by
            intro h2
            apply hne26
            ext
            · exact h2
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne35
            ext
            · exact h3
            · omega
          have hne5 : b.1 ≠ 5 := by
            intro h5
            apply hne53
            ext
            · exact h5
            · omega
          omega
    have hpair :
        (∑ p ∈ ({(0, 6), (1, 5), (2, 4), (3, 3), (5, 1)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 1 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_26, hne08_35, hne08_53]),
        Finset.sum_insert (by simp [hne17_26, hne17_35, hne17_53]),
        Finset.sum_insert (by simp [hne26_35, hne26_53]),
        Finset.sum_insert (by simp [hne35_53]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : f.derivative.coeff 5 = (6 : F) := by
      rw [Polynomial.coeff_derivative, hf6]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder2, hder3, hder5]
    try ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

end BridgeKappaDepressedRows610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepressedRows610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`4` Jacobian coefficient is
exactly `5 S E' + 4 T D' + 3 U C' + 2 V B' + W A' - D T' - 2 C U'
- 3 B V' - 4 A W'`. -/
theorem differentialJacobian_coeff_4_monicSexticDecic_bridge
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 4 =
      (5 : F) * g.coeff 5 * d (f.coeff 0) +
        (4 : F) * g.coeff 4 * d (f.coeff 1) +
        (3 : F) * g.coeff 3 * d (f.coeff 2) +
        (2 : F) * g.coeff 2 * d (f.coeff 3) +
        (1 : F) * g.coeff 1 * d (f.coeff 4) -
          (1 : F) * f.coeff 1 * d (g.coeff 4) -
          (2 : F) * f.coeff 2 * d (g.coeff 3) -
          (3 : F) * f.coeff 3 * d (g.coeff 2) -
          (4 : F) * f.coeff 4 * d (g.coeff 1) := by
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
  have hmem04 : ((0, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem13 : ((1, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem22 : ((2, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem31 : ((3, 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem40 : ((4, 0) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 4 =
        (5 : F) * g.coeff 5 * d (f.coeff 0) +
          (4 : F) * g.coeff 4 * d (f.coeff 1) +
          (3 : F) * g.coeff 3 * d (f.coeff 2) +
          (2 : F) * g.coeff 2 * d (f.coeff 3) +
          (1 : F) * g.coeff 1 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne04_13 : ((0, 4) : ℕ × ℕ) ≠ (1, 3) := by decide
    have hne04_22 : ((0, 4) : ℕ × ℕ) ≠ (2, 2) := by decide
    have hne04_31 : ((0, 4) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne04_40 : ((0, 4) : ℕ × ℕ) ≠ (4, 0) := by decide
    have hne13_22 : ((1, 3) : ℕ × ℕ) ≠ (2, 2) := by decide
    have hne13_31 : ((1, 3) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne13_40 : ((1, 3) : ℕ × ℕ) ≠ (4, 0) := by decide
    have hne22_31 : ((2, 2) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne22_40 : ((2, 2) : ℕ × ℕ) ≠ (4, 0) := by decide
    have hne31_40 : ((3, 1) : ℕ × ℕ) ≠ (4, 0) := by decide
    have hsubset :
        ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)) ⊆
          Finset.HasAntidiagonal.antidiagonal (4 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem04
      · subst b; exact hmem13
      · subst b; exact hmem22
      · subst b; exact hmem31
      · subst b; exact hmem40
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)),
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
      have hne31 : b ≠ (3, 1) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne40 : b ≠ (4, 0) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 5 ≤ b.1
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
        have hne3 : b.1 ≠ 3 := by
          intro h3
          apply hne31
          ext
          · exact h3
          · omega
        have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne40
          ext
          · exact h4
          · omega
        omega
    have hpair :
        (∑ p ∈ ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne04_13, hne04_22, hne04_31, hne04_40]),
        Finset.sum_insert (by simp [hne13_22, hne13_31, hne13_40]),
        Finset.sum_insert (by simp [hne22_31, hne22_40]),
        Finset.sum_insert (by simp [hne31_40]), Finset.sum_singleton]
      ring
    have hder4g : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3g : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2g : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0g : g.derivative.coeff 0 = (1 : F) * g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder4g, hder3g, hder2g, hder1g, hder0g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 4 =
        (1 : F) * f.coeff 1 * d (g.coeff 4) +
          (2 : F) * f.coeff 2 * d (g.coeff 3) +
          (3 : F) * f.coeff 3 * d (g.coeff 2) +
          (4 : F) * f.coeff 4 * d (g.coeff 1) := by
    rw [Polynomial.coeff_mul]
    have hne04_13 : ((0, 4) : ℕ × ℕ) ≠ (1, 3) := by decide
    have hne04_22 : ((0, 4) : ℕ × ℕ) ≠ (2, 2) := by decide
    have hne04_31 : ((0, 4) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne13_22 : ((1, 3) : ℕ × ℕ) ≠ (2, 2) := by decide
    have hne13_31 : ((1, 3) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne22_31 : ((2, 2) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hsubset : ({(0, 4), (1, 3), (2, 2), (3, 1)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (4 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb
      · subst b; exact hmem04
      · subst b; exact hmem13
      · subst b; exact hmem22
      · subst b; exact hmem31
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 4), (1, 3), (2, 2), (3, 1)} : Finset (ℕ × ℕ)),
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
      have hne22 : b ≠ (2, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne31 : b ≠ (3, 1) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h4 : b.1 = 4
        · have hf4 : f.derivative.coeff b.1 = 0 := by
            rw [h4, Polynomial.coeff_derivative, hf5]
            simp
          simp [hf4]
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
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne31
            ext
            · exact h3
            · omega
          omega
    have hpair :
        (∑ p ∈ ({(0, 4), (1, 3), (2, 2), (3, 1)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 1 := by
      rw [Finset.sum_insert (by simp [hne04_13, hne04_22, hne04_31]),
        Finset.sum_insert (by simp [hne13_22, hne13_31]),
        Finset.sum_insert (by simp [hne22_31]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder0, hder1, hder2, hder3]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

end BridgeKappaDepressedRows610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaAffineDecic610

variable {k : Type*} [Field k] [CharZero k]

theorem affineDepress_degreeTen_coeff1_610_bridge
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 1 =
      -10 * r ^ 9 + 9 * (p.coeff 9 / h ^ 9) * r ^ 8 -
        8 * (p.coeff 8 / h ^ 8) * r ^ 7 +
        7 * (p.coeff 7 / h ^ 7) * r ^ 6 -
        6 * (p.coeff 6 / h ^ 6) * r ^ 5 +
        5 * (p.coeff 5 / h ^ 5) * r ^ 4 -
        4 * (p.coeff 4 / h ^ 4) * r ^ 3 +
        3 * (p.coeff 3 / h ^ 3) * r ^ 2 -
        2 * (p.coeff 2 / h ^ 2) * r + p.coeff 1 / h := by
  let plow : (RatFunc k)[X] :=
    p - Polynomial.C (p.coeff 10) * Polynomial.X ^ 10 - Polynomial.C (p.coeff 9) * Polynomial.X ^ 9 -
      Polynomial.C (p.coeff 8) * Polynomial.X ^ 8 - Polynomial.C (p.coeff 7) * Polynomial.X ^ 7 -
      Polynomial.C (p.coeff 6) * Polynomial.X ^ 6 - Polynomial.C (p.coeff 5) * Polynomial.X ^ 5 -
      Polynomial.C (p.coeff 4) * Polynomial.X ^ 4 - Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 -
      Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 - Polynomial.C (p.coeff 1) * Polynomial.X ^ 1
  have hplow : ∀ n, 1 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h1 | hlt1
    · subst n; simp
    · have : 2 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h2 | hlt2
      · subst n; simp
      · have : 3 ≤ n := by omega
        rcases Nat.eq_or_lt_of_le this with h3 | hlt3
        · subst n; simp
        · have : 4 ≤ n := by omega
          rcases Nat.eq_or_lt_of_le this with h4 | hlt4
          · subst n; simp
          · have : 5 ≤ n := by omega
            rcases Nat.eq_or_lt_of_le this with h5 | hlt5
            · subst n; simp
            · have : 6 ≤ n := by omega
              rcases Nat.eq_or_lt_of_le this with h6 | hlt6
              · subst n; simp
              · have : 7 ≤ n := by omega
                rcases Nat.eq_or_lt_of_le this with h7 | hlt7
                · subst n; simp
                · have : 8 ≤ n := by omega
                  rcases Nat.eq_or_lt_of_le this with h8 | hlt8
                  · subst n; simp
                  · have : 9 ≤ n := by omega
                    rcases Nat.eq_or_lt_of_le this with h9 | hlt9
                    · subst n; simp
                    · have : 10 ≤ n := by omega
                      rcases Nat.eq_or_lt_of_le this with h10 | hlt10
                      · subst n; simp [hp10]
                      · simp [hp_high n (by omega), show n ≠ 10 by omega,
                          show n ≠ 9 by omega, show n ≠ 8 by omega,
                          show n ≠ 7 by omega, show n ≠ 6 by omega,
                          show n ≠ 5 by omega, show n ≠ 4 by omega,
                          show n ≠ 3 by omega, show n ≠ 2 by omega,
                          show n ≠ 1 by omega]
  have hplowDeg : plow.natDegree ≤ 0 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = Polynomial.C (p.coeff 10) * Polynomial.X ^ 10 + Polynomial.C (p.coeff 9) * Polynomial.X ^ 9 +
        Polynomial.C (p.coeff 8) * Polynomial.X ^ 8 + Polynomial.C (p.coeff 7) * Polynomial.X ^ 7 +
        Polynomial.C (p.coeff 6) * Polynomial.X ^ 6 + Polynomial.C (p.coeff 5) * Polynomial.X ^ 5 +
        Polynomial.C (p.coeff 4) * Polynomial.X ^ 4 + Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 +
        Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X ^ 1 + plow := by
    simp only [plow]; ring
  have hq :
      affineDepress68 h r p =
        (Polynomial.C (p.coeff 10) * Polynomial.X ^ 10).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 9) * Polynomial.X ^ 9).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 8) * Polynomial.X ^ 8).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 7) * Polynomial.X ^ 7).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 6) * Polynomial.X ^ 6).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 5) * Polynomial.X ^ 5).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 4) * Polynomial.X ^ 4).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 3) * Polynomial.X ^ 3).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 2) * Polynomial.X ^ 2).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 1) * Polynomial.X ^ 1).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) := rfl
    have hsum (A B D E G H I J K M s t : (RatFunc k)[X]) :
        (A + B + D + E + G + H + I + J + K + M + s).comp t =
          A.comp t + B.comp t + D.comp t + E.comp t + G.comp t +
            H.comp t + I.comp t + J.comp t + K.comp t + M.comp t + s.comp t := by
      have h1 : (A + B + D + E + G + H + I + J + K + M + s).comp t =
          (A + B + D + E + G + H + I + J + K + M).comp t + s.comp t :=
        Polynomial.add_comp
      have h2 : (A + B + D + E + G + H + I + J + K + M).comp t =
          (A + B + D + E + G + H + I + J + K).comp t + M.comp t :=
        Polynomial.add_comp
      have h3 : (A + B + D + E + G + H + I + J + K).comp t =
          (A + B + D + E + G + H + I + J).comp t + K.comp t :=
        Polynomial.add_comp
      have h4 : (A + B + D + E + G + H + I + J).comp t =
          (A + B + D + E + G + H + I).comp t + J.comp t :=
        Polynomial.add_comp
      have h5 : (A + B + D + E + G + H + I).comp t =
          (A + B + D + E + G + H).comp t + I.comp t :=
        Polynomial.add_comp
      have h6 : (A + B + D + E + G + H).comp t =
          (A + B + D + E + G).comp t + H.comp t := Polynomial.add_comp
      have h7 : (A + B + D + E + G).comp t =
          (A + B + D + E).comp t + G.comp t := Polynomial.add_comp
      have h8 : (A + B + D + E).comp t =
          (A + B + D).comp t + E.comp t := Polynomial.add_comp
      have h9 : (A + B + D).comp t =
          (A + B).comp t + D.comp t := Polynomial.add_comp
      have h10 : (A + B).comp t = A.comp t + B.comp t := Polynomial.add_comp
      rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    exact hdef.trans ((congrArg (fun t => t.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _ _ _ _ _ _))
  have hlow (n : ℕ) (hn : 1 ≤ n) :
      (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).natDegree ≤
          plow.natDegree * ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹).natDegree ≤ 0 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).natDegree ≤ 0 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 1 ≤ n))
  have h10_1 :
      ((Polynomial.C (p.coeff 10) * Polynomial.X ^ 10).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        -10 * r ^ 9 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 1 hh]
    have hle : (1 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 1 = 10 := by decide
    simp only [hle, ite_true, hp10, hbin]
    field_simp [hh]; ring
  have h9_1 :
      ((Polynomial.C (p.coeff 9) * Polynomial.X ^ 9).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        9 * (p.coeff 9 / h ^ 9) * r ^ 8 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 1 hh]
    have hle : (1 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 1 = 9 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h8_1 :
      ((Polynomial.C (p.coeff 8) * Polynomial.X ^ 8).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        -8 * (p.coeff 8 / h ^ 8) * r ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 1 hh]
    have hle : (1 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 1 = 8 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h7_1 :
      ((Polynomial.C (p.coeff 7) * Polynomial.X ^ 7).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        7 * (p.coeff 7 / h ^ 7) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 1 hh]
    have hle : (1 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 1 = 7 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h6_1 :
      ((Polynomial.C (p.coeff 6) * Polynomial.X ^ 6).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        -6 * (p.coeff 6 / h ^ 6) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 1 hh]
    have hle : (1 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 1 = 6 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h5_1 :
      ((Polynomial.C (p.coeff 5) * Polynomial.X ^ 5).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        5 * (p.coeff 5 / h ^ 5) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 1 hh]
    have hle : (1 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 1 = 5 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h4_1 :
      ((Polynomial.C (p.coeff 4) * Polynomial.X ^ 4).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        -4 * (p.coeff 4 / h ^ 4) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 1 hh]
    have hle : (1 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 1 = 4 := by decide
    simp only [hle, ite_true, hbin, pow_three]
    field_simp [hh]; ring
  have h3_1 :
      ((Polynomial.C (p.coeff 3) * Polynomial.X ^ 3).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        3 * (p.coeff 3 / h ^ 3) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 3) h r 3 1 hh]
    have hle : (1 : ℕ) ≤ 3 := by omega
    have hbin : (3 : ℕ).choose 1 = 3 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]; ring
  have h2_1 :
      ((Polynomial.C (p.coeff 2) * Polynomial.X ^ 2).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        -2 * (p.coeff 2 / h ^ 2) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 2) h r 2 1 hh]
    have hle : (1 : ℕ) ≤ 2 := by omega
    have hbin : (2 : ℕ).choose 1 = 2 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]; ring
  have h1_1 :
      ((Polynomial.C (p.coeff 1) * Polynomial.X ^ 1).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        p.coeff 1 / h := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 1) h r 1 1 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  rw [hq, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, h10_1, h9_1, h8_1, h7_1, h6_1, h5_1, h4_1, h3_1,
    h2_1, h1_1, hlow 1 (by omega)]
  ring

end BridgeKappaAffineDecic610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaJet610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 40000000 in
/-- Tail of the jet-substituted cleared `κ` defect above order `h⁴⁹`. -/
def bridgeKappaJetTail610
    (hh w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 lam : R) : R :=
    (1884529152000 : R) * w1 ^ 2 * p31 ^ 3
    - (4749013463040 : R) * w1 ^ 2 * p31 ^ 2 * u1
    + (1915568455680 : R) * w1 ^ 2 * p31 * q4
    + (15830044876800 : R) * w1 * a41 ^ 2 * p31 ^ 2
    - (9498026926080 : R) * w1 * a41 ^ 2 * p31 * u1
    + (1915568455680 : R) * w1 * a41 ^ 2 * q4
    - (10854887915520 : R) * w1 * a41 * p31 ^ 2 * s1
    + (4788921139200 : R) * w1 * a41 * p31 * q52
    + (2873352683520 : R) * w1 * p31 ^ 2 * b62
    - (6385228185600 : R) * w1 * p31 ^ 2 * p2
    + (6704489594880 : R) * w1 * p31 * u1 * p2
    - (2089711042560 : R) * w1 * p2 * q4
    + (4334417049600 : R) * a41 ^ 4 * p31
    - (791502243840 : R) * a41 ^ 4 * u1
    - (3618295971840 : R) * a41 ^ 3 * p31 * s1
    + (798153523200 : R) * a41 ^ 3 * q52
    + (2873352683520 : R) * a41 ^ 2 * p31 * b62
    - (13568609894400 : R) * a41 ^ 2 * p31 * p2
    + (3352244797440 : R) * a41 ^ 2 * u1 * p2
    + (7662273822720 : R) * a41 * p31 * s1 * p2
    - (2612138803200 : R) * a41 * q52 * p2
    - (3134566563840 : R) * p31 * b62 * p2
    + (4788921139200 : R) * p31 * p2 ^ 2
    - (1828497162240 : R) * u1 * p2 ^ 2
    + (1356860989440 : R) * lam * w1 * p31 ^ 3
    + (2035291484160 : R) * lam * a41 ^ 2 * p31 ^ 2
    - (1436676341760 : R) * lam * p31 ^ 2 * p2
    - (2889611366400 : R) * hh * w1 ^ 3 * a41 * p31 ^ 2
    + (12136367738880 : R) * hh * w1 ^ 3 * a41 * p31 * u1
    - (1809147985920 : R) * hh * w1 ^ 3 * a41 * q4
    + (6935067279360 : R) * hh * w1 ^ 3 * p31 ^ 2 * s1
    - (2261434982400 : R) * hh * w1 ^ 3 * p31 * q52
    - (15892862515200 : R) * hh * w1 ^ 2 * a41 ^ 3 * p31
    + (6068183869440 : R) * hh * w1 ^ 2 * a41 ^ 3 * u1
    + (20805201838080 : R) * hh * w1 ^ 2 * a41 ^ 2 * p31 * s1
    - (3392152473600 : R) * hh * w1 ^ 2 * a41 ^ 2 * q52
    - (8141165936640 : R) * hh * w1 ^ 2 * a41 * p31 * b62
    + (11307174912000 : R) * hh * w1 ^ 2 * a41 * p31 * p2
    - (9498026926080 : R) * hh * w1 ^ 2 * a41 * u1 * p2
    - (10854887915520 : R) * hh * w1 ^ 2 * p31 * s1 * p2
    + (2394460569600 : R) * hh * w1 ^ 2 * q52 * p2
    - (2889611366400 : R) * hh * w1 * a41 ^ 5
    + (3467533639680 : R) * hh * w1 * a41 ^ 4 * s1
    - (2713721978880 : R) * hh * w1 * a41 ^ 3 * b62
    + (10553363251200 : R) * hh * w1 * a41 ^ 3 * p2
    - (10854887915520 : R) * hh * w1 * a41 ^ 2 * s1 * p2
    + (5746705367040 : R) * hh * w1 * a41 * b62 * p2
    - (6385228185600 : R) * hh * w1 * a41 * p2 ^ 2
    - (1567283281920 : R) * hh * w1 * p31 * q3
    + (3831136911360 : R) * hh * w1 * s1 * p2 ^ 2
    - (783641640960 : R) * hh * a41 ^ 2 * q3
    + (4788921139200 : R) * hh * p31 ^ 2 * p1
    - (3656994324480 : R) * hh * p31 * u1 * p1
    + (1880739938304 : R) * hh * p2 * q3
    + (2507653251072 : R) * hh * p1 * q4
    - (7801950689280 : R) * hh * lam * w1 ^ 2 * a41 * p31 ^ 2
    - (5201300459520 : R) * hh * lam * w1 * a41 ^ 3 * p31
    + (8141165936640 : R) * hh * lam * w1 * a41 * p31 * p2
    - (260065022976 : R) * hh * lam * a41 ^ 5
    + (1356860989440 : R) * hh * lam * a41 ^ 3 * p2
    - (1436676341760 : R) * hh * lam * a41 * p2 ^ 2
    - (3491613734400 : R) * hh ^ 2 * w1 ^ 5 * p31 ^ 2
    - (2932955536896 : R) * hh ^ 2 * w1 ^ 5 * p31 * u1
    + (346753363968 : R) * hh ^ 2 * w1 ^ 5 * q4
    - (1745806867200 : R) * hh ^ 2 * w1 ^ 4 * a41 ^ 2 * p31
    - (7332388842240 : R) * hh ^ 2 * w1 ^ 4 * a41 ^ 2 * u1
    - (16759745925120 : R) * hh ^ 2 * w1 ^ 4 * a41 * p31 * s1
    + (2167208524800 : R) * hh ^ 2 * w1 ^ 4 * a41 * q52
    + (2600650229760 : R) * hh ^ 2 * w1 ^ 4 * p31 * b62
    + (5056819891200 : R) * hh ^ 2 * w1 ^ 4 * p31 * p2
    + (3034091934720 : R) * hh ^ 2 * w1 ^ 4 * u1 * p2
    + (4655484979200 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 4
    - (11173163950080 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 3 * s1
    + (5201300459520 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 2 * b62
    - (2889611366400 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 2 * p2
    + (13870134558720 : R) * hh ^ 2 * w1 ^ 3 * a41 * s1 * p2
    - (2713721978880 : R) * hh ^ 2 * w1 ^ 3 * b62 * p2
    - (1507623321600 : R) * hh ^ 2 * w1 ^ 3 * p2 ^ 2
    + (1436676341760 : R) * hh ^ 2 * w1 ^ 2 * a41 * q3
    - (12770456371200 : R) * hh ^ 2 * w1 * a41 * p31 * p1
    + (6704489594880 : R) * hh ^ 2 * w1 * a41 * u1 * p1
    + (7662273822720 : R) * hh ^ 2 * w1 * p31 * s1 * p1
    - (2612138803200 : R) * hh ^ 2 * w1 * q52 * p1
    - (4522869964800 : R) * hh ^ 2 * a41 ^ 3 * p1
    + (3831136911360 : R) * hh ^ 2 * a41 ^ 2 * s1 * p1
    - (3134566563840 : R) * hh ^ 2 * a41 * b62 * p1
    + (9577842278400 : R) * hh ^ 2 * a41 * p2 * p1
    + (1253826625536 : R) * hh ^ 2 * p31 * q2
    - (4179422085120 : R) * hh ^ 2 * s1 * p2 * p1
    + (3142452360960 : R) * hh ^ 2 * lam * w1 ^ 4 * p31 ^ 2
    + (12569809443840 : R) * hh ^ 2 * lam * w1 ^ 3 * a41 ^ 2 * p31
    - (5201300459520 : R) * hh ^ 2 * lam * w1 ^ 3 * p31 * p2
    + (3142452360960 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 ^ 4
    - (7801950689280 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 ^ 2 * p2
    + (2035291484160 : R) * hh ^ 2 * lam * w1 ^ 2 * p2 ^ 2
    - (2873352683520 : R) * hh ^ 2 * lam * a41 * p31 * p1
    + (8826023606400 : R) * hh ^ 3 * w1 ^ 6 * a41 * p31
    + (2851484549760 : R) * hh ^ 3 * w1 ^ 6 * a41 * u1
    + (3258839485440 : R) * hh ^ 3 * w1 ^ 6 * p31 * s1
    - (349161373440 : R) * hh ^ 3 * w1 ^ 6 * q52
    + (2715699571200 : R) * hh ^ 3 * w1 ^ 5 * a41 ^ 3
    + (9776518456320 : R) * hh ^ 3 * w1 ^ 5 * a41 ^ 2 * s1
    - (2513961888768 : R) * hh ^ 3 * w1 ^ 5 * a41 * b62
    - (6983227468800 : R) * hh ^ 3 * w1 ^ 5 * a41 * p2
    - (3351949185024 : R) * hh ^ 3 * w1 ^ 5 * s1 * p2
    - (339215247360 : R) * hh ^ 3 * w1 ^ 4 * q3
    - (3015246643200 : R) * hh ^ 3 * w1 ^ 3 * p31 * p1
    - (3166008975360 : R) * hh ^ 3 * w1 ^ 3 * u1 * p1
    + (5653587456000 : R) * hh ^ 3 * w1 ^ 2 * a41 ^ 2 * p1
    - (10854887915520 : R) * hh ^ 3 * w1 ^ 2 * a41 * s1 * p1
    + (2873352683520 : R) * hh ^ 3 * w1 ^ 2 * b62 * p1
    + (798153523200 : R) * hh ^ 3 * w1 ^ 2 * p2 * p1
    - (1044855521280 : R) * hh ^ 3 * w1 * a41 * q2
    + (9577842278400 : R) * hh ^ 3 * a41 * p31 * p0
    - (3656994324480 : R) * hh ^ 3 * a41 * u1 * p0
    - (4179422085120 : R) * hh ^ 3 * p31 * s1 * p0
    + (3134566563840 : R) * hh ^ 3 * q52 * p0
    - (7332388842240 : R) * hh ^ 3 * lam * w1 ^ 5 * a41 * p31
    - (6110324035200 : R) * hh ^ 3 * lam * w1 ^ 4 * a41 ^ 3
    + (6284904721920 : R) * hh ^ 3 * lam * w1 ^ 4 * a41 * p2
    + (4070582968320 : R) * hh ^ 3 * lam * w1 ^ 2 * p31 * p1
    + (4070582968320 : R) * hh ^ 3 * lam * w1 * a41 ^ 2 * p1
    - (2873352683520 : R) * hh ^ 3 * lam * w1 * p2 * p1
    - (2071125045000 : R) * hh ^ 4 * w1 ^ 8 * p31
    - (347949007560 : R) * hh ^ 4 * w1 ^ 8 * u1
    - (5302080115200 : R) * hh ^ 4 * w1 ^ 7 * a41 ^ 2
    - (3181248069120 : R) * hh ^ 4 * w1 ^ 7 * a41 * s1
    + (349161373440 : R) * hh ^ 4 * w1 ^ 7 * b62
    + (2133763948800 : R) * hh ^ 4 * w1 ^ 7 * p2
    + (5056819891200 : R) * hh ^ 4 * w1 ^ 4 * a41 * p1
    + (3467533639680 : R) * hh ^ 4 * w1 ^ 4 * s1 * p1
    + (319261409280 : R) * hh ^ 4 * w1 ^ 3 * q2
    + (798153523200 : R) * hh ^ 4 * w1 ^ 2 * p31 * p0
    + (3352244797440 : R) * hh ^ 4 * w1 ^ 2 * u1 * p0
    - (6385228185600 : R) * hh ^ 4 * w1 * a41 ^ 2 * p0
    + (7662273822720 : R) * hh ^ 4 * w1 * a41 * s1 * p0
    - (3134566563840 : R) * hh ^ 4 * w1 * b62 * p0
    + (1741425868800 : R) * hh ^ 4 * w1 * p2 * p0
    + (870712934400 : R) * hh ^ 4 * w1 * p1 ^ 2
    + (626913312768 : R) * hh ^ 4 * a41 * q1
    + (1192968025920 : R) * hh ^ 4 * lam * w1 ^ 7 * p31
    + (4175388090720 : R) * hh ^ 4 * lam * w1 ^ 6 * a41 ^ 2
    - (1222064807040 : R) * hh ^ 4 * lam * w1 ^ 6 * p2
    - (5201300459520 : R) * hh ^ 4 * lam * w1 ^ 3 * a41 * p1
    - (2873352683520 : R) * hh ^ 4 * lam * w1 * p31 * p0
    - (1436676341760 : R) * hh ^ 4 * lam * a41 ^ 2 * p0
    + (1567283281920 : R) * hh ^ 4 * lam * p2 * p0
    + (783641640960 : R) * hh ^ 4 * lam * p1 ^ 2
    + (2018963377200 : R) * hh ^ 5 * w1 ^ 9 * a41
    + (346108007520 : R) * hh ^ 5 * w1 ^ 9 * s1
    - (2211355365120 : R) * hh ^ 5 * w1 ^ 6 * p1
    - (3015246643200 : R) * hh ^ 5 * w1 ^ 3 * a41 * p0
    - (3618295971840 : R) * hh ^ 5 * w1 ^ 3 * s1 * p0
    - (261213880320 : R) * hh ^ 5 * w1 ^ 2 * q1
    - (5224277606400 : R) * hh ^ 5 * p1 * p0
    - (1168114525380 : R) * hh ^ 5 * lam * w1 ^ 8 * a41
    + (1256980944384 : R) * hh ^ 5 * lam * w1 ^ 5 * p1
    + (4070582968320 : R) * hh ^ 5 * lam * w1 ^ 2 * a41 * p0
    - (231612681800 : R) * hh ^ 6 * w1 ^ 11
    + (2311689093120 : R) * hh ^ 6 * w1 ^ 5 * p0
    + (114648277491 : R) * hh ^ 6 * lam * w1 ^ 10
    - (1300325114880 : R) * hh ^ 6 * lam * w1 ^ 4 * p0

end BridgeKappaJet610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the `p₃₁ ≠ 0` complement child the factored root relation
forces `a₄₁ = 0`, the retained core forces `w₁ = 0`, and the two
remaining ground relations collapse to the pins `80 p₂ = 9 λ p₃₁` and
`16 b₆₂ = -5 λ p₃₁`. -/
theorem bridgeKappa_complement_pins610
    (w1 a41 p31 p2 b62 lam : F) (hnz : p31 ≠ 0)
    (hzero : a41 * p31 ^ 3 = 0)
    (hcore : (5 : F) * a41 ^ 2 + (2 : F) * p31 * w1 = 0)
    (hp2n : (80 : F) * p2 - (9 : F) * lam * p31 -
      (8 : F) * p31 * w1 = 0)
    (hb62n : (144 : F) * b62 + (45 : F) * lam * p31 -
      (152 : F) * p31 * w1 = 0) :
    a41 = 0 ∧ w1 = 0 ∧ (80 : F) * p2 = (9 : F) * lam * p31 ∧
      (16 : F) * b62 = -(5 : F) * lam * p31 := by
  have ha : a41 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (pow_ne_zero 3 hnz)
  have hpw : p31 * w1 = 0 := by
    linear_combination (1 / 2 : F) * hcore - (5 / 2 : F) * a41 * ha
  have hw : w1 = 0 := by
    rcases mul_eq_zero.mp hpw with h | h
    · exact absurd h hnz
    · exact h
  refine ⟨ha, hw, ?_, ?_⟩
  · linear_combination hp2n + (8 : F) * p31 * hw
  · linear_combination (1 / 9 : F) * hb62n + (152 / 9 : F) * p31 * hw

end BridgeKappaScalars610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- Exact denominator clearing for the decic `z¹` coordinate on the
ninth-power face. -/
theorem terminalDepressedW610_eq_cleared
    (h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    terminalDepressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3
        b2 b1 =
      (40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
          144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
          3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
          93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
          1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44) /
        (5038848 * h ^ 45) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h5038848 : (5038848 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [terminalDepressedW610, sexticDepressionR610, sexticDepressionR68]
  have hrewrite :
      -10 * (a5 / (6 * h ^ 5)) ^ 9 +
          9 * (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 8 -
        8 * (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) ^ 7 +
          7 * (b7 / h ^ 7) * (a5 / (6 * h ^ 5)) ^ 6 -
        6 * (b6 / h ^ 6) * (a5 / (6 * h ^ 5)) ^ 5 +
          5 * (b5 / h ^ 5) * (a5 / (6 * h ^ 5)) ^ 4 -
        4 * (b4 / h ^ 4) * (a5 / (6 * h ^ 5)) ^ 3 +
          3 * (b3 / h ^ 3) * (a5 / (6 * h ^ 5)) ^ 2 -
        2 * (b2 / h ^ 2) * (a5 / (6 * h ^ 5)) + b1 / h =
        (40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
            144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
            3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
            93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
            1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44) /
          (5038848 * h ^ 45) := by
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh45, h5038848]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh45, h5038848]
    ring
  exact hrewrite

end BridgeKappaDepression610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- First residual of the degree-`4` row.  Equivalent to
`(1/6) A θ + (1/3) B η + (1/2) C ζ - (1/8) A² ζ + (2/3) D ε
- (2/9) A B ε + (5/6) E δ + (35/1296) A³ δ - (5/36) A C δ
- (5/72) B² δ + (20/243) A³ B α - (4/27) A² D α - (8/27) A B C α
- (4/81) B³ α + (4/9) B E α + (4/9) C D α + (385/31104) A⁴ β
- (35/432) A² C β - (35/432) A B² β + (7/36) A E β + (7/36) B D β
+ (7/72) C² β - (3/256) L A⁵ + (3/32) L A³ C + (9/64) L A² B²
- (3/16) L A² E - (3/8) L A B D - (3/16) L A C² - (3/16) L B² C
+ (3/4) L C E + (3/8) L D² - (35/729) A⁴ B + (20/243) A³ D
+ (20/81) A² B C + (20/243) A B³ - (10/27) A B E - (10/27) A C D
- (5/27) B² D - (5/27) B C² + (10/9) D E`
on the second- through ninth-face integrals. -/
def bridgeKappaResidual610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 6 : F) * A * bridgeThetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0 +
    (1 / 3 : F) * B * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 +
    (1 / 2 : F) * C0 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 -
    (1 / 8 : F) * A ^ 2 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 +
    (2 / 3 : F) * D0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 -
    (2 / 9 : F) * A * B * epsilonResidual610 L A B C0 D0 E0 P Q R T0 +
    (5 / 6 : F) * E0 * deltaResidual610 L A B C0 D0 P Q S0 +
    (35 / 1296 : F) * A ^ 3 * deltaResidual610 L A B C0 D0 P Q S0 -
    (5 / 36 : F) * A * C0 * deltaResidual610 L A B C0 D0 P Q S0 -
    (5 / 72 : F) * B ^ 2 * deltaResidual610 L A B C0 D0 P Q S0 +
    (20 / 243 : F) * A ^ 3 * B * alphaResidual610 A P -
    (4 / 27 : F) * A ^ 2 * D0 * alphaResidual610 A P -
    (8 / 27 : F) * A * B * C0 * alphaResidual610 A P -
    (4 / 81 : F) * B ^ 3 * alphaResidual610 A P +
    (4 / 9 : F) * B * E0 * alphaResidual610 A P +
    (4 / 9 : F) * C0 * D0 * alphaResidual610 A P +
    (385 / 31104 : F) * A ^ 4 * betaResidual610 L A B Q -
    (35 / 432 : F) * A ^ 2 * C0 * betaResidual610 L A B Q -
    (35 / 432 : F) * A * B ^ 2 * betaResidual610 L A B Q +
    (7 / 36 : F) * A * E0 * betaResidual610 L A B Q +
    (7 / 36 : F) * B * D0 * betaResidual610 L A B Q +
    (7 / 72 : F) * C0 ^ 2 * betaResidual610 L A B Q -
    (3 / 256 : F) * L * A ^ 5 +
    (3 / 32 : F) * L * A ^ 3 * C0 +
    (9 / 64 : F) * L * A ^ 2 * B ^ 2 -
    (3 / 16 : F) * L * A ^ 2 * E0 -
    (3 / 8 : F) * L * A * B * D0 -
    (3 / 16 : F) * L * A * C0 ^ 2 -
    (3 / 16 : F) * L * B ^ 2 * C0 +
    (3 / 4 : F) * L * C0 * E0 +
    (3 / 8 : F) * L * D0 ^ 2 -
    (35 / 729 : F) * A ^ 4 * B +
    (20 / 243 : F) * A ^ 3 * D0 +
    (20 / 81 : F) * A ^ 2 * B * C0 +
    (20 / 243 : F) * A * B ^ 3 -
    (10 / 27 : F) * A * B * E0 -
    (10 / 27 : F) * A * C0 * D0 -
    (5 / 27 : F) * B ^ 2 * D0 -
    (5 / 27 : F) * B * C0 ^ 2 +
    (10 / 9 : F) * D0 * E0

end BridgeKappaDepression610

end Max11DegreeRoutes
