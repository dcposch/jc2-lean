import Fable610ScaleTwoTerminalIntegralClosureScratch

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
