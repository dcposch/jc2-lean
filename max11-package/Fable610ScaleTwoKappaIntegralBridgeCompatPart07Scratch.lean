import Fable610ScaleTwoTerminalIntegralClosureScratch

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
