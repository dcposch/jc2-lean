import Fable810ScaleTwoSeventeenthFinalRowScratch
import Grok810ScaleZeroEighthDefectScratch

/-! # Terminal integral bridge for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the seventeenth final-row packet exhausts the
Jacobian coefficient tower: the degree-`0` row is the Keller constant
`W G' - F X' = j` and there is no unused row below it.  The remaining
mechanism on this face is clearing an isolated first integral.  Among
the uncleared degree-`5` through degree-`1` first integrals only the
degree-`5` integral `μ` admits an exact construction — it is isolated
on the tracked second- through ninth-face residuals `α, …, η` — so it
is the lowest, most constrained choice.

This file constructs `μ` for the scale-two lane and derives its exact
literal-source `h`-adic clearing: `d μ = 0` on the depressed rows of
degree `8`, `7`, and `5` (`terminalMuResidual810_deriv_zero`),
`17179869184 h⁸⁴ μ` is the explicit weight-`84` polynomial numerator
`terminalClearedMuDefect810`, and on the literal source the cleared
defect is a ground constant times `h₀⁸⁴`
(`nonzeroFace810_terminalMuPowerRelation`).  The `μ` ground constant
`eta` joins `δ, ε, ζ, η` and is not cleared to zero.

Combining the clearing with the seventeenth-face jet
`p₇ = h₀⁶ t₀`, `p₆ = h₀⁴ v₁`, `p₅ = h₀² u₁`, `q₈ = h₀⁶ s₁`,
`q₇ = h₀⁴ w₁`, `q₆ = h₀² b₆₂` factors the numerator through `h₀⁷²`,
twelve orders below the defect weight: the peeled power relation is
`head + h₀ · tail = C eta · h₀¹²`, so the order-`72` head vanishes at
the root of `h₀` on every live branch — a genuinely new relation the
row tower never reached.  On the left branch the head reduces, modulo
the second/third-defect reductions and the `Gred`/`Vred` loads, to an
exact degree-`12` relation on `(t₀, v₁, u₁, b₆₂)` alone
(`bridgeMuLeftResidual810`).  On the right branch the head collapses
the entire local jet: on the `u₁ = 0` sibling a `v₁³`-multiple of the
head reduces to `786432000 v₁⁹` and on the complementary factor to
`5767168000 v₁⁶`, forcing `v₁(a) = 0` on both, and in cascade
`u₁(a) = b₆₂(a) = p₄(a) = s₁(a) = w₁(a) = q₅(a) = 0` together with
the divisibility upgrades `h₀⁵ ∣ p₆`, `h₀³ ∣ p₅`, `h₀⁷ ∣ q₈`,
`h₀⁵ ∣ q₇`, `h₀³ ∣ q₆`, `h₀ ∣ p₄`, and `h₀ ∣ q₅`.  This is the first
individual vanishing of `v₁, u₁, a₄` on this lane.

No branch is genuinely inconsistent, so none is closed: the left
`F₁ ∨ F₂` alternative survives carrying the new degree-`12` residual,
and both right sub-branches survive with the collapsed zero jet — the
Keller boundary relation `G'(a) W(a) - F(a) X'(a) = j ≠ 0` lives on
`p₀, p₁, q₀, q₁`, which the collapse does not touch.  The ground
constants `δ, ε, ζ, η, eta` stay uncleared, and the aligned face
`N = 0` remains open.  The next mechanism is either the aligned face
or driving the right-branch zero jet into the retained sibling and
complementary witness laws (`σ, ρ, π, k_z, ω, β, ρ_c`) at the next
`h`-order.

The degree-`8` depressed row lemma and the `z¹` decic clearing are
reused from the imported scale-zero eighth-defect scratch; the
degree-`7` and degree-`5` row lemmas and the `μ` machinery are
restated here for the scale-two chain with `_bridge`/`terminal` names
to keep both chains importable.  `d μ = 0` needs no constancy of the
degree-`8`/`7` integrals — only the rows themselves.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Degree-`7` depressed Jacobian coefficient -/

section DepressedRow810BridgeSeven

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]



/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`7` Jacobian coefficient is
exactly `8 P G' + 7 Q F' + 6 R E' + 5 S D' + 4 T C' + 3 U B' + 2 V A'
- F Q' - 2 E R' - 3 D S' - 4 C T' - 5 B U' - 6 A V' - 8 X'`. -/
theorem differentialJacobian_coeff_7_monicOcticDecic_bridge
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 7 =
      (8 : F) * g.coeff 8 * d (f.coeff 0) +
        (7 : F) * g.coeff 7 * d (f.coeff 1) +
        (6 : F) * g.coeff 6 * d (f.coeff 2) +
        (5 : F) * g.coeff 5 * d (f.coeff 3) +
        (4 : F) * g.coeff 4 * d (f.coeff 4) +
        (3 : F) * g.coeff 3 * d (f.coeff 5) +
        (2 : F) * g.coeff 2 * d (f.coeff 6) -
          f.coeff 1 * d (g.coeff 7) -
          (2 : F) * f.coeff 2 * d (g.coeff 6) -
          (3 : F) * f.coeff 3 * d (g.coeff 5) -
          (4 : F) * f.coeff 4 * d (g.coeff 4) -
          (5 : F) * f.coeff 5 * d (g.coeff 3) -
          (6 : F) * f.coeff 6 * d (g.coeff 2) -
          (8 : F) * d (g.coeff 0) := by
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
  have hmem07 : ((0, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem16 : ((1, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem25 : ((2, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem34 : ((3, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem43 : ((4, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem52 : ((5, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem61 : ((6, 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem70 : ((7, 0) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 7 =
        (8 : F) * g.coeff 8 * d (f.coeff 0) +
          (7 : F) * g.coeff 7 * d (f.coeff 1) +
          (6 : F) * g.coeff 6 * d (f.coeff 2) +
          (5 : F) * g.coeff 5 * d (f.coeff 3) +
          (4 : F) * g.coeff 4 * d (f.coeff 4) +
          (3 : F) * g.coeff 3 * d (f.coeff 5) +
          (2 : F) * g.coeff 2 * d (f.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne07_16 : ((0, 7) : ℕ × ℕ) ≠ (1, 6) := by decide
    have hne07_25 : ((0, 7) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne07_34 : ((0, 7) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne07_43 : ((0, 7) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne07_52 : ((0, 7) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne07_61 : ((0, 7) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hne16_25 : ((1, 6) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne16_34 : ((1, 6) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne16_43 : ((1, 6) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne16_52 : ((1, 6) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne16_61 : ((1, 6) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hne25_34 : ((2, 5) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne25_43 : ((2, 5) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne25_52 : ((2, 5) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne25_61 : ((2, 5) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hne34_43 : ((3, 4) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne34_52 : ((3, 4) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne34_61 : ((3, 4) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hne43_52 : ((4, 3) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne43_61 : ((4, 3) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hne52_61 : ((5, 2) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hsubset :
        ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1)} :
            Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (7 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb | hb | hb
      · subst b; exact hmem07
      · subst b; exact hmem16
      · subst b; exact hmem25
      · subst b; exact hmem34
      · subst b; exact hmem43
      · subst b; exact hmem52
      · subst b; exact hmem61
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2),
              (6, 1)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 7 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 7) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne44 : b ≠ (4, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne53 : b ≠ (5, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne62 : b ≠ (6, 1) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 7 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0; apply hne08; ext; exact h0; omega
        have hne1 : b.1 ≠ 1 := by
          intro h1; apply hne17; ext; exact h1; omega
        have hne2 : b.1 ≠ 2 := by
          intro h2; apply hne26; ext; exact h2; omega
        have hne3 : b.1 ≠ 3 := by
          intro h3; apply hne35; ext; exact h3; omega
        have hne4 : b.1 ≠ 4 := by
          intro h4; apply hne44; ext; exact h4; omega
        have hne5 : b.1 ≠ 5 := by
          intro h5; apply hne53; ext; exact h5; omega
        have hne6 : b.1 ≠ 6 := by
          intro h6; apply hne62; ext; exact h6; omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2),
            (6, 1)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 5 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 6 * g.derivative.coeff 1 := by
      rw [Finset.sum_insert (by simp [hne07_16, hne07_25, hne07_34, hne07_43,
            hne07_52, hne07_61]),
        Finset.sum_insert (by simp [hne16_25, hne16_34, hne16_43, hne16_52,
            hne16_61]),
        Finset.sum_insert (by simp [hne25_34, hne25_43, hne25_52, hne25_61]),
        Finset.sum_insert (by simp [hne34_43, hne34_52, hne34_61]),
        Finset.sum_insert (by simp [hne43_52, hne43_61]),
        Finset.sum_insert (by simp [hne52_61]), Finset.sum_singleton]
      ring
    have hder7 : g.derivative.coeff 7 = (8 : F) * g.coeff 8 := by
      rw [Polynomial.coeff_derivative]
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
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder7, hder6, hder5,
      hder4, hder3, hder2, hder1g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 7 =
        f.coeff 1 * d (g.coeff 7) +
          (2 : F) * f.coeff 2 * d (g.coeff 6) +
          (3 : F) * f.coeff 3 * d (g.coeff 5) +
          (4 : F) * f.coeff 4 * d (g.coeff 4) +
          (5 : F) * f.coeff 5 * d (g.coeff 3) +
          (6 : F) * f.coeff 6 * d (g.coeff 2) +
          (8 : F) * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul]
    have hne07_16 : ((0, 7) : ℕ × ℕ) ≠ (1, 6) := by decide
    have hne07_25 : ((0, 7) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne07_34 : ((0, 7) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne07_43 : ((0, 7) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne07_52 : ((0, 7) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne07_70 : ((0, 7) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hne16_25 : ((1, 6) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne16_34 : ((1, 6) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne16_43 : ((1, 6) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne16_52 : ((1, 6) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne16_70 : ((1, 6) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hne25_34 : ((2, 5) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne25_43 : ((2, 5) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne25_52 : ((2, 5) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne25_70 : ((2, 5) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hne34_43 : ((3, 4) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne34_52 : ((3, 4) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne34_70 : ((3, 4) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hne43_52 : ((4, 3) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne43_70 : ((4, 3) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hne52_70 : ((5, 2) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hsubset :
        ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (7, 0)} :
            Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (7 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb | hb | hb
      · subst b; exact hmem07
      · subst b; exact hmem16
      · subst b; exact hmem25
      · subst b; exact hmem34
      · subst b; exact hmem43
      · subst b; exact hmem52
      · subst b; exact hmem70
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2),
              (7, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 7 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 7) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne44 : b ≠ (4, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne53 : b ≠ (5, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne71 : b ≠ (7, 0) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 8 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h6 : b.1 = 6
        · have hf6 : f.derivative.coeff b.1 = 0 := by
            rw [h6, Polynomial.coeff_derivative, hf7]
            simp
          simp [hf6]
        · have hne0 : b.1 ≠ 0 := by
            intro h0; apply hne08; ext; exact h0; omega
          have hne1 : b.1 ≠ 1 := by
            intro h1; apply hne17; ext; exact h1; omega
          have hne2 : b.1 ≠ 2 := by
            intro h2; apply hne26; ext; exact h2; omega
          have hne3 : b.1 ≠ 3 := by
            intro h3; apply hne35; ext; exact h3; omega
          have hne4 : b.1 ≠ 4 := by
            intro h4; apply hne44; ext; exact h4; omega
          have hne5 : b.1 ≠ 5 := by
            intro h5; apply hne53; ext; exact h5; omega
          have hne7 : b.1 ≠ 7 := by
            intro h7; apply hne71; ext; exact h7; omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2),
            (7, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 4 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 7 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne07_16, hne07_25, hne07_34, hne07_43,
            hne07_52, hne07_70]),
        Finset.sum_insert (by simp [hne16_25, hne16_34, hne16_43, hne16_52,
            hne16_70]),
        Finset.sum_insert (by simp [hne25_34, hne25_43, hne25_52, hne25_70]),
        Finset.sum_insert (by simp [hne34_43, hne34_52, hne34_70]),
        Finset.sum_insert (by simp [hne43_52, hne43_70]),
        Finset.sum_insert (by simp [hne52_70]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]
      simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder4 : f.derivative.coeff 4 = (5 : F) * f.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : f.derivative.coeff 5 = (6 : F) * f.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder7 : f.derivative.coeff 7 = (8 : F) := by
      rw [Polynomial.coeff_derivative, hf8]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder0, hder1, hder2,
      hder3, hder4, hder5, hder7]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

end DepressedRow810BridgeSeven

/-! ## The degree-`5` first integral `μ` and its weight-`84` clearing -/

section BridgeMuResidual810

variable {F : Type*} [Field F] [CharZero F]

/-- First residual of the degree-`5` row. -/
def terminalMuResidual810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 8 : F) * W0 * B
    - (1 / 8 : F) * alphaResidual810 A P * B * F0
    + (1 / 4 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * C0
    - (3 / 32 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * A ^ 2
    + (3 / 8 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * D0
    - (9 / 32 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * A * B
    + (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * E0
    + (1 / 16 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A ^ 3
    - (1 / 4 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A * C0
    - (3 / 16 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * B ^ 2
    + (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * F0
    + (45 / 256 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A ^ 2 * B
    - (15 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * D0
    - (5 / 16 : F) * deltaResidual810 L A B C0 D0 P Q S0 * B * C0
    + (3 / 4 : F) * gammaResidual810 L A B C0 P R * G0
    - (45 / 2048 : F) * gammaResidual810 L A B C0 P R * A ^ 4
    + (15 / 128 : F) * gammaResidual810 L A B C0 P R * A ^ 2 * C0
    + (9 / 64 : F) * gammaResidual810 L A B C0 P R * A * B ^ 2
    - (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * E0
    - (9 / 32 : F) * gammaResidual810 L A B C0 P R * B * D0
    - (3 / 32 : F) * gammaResidual810 L A B C0 P R * C0 ^ 2
    - (189 / 4096 : F) * betaResidual810 L A B Q * A ^ 3 * B
    + (63 / 1024 : F) * betaResidual810 L A B Q * A ^ 2 * D0
    + (35 / 256 : F) * betaResidual810 L A B Q * A * B * C0
    - (7 / 64 : F) * betaResidual810 L A B Q * A * F0
    + (7 / 256 : F) * betaResidual810 L A B Q * B ^ 3
    - (7 / 32 : F) * betaResidual810 L A B Q * B * E0
    - (7 / 64 : F) * betaResidual810 L A B Q * C0 * D0
    - (945 / 32768 : F) * L * A ^ 4 * B
    + (315 / 8192 : F) * L * A ^ 3 * D0
    + (63 / 512 : F) * L * A ^ 2 * B * C0
    - (63 / 1024 : F) * L * A ^ 2 * F0
    + (189 / 4096 : F) * L * A * B ^ 3
    - (9 / 64 : F) * L * A * B * E0
    - (63 / 512 : F) * L * A * C0 * D0
    - (81 / 1024 : F) * L * B ^ 2 * D0
    - (9 / 128 : F) * L * B * C0 ^ 2
    + (9 / 64 : F) * L * C0 * F0
    + (9 / 64 : F) * L * D0 * E0
    + (385 / 65536 : F) * A ^ 6
    - (385 / 8192 : F) * A ^ 4 * C0
    - (105 / 1024 : F) * A ^ 3 * B ^ 2
    + (35 / 512 : F) * A ^ 3 * E0
    + (225 / 1024 : F) * A ^ 2 * B * D0
    + (105 / 1024 : F) * A ^ 2 * C0 ^ 2
    - (15 / 128 : F) * A ^ 2 * G0
    + (15 / 64 : F) * A * B ^ 2 * C0
    - (35 / 128 : F) * A * B * F0
    - (15 / 64 : F) * A * C0 * E0
    - (15 / 128 : F) * A * D0 ^ 2
    + (45 / 2048 : F) * B ^ 4
    - (5 / 32 : F) * B ^ 2 * E0
    - (35 / 128 : F) * B * C0 * D0
    - (5 / 128 : F) * C0 ^ 3
    + (5 / 16 : F) * C0 * G0
    + (5 / 16 : F) * D0 * F0
    + (5 / 32 : F) * E0 ^ 2

set_option maxHeartbeats 4000000 in
/-- Polynomial numerator of `17179869184 h⁸⁴ μ` on the ninth-power face. -/
def terminalClearedMuDefect810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
    (203408205 : F[X]) * a7 ^ 12
    - (801115392 : F[X]) * h ^ 6 * a7 ^ 10 * b8
    - (199709874 : F[X]) * h ^ 7 * a7 ^ 11 * Polynomial.C lambda
    - (1502091360 : F[X]) * h ^ 8 * a7 ^ 10 * a6
    + (801115392 : F[X]) * h ^ 14 * a7 ^ 9 * b7
    + (8240044032 : F[X]) * h ^ 14 * a7 ^ 8 * a6 * b8
    + (2253137040 : F[X]) * h ^ 15 * a7 ^ 9 * a6 * Polynomial.C lambda
    + (1573619520 : F[X]) * h ^ 16 * a7 ^ 9 * a5
    + (1287506880 : F[X]) * h ^ 16 * a7 ^ 8 * a6 ^ 2
    - (797423616 : F[X]) * h ^ 22 * a7 ^ 8 * b6
    - (7442620416 : F[X]) * h ^ 22 * a7 ^ 7 * a6 * b7
    - (8505851904 : F[X]) * h ^ 22 * a7 ^ 7 * a5 * b8
    - (29770481664 : F[X]) * h ^ 22 * a7 ^ 6 * a6 ^ 2 * b8
    - (2317512384 : F[X]) * h ^ 23 * a7 ^ 8 * a5 * Polynomial.C lambda
    - (9270049536 : F[X]) * h ^ 23 * a7 ^ 7 * a6 ^ 2 * Polynomial.C lambda
    - (1661299200 : F[X]) * h ^ 24 * a7 ^ 8 * a4
    - (1329039360 : F[X]) * h ^ 24 * a7 ^ 7 * a6 * a5
    + (12404367360 : F[X]) * h ^ 24 * a7 ^ 6 * a6 ^ 3
    + (787578880 : F[X]) * h ^ 30 * a7 ^ 7 * b5
    + (6615662592 : F[X]) * h ^ 30 * a7 ^ 6 * a6 * b6
    + (7718273024 : F[X]) * h ^ 30 * a7 ^ 6 * a5 * b7
    + (8820883456 : F[X]) * h ^ 30 * a7 ^ 6 * a4 * b8
    + (23154819072 : F[X]) * h ^ 30 * a7 ^ 5 * a6 ^ 2 * b7
    + (52925300736 : F[X]) * h ^ 30 * a7 ^ 5 * a6 * a5 * b8
    + (44104417280 : F[X]) * h ^ 30 * a7 ^ 4 * a6 ^ 3 * b8
    + (2392270848 : F[X]) * h ^ 31 * a7 ^ 7 * a4 * Polynomial.C lambda
    + (16745895936 : F[X]) * h ^ 31 * a7 ^ 6 * a6 * a5 * Polynomial.C lambda
    + (16745895936 : F[X]) * h ^ 31 * a7 ^ 5 * a6 ^ 3 * Polynomial.C lambda
    + (1772052480 : F[X]) * h ^ 32 * a7 ^ 7 * a3
    - (37213102080 : F[X]) * h ^ 32 * a7 ^ 5 * a6 ^ 2 * a5
    - (31010918400 : F[X]) * h ^ 32 * a7 ^ 4 * a6 ^ 4
    - (767033344 : F[X]) * h ^ 38 * a7 ^ 6 * b4
    - (5752750080 : F[X]) * h ^ 38 * a7 ^ 5 * a6 * b5
    - (6903300096 : F[X]) * h ^ 38 * a7 ^ 5 * a5 * b6
    - (8053850112 : F[X]) * h ^ 38 * a7 ^ 5 * a4 * b7
    - (9204400128 : F[X]) * h ^ 38 * a7 ^ 5 * a3 * b8
    - (17258250240 : F[X]) * h ^ 38 * a7 ^ 4 * a6 ^ 2 * b6
    - (40269250560 : F[X]) * h ^ 38 * a7 ^ 4 * a6 * a5 * b7
    - (46022000640 : F[X]) * h ^ 38 * a7 ^ 4 * a6 * a4 * b8
    - (23011000320 : F[X]) * h ^ 38 * a7 ^ 4 * a5 ^ 2 * b8
    - (26846167040 : F[X]) * h ^ 38 * a7 ^ 3 * a6 ^ 3 * b7
    - (92044001280 : F[X]) * h ^ 38 * a7 ^ 3 * a6 ^ 2 * a5 * b8
    - (23011000320 : F[X]) * h ^ 38 * a7 ^ 2 * a6 ^ 4 * b8
    - (2480873472 : F[X]) * h ^ 39 * a7 ^ 6 * a3 * Polynomial.C lambda
    - (14885240832 : F[X]) * h ^ 39 * a7 ^ 5 * a6 * a4 * Polynomial.C lambda
    - (7442620416 : F[X]) * h ^ 39 * a7 ^ 5 * a5 ^ 2 * Polynomial.C lambda
    - (37213102080 : F[X]) * h ^ 39 * a7 ^ 4 * a6 ^ 2 * a5 * Polynomial.C lambda
    - (12404367360 : F[X]) * h ^ 39 * a7 ^ 3 * a6 ^ 4 * Polynomial.C lambda
    - (1917583360 : F[X]) * h ^ 40 * a7 ^ 6 * a2
    + (1438187520 : F[X]) * h ^ 40 * a7 ^ 5 * a6 * a3
    + (1438187520 : F[X]) * h ^ 40 * a7 ^ 5 * a5 * a4
    + (35954688000 : F[X]) * h ^ 40 * a7 ^ 4 * a6 ^ 2 * a4
    + (35954688000 : F[X]) * h ^ 40 * a7 ^ 4 * a6 * a5 ^ 2
    + (91085209600 : F[X]) * h ^ 40 * a7 ^ 3 * a6 ^ 3 * a5
    + (20134625280 : F[X]) * h ^ 40 * a7 ^ 2 * a6 ^ 5
    + (726663168 : F[X]) * h ^ 46 * a7 ^ 5 * b3
    + (4844421120 : F[X]) * h ^ 46 * a7 ^ 4 * a6 * b4
    + (6055526400 : F[X]) * h ^ 46 * a7 ^ 4 * a5 * b5
    + (7266631680 : F[X]) * h ^ 46 * a7 ^ 4 * a4 * b6
    + (8477736960 : F[X]) * h ^ 46 * a7 ^ 4 * a3 * b7
    + (9688842240 : F[X]) * h ^ 46 * a7 ^ 4 * a2 * b8
    + (12111052800 : F[X]) * h ^ 46 * a7 ^ 3 * a6 ^ 2 * b5
    + (29066526720 : F[X]) * h ^ 46 * a7 ^ 3 * a6 * a5 * b6
    + (33910947840 : F[X]) * h ^ 46 * a7 ^ 3 * a6 * a4 * b7
    + (38755368960 : F[X]) * h ^ 46 * a7 ^ 3 * a6 * a3 * b8
    + (16955473920 : F[X]) * h ^ 46 * a7 ^ 3 * a5 ^ 2 * b7
    + (38755368960 : F[X]) * h ^ 46 * a7 ^ 3 * a5 * a4 * b8
    + (14533263360 : F[X]) * h ^ 46 * a7 ^ 2 * a6 ^ 3 * b6
    + (50866421760 : F[X]) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * a5 * b7
    + (58133053440 : F[X]) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * a4 * b8
    + (58133053440 : F[X]) * h ^ 46 * a7 ^ 2 * a6 * a5 ^ 2 * b8
    + (8477736960 : F[X]) * h ^ 46 * a7 * a6 ^ 4 * b7
    + (38755368960 : F[X]) * h ^ 46 * a7 * a6 ^ 3 * a5 * b8
    + (1937768448 : F[X]) * h ^ 46 * a6 ^ 5 * b8
    + (2588737536 : F[X]) * h ^ 47 * a7 ^ 5 * a2 * Polynomial.C lambda
    + (12943687680 : F[X]) * h ^ 47 * a7 ^ 4 * a6 * a3 * Polynomial.C lambda
    + (12943687680 : F[X]) * h ^ 47 * a7 ^ 4 * a5 * a4 * Polynomial.C lambda
    + (25887375360 : F[X]) * h ^ 47 * a7 ^ 3 * a6 ^ 2 * a4 * Polynomial.C lambda
    + (25887375360 : F[X]) * h ^ 47 * a7 ^ 3 * a6 * a5 ^ 2 * Polynomial.C lambda
    + (25887375360 : F[X]) * h ^ 47 * a7 ^ 2 * a6 ^ 3 * a5 * Polynomial.C lambda
    + (2588737536 : F[X]) * h ^ 47 * a7 * a6 ^ 5 * Polynomial.C lambda
    + (2119434240 : F[X]) * h ^ 48 * a7 ^ 5 * a1
    - (3027763200 : F[X]) * h ^ 48 * a7 ^ 4 * a6 * a2
    - (3027763200 : F[X]) * h ^ 48 * a7 ^ 4 * a5 * a3
    - (1513881600 : F[X]) * h ^ 48 * a7 ^ 4 * a4 ^ 2
    - (33305395200 : F[X]) * h ^ 48 * a7 ^ 3 * a6 ^ 2 * a3
    - (66610790400 : F[X]) * h ^ 48 * a7 ^ 3 * a6 * a5 * a4
    - (11101798400 : F[X]) * h ^ 48 * a7 ^ 3 * a5 ^ 3
    - (60555264000 : F[X]) * h ^ 48 * a7 ^ 2 * a6 ^ 3 * a4
    - (90832896000 : F[X]) * h ^ 48 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2
    - (43902566400 : F[X]) * h ^ 48 * a7 * a6 ^ 4 * a5
    - (1917583360 : F[X]) * h ^ 48 * a6 ^ 6
    - (645922816 : F[X]) * h ^ 54 * a7 ^ 4 * b2
    - (3875536896 : F[X]) * h ^ 54 * a7 ^ 3 * a6 * b3
    - (5167382528 : F[X]) * h ^ 54 * a7 ^ 3 * a5 * b4
    - (6459228160 : F[X]) * h ^ 54 * a7 ^ 3 * a4 * b5
    - (7751073792 : F[X]) * h ^ 54 * a7 ^ 3 * a3 * b6
    - (9042919424 : F[X]) * h ^ 54 * a7 ^ 3 * a2 * b7
    - (10334765056 : F[X]) * h ^ 54 * a7 ^ 3 * a1 * b8
    - (7751073792 : F[X]) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * b4
    - (19377684480 : F[X]) * h ^ 54 * a7 ^ 2 * a6 * a5 * b5
    - (23253221376 : F[X]) * h ^ 54 * a7 ^ 2 * a6 * a4 * b6
    - (27128758272 : F[X]) * h ^ 54 * a7 ^ 2 * a6 * a3 * b7
    - (31004295168 : F[X]) * h ^ 54 * a7 ^ 2 * a6 * a2 * b8
    - (11626610688 : F[X]) * h ^ 54 * a7 ^ 2 * a5 ^ 2 * b6
    - (27128758272 : F[X]) * h ^ 54 * a7 ^ 2 * a5 * a4 * b7
    - (31004295168 : F[X]) * h ^ 54 * a7 ^ 2 * a5 * a3 * b8
    - (15502147584 : F[X]) * h ^ 54 * a7 ^ 2 * a4 ^ 2 * b8
    - (6459228160 : F[X]) * h ^ 54 * a7 * a6 ^ 3 * b5
    - (23253221376 : F[X]) * h ^ 54 * a7 * a6 ^ 2 * a5 * b6
    - (27128758272 : F[X]) * h ^ 54 * a7 * a6 ^ 2 * a4 * b7
    - (31004295168 : F[X]) * h ^ 54 * a7 * a6 ^ 2 * a3 * b8
    - (27128758272 : F[X]) * h ^ 54 * a7 * a6 * a5 ^ 2 * b7
    - (62008590336 : F[X]) * h ^ 54 * a7 * a6 * a5 * a4 * b8
    - (10334765056 : F[X]) * h ^ 54 * a7 * a5 ^ 3 * b8
    - (1937768448 : F[X]) * h ^ 54 * a6 ^ 4 * b6
    - (9042919424 : F[X]) * h ^ 54 * a6 ^ 3 * a5 * b7
    - (10334765056 : F[X]) * h ^ 54 * a6 ^ 3 * a4 * b8
    - (15502147584 : F[X]) * h ^ 54 * a6 ^ 2 * a5 ^ 2 * b8
    - (2724986880 : F[X]) * h ^ 55 * a7 ^ 4 * a1 * Polynomial.C lambda
    - (10899947520 : F[X]) * h ^ 55 * a7 ^ 3 * a6 * a2 * Polynomial.C lambda
    - (10899947520 : F[X]) * h ^ 55 * a7 ^ 3 * a5 * a3 * Polynomial.C lambda
    - (5449973760 : F[X]) * h ^ 55 * a7 ^ 3 * a4 ^ 2 * Polynomial.C lambda
    - (16349921280 : F[X]) * h ^ 55 * a7 ^ 2 * a6 ^ 2 * a3 * Polynomial.C lambda
    - (32699842560 : F[X]) * h ^ 55 * a7 ^ 2 * a6 * a5 * a4 * Polynomial.C lambda
    - (5449973760 : F[X]) * h ^ 55 * a7 ^ 2 * a5 ^ 3 * Polynomial.C lambda
    - (10899947520 : F[X]) * h ^ 55 * a7 * a6 ^ 3 * a4 * Polynomial.C lambda
    - (16349921280 : F[X]) * h ^ 55 * a7 * a6 ^ 2 * a5 ^ 2 * Polynomial.C lambda
    - (2724986880 : F[X]) * h ^ 55 * a6 ^ 4 * a5 * Polynomial.C lambda
    - (2422210560 : F[X]) * h ^ 56 * a7 ^ 4 * a0
    + (4844421120 : F[X]) * h ^ 56 * a7 ^ 3 * a6 * a1
    + (4844421120 : F[X]) * h ^ 56 * a7 ^ 3 * a5 * a2
    + (4844421120 : F[X]) * h ^ 56 * a7 ^ 3 * a4 * a3
    + (29066526720 : F[X]) * h ^ 56 * a7 ^ 2 * a6 ^ 2 * a2
    + (58133053440 : F[X]) * h ^ 56 * a7 ^ 2 * a6 * a5 * a3
    + (29066526720 : F[X]) * h ^ 56 * a7 ^ 2 * a6 * a4 ^ 2
    + (29066526720 : F[X]) * h ^ 56 * a7 ^ 2 * a5 ^ 2 * a4
    + (33910947840 : F[X]) * h ^ 56 * a7 * a6 ^ 3 * a3
    + (101732843520 : F[X]) * h ^ 56 * a7 * a6 ^ 2 * a5 * a4
    + (33910947840 : F[X]) * h ^ 56 * a7 * a6 * a5 ^ 3
    + (12111052800 : F[X]) * h ^ 56 * a6 ^ 4 * a4
    + (24222105600 : F[X]) * h ^ 56 * a6 ^ 3 * a5 ^ 2
    + (469762048 : F[X]) * h ^ 62 * a7 ^ 3 * b1
    + (2818572288 : F[X]) * h ^ 62 * a7 ^ 2 * a6 * b2
    + (4227858432 : F[X]) * h ^ 62 * a7 ^ 2 * a5 * b3
    + (5637144576 : F[X]) * h ^ 62 * a7 ^ 2 * a4 * b4
    + (7046430720 : F[X]) * h ^ 62 * a7 ^ 2 * a3 * b5
    + (8455716864 : F[X]) * h ^ 62 * a7 ^ 2 * a2 * b6
    + (9865003008 : F[X]) * h ^ 62 * a7 ^ 2 * a1 * b7
    + (11274289152 : F[X]) * h ^ 62 * a7 ^ 2 * a0 * b8
    + (4227858432 : F[X]) * h ^ 62 * a7 * a6 ^ 2 * b3
    + (11274289152 : F[X]) * h ^ 62 * a7 * a6 * a5 * b4
    + (14092861440 : F[X]) * h ^ 62 * a7 * a6 * a4 * b5
    + (16911433728 : F[X]) * h ^ 62 * a7 * a6 * a3 * b6
    + (19730006016 : F[X]) * h ^ 62 * a7 * a6 * a2 * b7
    + (22548578304 : F[X]) * h ^ 62 * a7 * a6 * a1 * b8
    + (7046430720 : F[X]) * h ^ 62 * a7 * a5 ^ 2 * b5
    + (16911433728 : F[X]) * h ^ 62 * a7 * a5 * a4 * b6
    + (19730006016 : F[X]) * h ^ 62 * a7 * a5 * a3 * b7
    + (22548578304 : F[X]) * h ^ 62 * a7 * a5 * a2 * b8
    + (9865003008 : F[X]) * h ^ 62 * a7 * a4 ^ 2 * b7
    + (22548578304 : F[X]) * h ^ 62 * a7 * a4 * a3 * b8
    + (1879048192 : F[X]) * h ^ 62 * a6 ^ 3 * b4
    + (7046430720 : F[X]) * h ^ 62 * a6 ^ 2 * a5 * b5
    + (8455716864 : F[X]) * h ^ 62 * a6 ^ 2 * a4 * b6
    + (9865003008 : F[X]) * h ^ 62 * a6 ^ 2 * a3 * b7
    + (11274289152 : F[X]) * h ^ 62 * a6 ^ 2 * a2 * b8
    + (8455716864 : F[X]) * h ^ 62 * a6 * a5 ^ 2 * b6
    + (19730006016 : F[X]) * h ^ 62 * a6 * a5 * a4 * b7
    + (22548578304 : F[X]) * h ^ 62 * a6 * a5 * a3 * b8
    + (11274289152 : F[X]) * h ^ 62 * a6 * a4 ^ 2 * b8
    + (3288334336 : F[X]) * h ^ 62 * a5 ^ 3 * b7
    + (11274289152 : F[X]) * h ^ 62 * a5 ^ 2 * a4 * b8
    + (2906652672 : F[X]) * h ^ 63 * a7 ^ 3 * a0 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 ^ 2 * a6 * a1 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 ^ 2 * a5 * a2 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 ^ 2 * a4 * a3 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 * a6 ^ 2 * a2 * Polynomial.C lambda
    + (17439916032 : F[X]) * h ^ 63 * a7 * a6 * a5 * a3 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 * a6 * a4 ^ 2 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a7 * a5 ^ 2 * a4 * Polynomial.C lambda
    + (2906652672 : F[X]) * h ^ 63 * a6 ^ 3 * a3 * Polynomial.C lambda
    + (8719958016 : F[X]) * h ^ 63 * a6 ^ 2 * a5 * a4 * Polynomial.C lambda
    + (2906652672 : F[X]) * h ^ 63 * a6 * a5 ^ 3 * Polynomial.C lambda
    - (7046430720 : F[X]) * h ^ 64 * a7 ^ 2 * a6 * a0
    - (7046430720 : F[X]) * h ^ 64 * a7 ^ 2 * a5 * a1
    - (7046430720 : F[X]) * h ^ 64 * a7 ^ 2 * a4 * a2
    - (3523215360 : F[X]) * h ^ 64 * a7 ^ 2 * a3 ^ 2
    - (22900899840 : F[X]) * h ^ 64 * a7 * a6 ^ 2 * a1
    - (45801799680 : F[X]) * h ^ 64 * a7 * a6 * a5 * a2
    - (45801799680 : F[X]) * h ^ 64 * a7 * a6 * a4 * a3
    - (22900899840 : F[X]) * h ^ 64 * a7 * a5 ^ 2 * a3
    - (22900899840 : F[X]) * h ^ 64 * a7 * a5 * a4 ^ 2
    - (12918456320 : F[X]) * h ^ 64 * a6 ^ 3 * a2
    - (38755368960 : F[X]) * h ^ 64 * a6 ^ 2 * a5 * a3
    - (19377684480 : F[X]) * h ^ 64 * a6 ^ 2 * a4 ^ 2
    - (38755368960 : F[X]) * h ^ 64 * a6 * a5 ^ 2 * a4
    - (3229614080 : F[X]) * h ^ 64 * a5 ^ 4
    - (1610612736 : F[X]) * h ^ 70 * a7 * a6 * b1
    - (3221225472 : F[X]) * h ^ 70 * a7 * a5 * b2
    - (4831838208 : F[X]) * h ^ 70 * a7 * a4 * b3
    - (6442450944 : F[X]) * h ^ 70 * a7 * a3 * b4
    - (8053063680 : F[X]) * h ^ 70 * a7 * a2 * b5
    - (9663676416 : F[X]) * h ^ 70 * a7 * a1 * b6
    - (11274289152 : F[X]) * h ^ 70 * a7 * a0 * b7
    - (1610612736 : F[X]) * h ^ 70 * a6 ^ 2 * b2
    - (4831838208 : F[X]) * h ^ 70 * a6 * a5 * b3
    - (6442450944 : F[X]) * h ^ 70 * a6 * a4 * b4
    - (8053063680 : F[X]) * h ^ 70 * a6 * a3 * b5
    - (9663676416 : F[X]) * h ^ 70 * a6 * a2 * b6
    - (11274289152 : F[X]) * h ^ 70 * a6 * a1 * b7
    - (12884901888 : F[X]) * h ^ 70 * a6 * a0 * b8
    - (3221225472 : F[X]) * h ^ 70 * a5 ^ 2 * b4
    - (8053063680 : F[X]) * h ^ 70 * a5 * a4 * b5
    - (9663676416 : F[X]) * h ^ 70 * a5 * a3 * b6
    - (11274289152 : F[X]) * h ^ 70 * a5 * a2 * b7
    - (12884901888 : F[X]) * h ^ 70 * a5 * a1 * b8
    - (4831838208 : F[X]) * h ^ 70 * a4 ^ 2 * b6
    - (11274289152 : F[X]) * h ^ 70 * a4 * a3 * b7
    - (12884901888 : F[X]) * h ^ 70 * a4 * a2 * b8
    - (6442450944 : F[X]) * h ^ 70 * a3 ^ 2 * b8
    - (6341787648 : F[X]) * h ^ 71 * a7 * a6 * a0 * Polynomial.C lambda
    - (6341787648 : F[X]) * h ^ 71 * a7 * a5 * a1 * Polynomial.C lambda
    - (6341787648 : F[X]) * h ^ 71 * a7 * a4 * a2 * Polynomial.C lambda
    - (3170893824 : F[X]) * h ^ 71 * a7 * a3 ^ 2 * Polynomial.C lambda
    - (3170893824 : F[X]) * h ^ 71 * a6 ^ 2 * a1 * Polynomial.C lambda
    - (6341787648 : F[X]) * h ^ 71 * a6 * a5 * a2 * Polynomial.C lambda
    - (6341787648 : F[X]) * h ^ 71 * a6 * a4 * a3 * Polynomial.C lambda
    - (3170893824 : F[X]) * h ^ 71 * a5 ^ 2 * a3 * Polynomial.C lambda
    - (3170893824 : F[X]) * h ^ 71 * a5 * a4 ^ 2 * Polynomial.C lambda
    + (10066329600 : F[X]) * h ^ 72 * a7 * a5 * a0
    + (10066329600 : F[X]) * h ^ 72 * a7 * a4 * a1
    + (10066329600 : F[X]) * h ^ 72 * a7 * a3 * a2
    + (14092861440 : F[X]) * h ^ 72 * a6 ^ 2 * a0
    + (28185722880 : F[X]) * h ^ 72 * a6 * a5 * a1
    + (28185722880 : F[X]) * h ^ 72 * a6 * a4 * a2
    + (14092861440 : F[X]) * h ^ 72 * a6 * a3 ^ 2
    + (14092861440 : F[X]) * h ^ 72 * a5 ^ 2 * a2
    + (28185722880 : F[X]) * h ^ 72 * a5 * a4 * a3
    + (4697620480 : F[X]) * h ^ 72 * a4 ^ 3
    + (2147483648 : F[X]) * h ^ 78 * a5 * b1
    + (4294967296 : F[X]) * h ^ 78 * a4 * b2
    + (6442450944 : F[X]) * h ^ 78 * a3 * b3
    + (8589934592 : F[X]) * h ^ 78 * a2 * b4
    + (10737418240 : F[X]) * h ^ 78 * a1 * b5
    + (12884901888 : F[X]) * h ^ 78 * a0 * b6
    + (3623878656 : F[X]) * h ^ 79 * a5 * a0 * Polynomial.C lambda
    + (3623878656 : F[X]) * h ^ 79 * a4 * a1 * Polynomial.C lambda
    + (3623878656 : F[X]) * h ^ 79 * a3 * a2 * Polynomial.C lambda
    - (16106127360 : F[X]) * h ^ 80 * a4 * a0
    - (16106127360 : F[X]) * h ^ 80 * a3 * a1
    - (8053063680 : F[X]) * h ^ 80 * a2 ^ 2

set_option maxHeartbeats 40000000 in
/-- Clearing the first integral `μ` of the degree-`5` row against `h⁸⁴`
on the ninth-power face. -/
theorem terminalMuDefect_eq_cleared810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (17179869184 : F) * h ^ 84 *
        terminalMuResidual810
          (depressedL810 h (octicDepressionR810 h a7) b9)
          (depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
          (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
          (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
          (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
            a1)
          (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
            a1 a0)
          (depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
          (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
          (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
          (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
          (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3)
          (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3 b2)
          (depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3 b2 b1) =
    (203408205 : F) * a7 ^ 12
    - (801115392 : F) * h ^ 6 * a7 ^ 10 * b8
    - (199709874 : F) * h ^ 7 * a7 ^ 11 * lambda
    - (1502091360 : F) * h ^ 8 * a7 ^ 10 * a6
    + (801115392 : F) * h ^ 14 * a7 ^ 9 * b7
    + (8240044032 : F) * h ^ 14 * a7 ^ 8 * a6 * b8
    + (2253137040 : F) * h ^ 15 * a7 ^ 9 * a6 * lambda
    + (1573619520 : F) * h ^ 16 * a7 ^ 9 * a5
    + (1287506880 : F) * h ^ 16 * a7 ^ 8 * a6 ^ 2
    - (797423616 : F) * h ^ 22 * a7 ^ 8 * b6
    - (7442620416 : F) * h ^ 22 * a7 ^ 7 * a6 * b7
    - (8505851904 : F) * h ^ 22 * a7 ^ 7 * a5 * b8
    - (29770481664 : F) * h ^ 22 * a7 ^ 6 * a6 ^ 2 * b8
    - (2317512384 : F) * h ^ 23 * a7 ^ 8 * a5 * lambda
    - (9270049536 : F) * h ^ 23 * a7 ^ 7 * a6 ^ 2 * lambda
    - (1661299200 : F) * h ^ 24 * a7 ^ 8 * a4
    - (1329039360 : F) * h ^ 24 * a7 ^ 7 * a6 * a5
    + (12404367360 : F) * h ^ 24 * a7 ^ 6 * a6 ^ 3
    + (787578880 : F) * h ^ 30 * a7 ^ 7 * b5
    + (6615662592 : F) * h ^ 30 * a7 ^ 6 * a6 * b6
    + (7718273024 : F) * h ^ 30 * a7 ^ 6 * a5 * b7
    + (8820883456 : F) * h ^ 30 * a7 ^ 6 * a4 * b8
    + (23154819072 : F) * h ^ 30 * a7 ^ 5 * a6 ^ 2 * b7
    + (52925300736 : F) * h ^ 30 * a7 ^ 5 * a6 * a5 * b8
    + (44104417280 : F) * h ^ 30 * a7 ^ 4 * a6 ^ 3 * b8
    + (2392270848 : F) * h ^ 31 * a7 ^ 7 * a4 * lambda
    + (16745895936 : F) * h ^ 31 * a7 ^ 6 * a6 * a5 * lambda
    + (16745895936 : F) * h ^ 31 * a7 ^ 5 * a6 ^ 3 * lambda
    + (1772052480 : F) * h ^ 32 * a7 ^ 7 * a3
    - (37213102080 : F) * h ^ 32 * a7 ^ 5 * a6 ^ 2 * a5
    - (31010918400 : F) * h ^ 32 * a7 ^ 4 * a6 ^ 4
    - (767033344 : F) * h ^ 38 * a7 ^ 6 * b4
    - (5752750080 : F) * h ^ 38 * a7 ^ 5 * a6 * b5
    - (6903300096 : F) * h ^ 38 * a7 ^ 5 * a5 * b6
    - (8053850112 : F) * h ^ 38 * a7 ^ 5 * a4 * b7
    - (9204400128 : F) * h ^ 38 * a7 ^ 5 * a3 * b8
    - (17258250240 : F) * h ^ 38 * a7 ^ 4 * a6 ^ 2 * b6
    - (40269250560 : F) * h ^ 38 * a7 ^ 4 * a6 * a5 * b7
    - (46022000640 : F) * h ^ 38 * a7 ^ 4 * a6 * a4 * b8
    - (23011000320 : F) * h ^ 38 * a7 ^ 4 * a5 ^ 2 * b8
    - (26846167040 : F) * h ^ 38 * a7 ^ 3 * a6 ^ 3 * b7
    - (92044001280 : F) * h ^ 38 * a7 ^ 3 * a6 ^ 2 * a5 * b8
    - (23011000320 : F) * h ^ 38 * a7 ^ 2 * a6 ^ 4 * b8
    - (2480873472 : F) * h ^ 39 * a7 ^ 6 * a3 * lambda
    - (14885240832 : F) * h ^ 39 * a7 ^ 5 * a6 * a4 * lambda
    - (7442620416 : F) * h ^ 39 * a7 ^ 5 * a5 ^ 2 * lambda
    - (37213102080 : F) * h ^ 39 * a7 ^ 4 * a6 ^ 2 * a5 * lambda
    - (12404367360 : F) * h ^ 39 * a7 ^ 3 * a6 ^ 4 * lambda
    - (1917583360 : F) * h ^ 40 * a7 ^ 6 * a2
    + (1438187520 : F) * h ^ 40 * a7 ^ 5 * a6 * a3
    + (1438187520 : F) * h ^ 40 * a7 ^ 5 * a5 * a4
    + (35954688000 : F) * h ^ 40 * a7 ^ 4 * a6 ^ 2 * a4
    + (35954688000 : F) * h ^ 40 * a7 ^ 4 * a6 * a5 ^ 2
    + (91085209600 : F) * h ^ 40 * a7 ^ 3 * a6 ^ 3 * a5
    + (20134625280 : F) * h ^ 40 * a7 ^ 2 * a6 ^ 5
    + (726663168 : F) * h ^ 46 * a7 ^ 5 * b3
    + (4844421120 : F) * h ^ 46 * a7 ^ 4 * a6 * b4
    + (6055526400 : F) * h ^ 46 * a7 ^ 4 * a5 * b5
    + (7266631680 : F) * h ^ 46 * a7 ^ 4 * a4 * b6
    + (8477736960 : F) * h ^ 46 * a7 ^ 4 * a3 * b7
    + (9688842240 : F) * h ^ 46 * a7 ^ 4 * a2 * b8
    + (12111052800 : F) * h ^ 46 * a7 ^ 3 * a6 ^ 2 * b5
    + (29066526720 : F) * h ^ 46 * a7 ^ 3 * a6 * a5 * b6
    + (33910947840 : F) * h ^ 46 * a7 ^ 3 * a6 * a4 * b7
    + (38755368960 : F) * h ^ 46 * a7 ^ 3 * a6 * a3 * b8
    + (16955473920 : F) * h ^ 46 * a7 ^ 3 * a5 ^ 2 * b7
    + (38755368960 : F) * h ^ 46 * a7 ^ 3 * a5 * a4 * b8
    + (14533263360 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 3 * b6
    + (50866421760 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * a5 * b7
    + (58133053440 : F) * h ^ 46 * a7 ^ 2 * a6 ^ 2 * a4 * b8
    + (58133053440 : F) * h ^ 46 * a7 ^ 2 * a6 * a5 ^ 2 * b8
    + (8477736960 : F) * h ^ 46 * a7 * a6 ^ 4 * b7
    + (38755368960 : F) * h ^ 46 * a7 * a6 ^ 3 * a5 * b8
    + (1937768448 : F) * h ^ 46 * a6 ^ 5 * b8
    + (2588737536 : F) * h ^ 47 * a7 ^ 5 * a2 * lambda
    + (12943687680 : F) * h ^ 47 * a7 ^ 4 * a6 * a3 * lambda
    + (12943687680 : F) * h ^ 47 * a7 ^ 4 * a5 * a4 * lambda
    + (25887375360 : F) * h ^ 47 * a7 ^ 3 * a6 ^ 2 * a4 * lambda
    + (25887375360 : F) * h ^ 47 * a7 ^ 3 * a6 * a5 ^ 2 * lambda
    + (25887375360 : F) * h ^ 47 * a7 ^ 2 * a6 ^ 3 * a5 * lambda
    + (2588737536 : F) * h ^ 47 * a7 * a6 ^ 5 * lambda
    + (2119434240 : F) * h ^ 48 * a7 ^ 5 * a1
    - (3027763200 : F) * h ^ 48 * a7 ^ 4 * a6 * a2
    - (3027763200 : F) * h ^ 48 * a7 ^ 4 * a5 * a3
    - (1513881600 : F) * h ^ 48 * a7 ^ 4 * a4 ^ 2
    - (33305395200 : F) * h ^ 48 * a7 ^ 3 * a6 ^ 2 * a3
    - (66610790400 : F) * h ^ 48 * a7 ^ 3 * a6 * a5 * a4
    - (11101798400 : F) * h ^ 48 * a7 ^ 3 * a5 ^ 3
    - (60555264000 : F) * h ^ 48 * a7 ^ 2 * a6 ^ 3 * a4
    - (90832896000 : F) * h ^ 48 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2
    - (43902566400 : F) * h ^ 48 * a7 * a6 ^ 4 * a5
    - (1917583360 : F) * h ^ 48 * a6 ^ 6
    - (645922816 : F) * h ^ 54 * a7 ^ 4 * b2
    - (3875536896 : F) * h ^ 54 * a7 ^ 3 * a6 * b3
    - (5167382528 : F) * h ^ 54 * a7 ^ 3 * a5 * b4
    - (6459228160 : F) * h ^ 54 * a7 ^ 3 * a4 * b5
    - (7751073792 : F) * h ^ 54 * a7 ^ 3 * a3 * b6
    - (9042919424 : F) * h ^ 54 * a7 ^ 3 * a2 * b7
    - (10334765056 : F) * h ^ 54 * a7 ^ 3 * a1 * b8
    - (7751073792 : F) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * b4
    - (19377684480 : F) * h ^ 54 * a7 ^ 2 * a6 * a5 * b5
    - (23253221376 : F) * h ^ 54 * a7 ^ 2 * a6 * a4 * b6
    - (27128758272 : F) * h ^ 54 * a7 ^ 2 * a6 * a3 * b7
    - (31004295168 : F) * h ^ 54 * a7 ^ 2 * a6 * a2 * b8
    - (11626610688 : F) * h ^ 54 * a7 ^ 2 * a5 ^ 2 * b6
    - (27128758272 : F) * h ^ 54 * a7 ^ 2 * a5 * a4 * b7
    - (31004295168 : F) * h ^ 54 * a7 ^ 2 * a5 * a3 * b8
    - (15502147584 : F) * h ^ 54 * a7 ^ 2 * a4 ^ 2 * b8
    - (6459228160 : F) * h ^ 54 * a7 * a6 ^ 3 * b5
    - (23253221376 : F) * h ^ 54 * a7 * a6 ^ 2 * a5 * b6
    - (27128758272 : F) * h ^ 54 * a7 * a6 ^ 2 * a4 * b7
    - (31004295168 : F) * h ^ 54 * a7 * a6 ^ 2 * a3 * b8
    - (27128758272 : F) * h ^ 54 * a7 * a6 * a5 ^ 2 * b7
    - (62008590336 : F) * h ^ 54 * a7 * a6 * a5 * a4 * b8
    - (10334765056 : F) * h ^ 54 * a7 * a5 ^ 3 * b8
    - (1937768448 : F) * h ^ 54 * a6 ^ 4 * b6
    - (9042919424 : F) * h ^ 54 * a6 ^ 3 * a5 * b7
    - (10334765056 : F) * h ^ 54 * a6 ^ 3 * a4 * b8
    - (15502147584 : F) * h ^ 54 * a6 ^ 2 * a5 ^ 2 * b8
    - (2724986880 : F) * h ^ 55 * a7 ^ 4 * a1 * lambda
    - (10899947520 : F) * h ^ 55 * a7 ^ 3 * a6 * a2 * lambda
    - (10899947520 : F) * h ^ 55 * a7 ^ 3 * a5 * a3 * lambda
    - (5449973760 : F) * h ^ 55 * a7 ^ 3 * a4 ^ 2 * lambda
    - (16349921280 : F) * h ^ 55 * a7 ^ 2 * a6 ^ 2 * a3 * lambda
    - (32699842560 : F) * h ^ 55 * a7 ^ 2 * a6 * a5 * a4 * lambda
    - (5449973760 : F) * h ^ 55 * a7 ^ 2 * a5 ^ 3 * lambda
    - (10899947520 : F) * h ^ 55 * a7 * a6 ^ 3 * a4 * lambda
    - (16349921280 : F) * h ^ 55 * a7 * a6 ^ 2 * a5 ^ 2 * lambda
    - (2724986880 : F) * h ^ 55 * a6 ^ 4 * a5 * lambda
    - (2422210560 : F) * h ^ 56 * a7 ^ 4 * a0
    + (4844421120 : F) * h ^ 56 * a7 ^ 3 * a6 * a1
    + (4844421120 : F) * h ^ 56 * a7 ^ 3 * a5 * a2
    + (4844421120 : F) * h ^ 56 * a7 ^ 3 * a4 * a3
    + (29066526720 : F) * h ^ 56 * a7 ^ 2 * a6 ^ 2 * a2
    + (58133053440 : F) * h ^ 56 * a7 ^ 2 * a6 * a5 * a3
    + (29066526720 : F) * h ^ 56 * a7 ^ 2 * a6 * a4 ^ 2
    + (29066526720 : F) * h ^ 56 * a7 ^ 2 * a5 ^ 2 * a4
    + (33910947840 : F) * h ^ 56 * a7 * a6 ^ 3 * a3
    + (101732843520 : F) * h ^ 56 * a7 * a6 ^ 2 * a5 * a4
    + (33910947840 : F) * h ^ 56 * a7 * a6 * a5 ^ 3
    + (12111052800 : F) * h ^ 56 * a6 ^ 4 * a4
    + (24222105600 : F) * h ^ 56 * a6 ^ 3 * a5 ^ 2
    + (469762048 : F) * h ^ 62 * a7 ^ 3 * b1
    + (2818572288 : F) * h ^ 62 * a7 ^ 2 * a6 * b2
    + (4227858432 : F) * h ^ 62 * a7 ^ 2 * a5 * b3
    + (5637144576 : F) * h ^ 62 * a7 ^ 2 * a4 * b4
    + (7046430720 : F) * h ^ 62 * a7 ^ 2 * a3 * b5
    + (8455716864 : F) * h ^ 62 * a7 ^ 2 * a2 * b6
    + (9865003008 : F) * h ^ 62 * a7 ^ 2 * a1 * b7
    + (11274289152 : F) * h ^ 62 * a7 ^ 2 * a0 * b8
    + (4227858432 : F) * h ^ 62 * a7 * a6 ^ 2 * b3
    + (11274289152 : F) * h ^ 62 * a7 * a6 * a5 * b4
    + (14092861440 : F) * h ^ 62 * a7 * a6 * a4 * b5
    + (16911433728 : F) * h ^ 62 * a7 * a6 * a3 * b6
    + (19730006016 : F) * h ^ 62 * a7 * a6 * a2 * b7
    + (22548578304 : F) * h ^ 62 * a7 * a6 * a1 * b8
    + (7046430720 : F) * h ^ 62 * a7 * a5 ^ 2 * b5
    + (16911433728 : F) * h ^ 62 * a7 * a5 * a4 * b6
    + (19730006016 : F) * h ^ 62 * a7 * a5 * a3 * b7
    + (22548578304 : F) * h ^ 62 * a7 * a5 * a2 * b8
    + (9865003008 : F) * h ^ 62 * a7 * a4 ^ 2 * b7
    + (22548578304 : F) * h ^ 62 * a7 * a4 * a3 * b8
    + (1879048192 : F) * h ^ 62 * a6 ^ 3 * b4
    + (7046430720 : F) * h ^ 62 * a6 ^ 2 * a5 * b5
    + (8455716864 : F) * h ^ 62 * a6 ^ 2 * a4 * b6
    + (9865003008 : F) * h ^ 62 * a6 ^ 2 * a3 * b7
    + (11274289152 : F) * h ^ 62 * a6 ^ 2 * a2 * b8
    + (8455716864 : F) * h ^ 62 * a6 * a5 ^ 2 * b6
    + (19730006016 : F) * h ^ 62 * a6 * a5 * a4 * b7
    + (22548578304 : F) * h ^ 62 * a6 * a5 * a3 * b8
    + (11274289152 : F) * h ^ 62 * a6 * a4 ^ 2 * b8
    + (3288334336 : F) * h ^ 62 * a5 ^ 3 * b7
    + (11274289152 : F) * h ^ 62 * a5 ^ 2 * a4 * b8
    + (2906652672 : F) * h ^ 63 * a7 ^ 3 * a0 * lambda
    + (8719958016 : F) * h ^ 63 * a7 ^ 2 * a6 * a1 * lambda
    + (8719958016 : F) * h ^ 63 * a7 ^ 2 * a5 * a2 * lambda
    + (8719958016 : F) * h ^ 63 * a7 ^ 2 * a4 * a3 * lambda
    + (8719958016 : F) * h ^ 63 * a7 * a6 ^ 2 * a2 * lambda
    + (17439916032 : F) * h ^ 63 * a7 * a6 * a5 * a3 * lambda
    + (8719958016 : F) * h ^ 63 * a7 * a6 * a4 ^ 2 * lambda
    + (8719958016 : F) * h ^ 63 * a7 * a5 ^ 2 * a4 * lambda
    + (2906652672 : F) * h ^ 63 * a6 ^ 3 * a3 * lambda
    + (8719958016 : F) * h ^ 63 * a6 ^ 2 * a5 * a4 * lambda
    + (2906652672 : F) * h ^ 63 * a6 * a5 ^ 3 * lambda
    - (7046430720 : F) * h ^ 64 * a7 ^ 2 * a6 * a0
    - (7046430720 : F) * h ^ 64 * a7 ^ 2 * a5 * a1
    - (7046430720 : F) * h ^ 64 * a7 ^ 2 * a4 * a2
    - (3523215360 : F) * h ^ 64 * a7 ^ 2 * a3 ^ 2
    - (22900899840 : F) * h ^ 64 * a7 * a6 ^ 2 * a1
    - (45801799680 : F) * h ^ 64 * a7 * a6 * a5 * a2
    - (45801799680 : F) * h ^ 64 * a7 * a6 * a4 * a3
    - (22900899840 : F) * h ^ 64 * a7 * a5 ^ 2 * a3
    - (22900899840 : F) * h ^ 64 * a7 * a5 * a4 ^ 2
    - (12918456320 : F) * h ^ 64 * a6 ^ 3 * a2
    - (38755368960 : F) * h ^ 64 * a6 ^ 2 * a5 * a3
    - (19377684480 : F) * h ^ 64 * a6 ^ 2 * a4 ^ 2
    - (38755368960 : F) * h ^ 64 * a6 * a5 ^ 2 * a4
    - (3229614080 : F) * h ^ 64 * a5 ^ 4
    - (1610612736 : F) * h ^ 70 * a7 * a6 * b1
    - (3221225472 : F) * h ^ 70 * a7 * a5 * b2
    - (4831838208 : F) * h ^ 70 * a7 * a4 * b3
    - (6442450944 : F) * h ^ 70 * a7 * a3 * b4
    - (8053063680 : F) * h ^ 70 * a7 * a2 * b5
    - (9663676416 : F) * h ^ 70 * a7 * a1 * b6
    - (11274289152 : F) * h ^ 70 * a7 * a0 * b7
    - (1610612736 : F) * h ^ 70 * a6 ^ 2 * b2
    - (4831838208 : F) * h ^ 70 * a6 * a5 * b3
    - (6442450944 : F) * h ^ 70 * a6 * a4 * b4
    - (8053063680 : F) * h ^ 70 * a6 * a3 * b5
    - (9663676416 : F) * h ^ 70 * a6 * a2 * b6
    - (11274289152 : F) * h ^ 70 * a6 * a1 * b7
    - (12884901888 : F) * h ^ 70 * a6 * a0 * b8
    - (3221225472 : F) * h ^ 70 * a5 ^ 2 * b4
    - (8053063680 : F) * h ^ 70 * a5 * a4 * b5
    - (9663676416 : F) * h ^ 70 * a5 * a3 * b6
    - (11274289152 : F) * h ^ 70 * a5 * a2 * b7
    - (12884901888 : F) * h ^ 70 * a5 * a1 * b8
    - (4831838208 : F) * h ^ 70 * a4 ^ 2 * b6
    - (11274289152 : F) * h ^ 70 * a4 * a3 * b7
    - (12884901888 : F) * h ^ 70 * a4 * a2 * b8
    - (6442450944 : F) * h ^ 70 * a3 ^ 2 * b8
    - (6341787648 : F) * h ^ 71 * a7 * a6 * a0 * lambda
    - (6341787648 : F) * h ^ 71 * a7 * a5 * a1 * lambda
    - (6341787648 : F) * h ^ 71 * a7 * a4 * a2 * lambda
    - (3170893824 : F) * h ^ 71 * a7 * a3 ^ 2 * lambda
    - (3170893824 : F) * h ^ 71 * a6 ^ 2 * a1 * lambda
    - (6341787648 : F) * h ^ 71 * a6 * a5 * a2 * lambda
    - (6341787648 : F) * h ^ 71 * a6 * a4 * a3 * lambda
    - (3170893824 : F) * h ^ 71 * a5 ^ 2 * a3 * lambda
    - (3170893824 : F) * h ^ 71 * a5 * a4 ^ 2 * lambda
    + (10066329600 : F) * h ^ 72 * a7 * a5 * a0
    + (10066329600 : F) * h ^ 72 * a7 * a4 * a1
    + (10066329600 : F) * h ^ 72 * a7 * a3 * a2
    + (14092861440 : F) * h ^ 72 * a6 ^ 2 * a0
    + (28185722880 : F) * h ^ 72 * a6 * a5 * a1
    + (28185722880 : F) * h ^ 72 * a6 * a4 * a2
    + (14092861440 : F) * h ^ 72 * a6 * a3 ^ 2
    + (14092861440 : F) * h ^ 72 * a5 ^ 2 * a2
    + (28185722880 : F) * h ^ 72 * a5 * a4 * a3
    + (4697620480 : F) * h ^ 72 * a4 ^ 3
    + (2147483648 : F) * h ^ 78 * a5 * b1
    + (4294967296 : F) * h ^ 78 * a4 * b2
    + (6442450944 : F) * h ^ 78 * a3 * b3
    + (8589934592 : F) * h ^ 78 * a2 * b4
    + (10737418240 : F) * h ^ 78 * a1 * b5
    + (12884901888 : F) * h ^ 78 * a0 * b6
    + (3623878656 : F) * h ^ 79 * a5 * a0 * lambda
    + (3623878656 : F) * h ^ 79 * a4 * a1 * lambda
    + (3623878656 : F) * h ^ 79 * a3 * a2 * lambda
    - (16106127360 : F) * h ^ 80 * a4 * a0
    - (16106127360 : F) * h ^ 80 * a3 * a1
    - (8053063680 : F) * h ^ 80 * a2 ^ 2 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h512 : (512 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h4096 : (4096 : F) ≠ 0 := by norm_num
  have h16384 : (16384 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h32768 : (32768 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  have hh63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  have hh84 : h ^ 84 ≠ 0 := pow_ne_zero 84 hh
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
  have hC :
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
        (2048 * a4 * h ^ 24 - 1280 * a5 * a7 * h ^ 16 +
            480 * a6 * a7 ^ 2 * h ^ 8 - 105 * a7 ^ 4) /
          (2048 * h ^ 28) :=
    depressedC810_eq_cleared h a7 a6 a5 a4 hh
  have hD0 :
      depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
        (1024 * a3 * h ^ 32 - 512 * a4 * a7 * h ^ 24 +
            160 * a5 * a7 ^ 2 * h ^ 16 - 40 * a6 * a7 ^ 3 * h ^ 8 +
            7 * a7 ^ 5) /
          (1024 * h ^ 35) :=
    depressedD810_eq_cleared h a7 a6 a5 a4 a3 hh
  have hE0 :
      depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 =
        (65536 * a2 * h ^ 40 - 24576 * a3 * a7 * h ^ 32 +
            6144 * a4 * a7 ^ 2 * h ^ 24 - 1280 * a5 * a7 ^ 3 * h ^ 16 +
            240 * a6 * a7 ^ 4 * h ^ 8 - 35 * a7 ^ 6) /
          (65536 * h ^ 42) :=
    depressedE810_eq_cleared h a7 a6 a5 a4 a3 a2 hh
  have hF0 :
      depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 =
        (131072 * a1 * h ^ 48 - 32768 * a2 * a7 * h ^ 40 +
            6144 * a3 * a7 ^ 2 * h ^ 32 - 1024 * a4 * a7 ^ 3 * h ^ 24 +
            160 * a5 * a7 ^ 4 * h ^ 16 - 24 * a6 * a7 ^ 5 * h ^ 8 +
            3 * a7 ^ 7) /
          (131072 * h ^ 49) :=
    depressedF810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 hh
  have hG0 :
      depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
          a0 =
        (16777216 * a0 * h ^ 56 - 2097152 * a1 * a7 * h ^ 48 +
            262144 * a2 * a7 ^ 2 * h ^ 40 - 32768 * a3 * a7 ^ 3 * h ^ 32 +
            4096 * a4 * a7 ^ 4 * h ^ 24 - 512 * a5 * a7 ^ 5 * h ^ 16 +
            64 * a6 * a7 ^ 6 * h ^ 8 - 7 * a7 ^ 8) /
          (16777216 * h ^ 56) :=
    depressedG810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 a0 hh
  have hP :
      depressedP810 h (octicDepressionR810 h a7) b9 b8 =
        (-45 * a7 ^ 2 + 18 * lambda * a7 * h ^ 7 + 64 * b8 * h ^ 6) /
          (64 * h ^ 14) :=
    depressedP810_eq_cleared_ninthPower h a7 b9 b8 lambda hh hN
  have hQ :
      depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 =
        (64 * b7 * h ^ 14 - 64 * a7 * b8 * h ^ 6 -
            9 * lambda * a7 ^ 2 * h ^ 7 + 30 * a7 ^ 3) /
          (64 * h ^ 21) :=
    depressedQ810_eq_cleared h a7 b9 b8 b7 lambda hh hN
  have hR :
      depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 =
        (-315 * a7 ^ 4 + 84 * lambda * a7 ^ 3 * h ^ 7 +
            896 * a7 ^ 2 * b8 * h ^ 6 - 1792 * a7 * b7 * h ^ 14 +
            2048 * b6 * h ^ 22) /
          (2048 * h ^ 28) :=
    depressedR810_eq_cleared h a7 b9 b8 b7 b6 lambda hh hN
  have hS :
      depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
        (252 * a7 ^ 5 - 63 * lambda * a7 ^ 4 * h ^ 7 -
            896 * a7 ^ 3 * b8 * h ^ 6 + 2688 * a7 ^ 2 * b7 * h ^ 14 -
            6144 * a7 * b6 * h ^ 22 + 8192 * b5 * h ^ 30) /
          (8192 * h ^ 35) :=
    depressedS810_eq_cleared h a7 b9 b8 b7 b6 b5 lambda hh hN
  have hT0 :
      depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 =
        (-525 * a7 ^ 6 + 126 * lambda * a7 ^ 5 * h ^ 7 +
            2240 * a7 ^ 4 * b8 * h ^ 6 - 8960 * a7 ^ 3 * b7 * h ^ 14 +
            30720 * a7 ^ 2 * b6 * h ^ 22 - 81920 * a7 * b5 * h ^ 30 +
            131072 * b4 * h ^ 38) /
          (131072 * h ^ 42) :=
    depressedT810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hU0 :
      depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 =
        (90 * a7 ^ 7 - 21 * lambda * a7 ^ 6 * h ^ 7 -
            448 * a7 ^ 5 * b8 * h ^ 6 + 2240 * a7 ^ 4 * b7 * h ^ 14 -
            10240 * a7 ^ 3 * b6 * h ^ 22 + 40960 * a7 ^ 2 * b5 * h ^ 30 -
            131072 * a7 * b4 * h ^ 38 + 262144 * b3 * h ^ 46) /
          (262144 * h ^ 49) :=
    depressedU810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  have hV0 :
      depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 =
        (-315 * a7 ^ 8 + 72 * lambda * a7 ^ 7 * h ^ 7 +
            1792 * a7 ^ 6 * b8 * h ^ 6 - 10752 * a7 ^ 5 * b7 * h ^ 14 +
            61440 * a7 ^ 4 * b6 * h ^ 22 - 327680 * a7 ^ 3 * b5 * h ^ 30 +
            1572864 * a7 ^ 2 * b4 * h ^ 38 -
            6291456 * a7 * b3 * h ^ 46 + 16777216 * b2 * h ^ 54) /
          (16777216 * h ^ 56) :=
    depressedV810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  have hW0 :
      depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 =
        (40 * a7 ^ 9 - 9 * lambda * a7 ^ 8 * h ^ 7 -
            256 * a7 ^ 7 * b8 * h ^ 6 + 1792 * a7 ^ 6 * b7 * h ^ 14 -
            12288 * a7 ^ 5 * b6 * h ^ 22 + 81920 * a7 ^ 4 * b5 * h ^ 30 -
            524288 * a7 ^ 3 * b4 * h ^ 38 +
            3145728 * a7 ^ 2 * b3 * h ^ 46 -
            16777216 * a7 * b2 * h ^ 54 + 67108864 * b1 * h ^ 62) /
          (67108864 * h ^ 63) :=
    depressedW810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda hh hN
  simp only [terminalMuResidual810, hL, hA, hB, hC, hD0, hE0, hF0, hG0, hP, hQ,
    hR, hS, hT0, hU0, hV0, hW0, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810,
    zetaResidual810, etaResidual810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h128, h256, h512, h1024, h2048,
    h4096, h8192, h16384, h32768, h65536, h131072, h262144, h16777216,
    h67108864, h17179869184, hh14, hh21, hh28, hh35, hh42, hh49, hh56,
    hh63, hh84]
  ring

end BridgeMuResidual810

/-! ## Degree-`5` depressed Jacobian coefficient and `d μ = 0` -/

section DepressedRow810BridgeFive

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`5` Jacobian coefficient is
exactly `6 R G' + 5 S F' + 4 T E' + 3 U D' + 2 V C' + W B'
- F S' - 2 E T' - 3 D U' - 4 C V' - 5 B W' - 6 A X'`. -/
theorem differentialJacobian_coeff_5_monicOcticDecic_bridge
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 5 =
      (6 : F) * g.coeff 6 * d (f.coeff 0) +
        (5 : F) * g.coeff 5 * d (f.coeff 1) +
        (4 : F) * g.coeff 4 * d (f.coeff 2) +
        (3 : F) * g.coeff 3 * d (f.coeff 3) +
        (2 : F) * g.coeff 2 * d (f.coeff 4) +
        g.coeff 1 * d (f.coeff 5) -
          f.coeff 1 * d (g.coeff 5) -
          (2 : F) * f.coeff 2 * d (g.coeff 4) -
          (3 : F) * f.coeff 3 * d (g.coeff 3) -
          (4 : F) * f.coeff 4 * d (g.coeff 2) -
          (5 : F) * f.coeff 5 * d (g.coeff 1) -
          (6 : F) * f.coeff 6 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :
      Finset (ℕ × ℕ)) =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1),
        (5, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne05_14 : ((0, 5) : ℕ × ℕ) ≠ (1, 4) := by decide
  have hne05_23 : ((0, 5) : ℕ × ℕ) ≠ (2, 3) := by decide
  have hne05_32 : ((0, 5) : ℕ × ℕ) ≠ (3, 2) := by decide
  have hne05_41 : ((0, 5) : ℕ × ℕ) ≠ (4, 1) := by decide
  have hne05_50 : ((0, 5) : ℕ × ℕ) ≠ (5, 0) := by decide
  have hne14_23 : ((1, 4) : ℕ × ℕ) ≠ (2, 3) := by decide
  have hne14_32 : ((1, 4) : ℕ × ℕ) ≠ (3, 2) := by decide
  have hne14_41 : ((1, 4) : ℕ × ℕ) ≠ (4, 1) := by decide
  have hne14_50 : ((1, 4) : ℕ × ℕ) ≠ (5, 0) := by decide
  have hne23_32 : ((2, 3) : ℕ × ℕ) ≠ (3, 2) := by decide
  have hne23_41 : ((2, 3) : ℕ × ℕ) ≠ (4, 1) := by decide
  have hne23_50 : ((2, 3) : ℕ × ℕ) ≠ (5, 0) := by decide
  have hne32_41 : ((3, 2) : ℕ × ℕ) ≠ (4, 1) := by decide
  have hne32_50 : ((3, 2) : ℕ × ℕ) ≠ (5, 0) := by decide
  have hne41_50 : ((4, 1) : ℕ × ℕ) ≠ (5, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 5 =
        (6 : F) * g.coeff 6 * d (f.coeff 0) +
          (5 : F) * g.coeff 5 * d (f.coeff 1) +
          (4 : F) * g.coeff 4 * d (f.coeff 2) +
          (3 : F) * g.coeff 3 * d (f.coeff 3) +
          (2 : F) * g.coeff 2 * d (f.coeff 4) +
          g.coeff 1 * d (f.coeff 5) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 5 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne05_14, hne05_23, hne05_32, hne05_41, hne05_50]),
        Finset.sum_insert (by simp [hne14_23, hne14_32, hne14_41, hne14_50]),
        Finset.sum_insert (by simp [hne23_32, hne23_41, hne23_50]),
        Finset.sum_insert (by simp [hne32_41, hne32_50]),
        Finset.sum_insert (by simp [hne41_50]),
        Finset.sum_singleton]
      ring
    have hder5 : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0 : g.derivative.coeff 0 = g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder5, hder4, hder3, hder2, hder1, hder0]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 5 =
        f.coeff 1 * d (g.coeff 5) +
          (2 : F) * f.coeff 2 * d (g.coeff 4) +
          (3 : F) * f.coeff 3 * d (g.coeff 3) +
          (4 : F) * f.coeff 4 * d (g.coeff 2) +
          (5 : F) * f.coeff 5 * d (g.coeff 1) +
          (6 : F) * f.coeff 6 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 4 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne05_14, hne05_23, hne05_32, hne05_41, hne05_50]),
        Finset.sum_insert (by simp [hne14_23, hne14_32, hne14_41, hne14_50]),
        Finset.sum_insert (by simp [hne23_32, hne23_41, hne23_50]),
        Finset.sum_insert (by simp [hne32_41, hne32_50]),
        Finset.sum_insert (by simp [hne41_50]),
        Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder4 : f.derivative.coeff 4 = (5 : F) * f.coeff 5 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder5 : f.derivative.coeff 5 = (6 : F) * f.coeff 6 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder2, hder3, hder4, hder5]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

set_option maxHeartbeats 80000000 in
theorem terminalMuResidual810_deriv_zero
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0)
    (heta : d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0)
    (hrow8 : (9 : F) * L * d G0 + (8 : F) * P * d F0 +
        (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A -
        F0 * d P - (2 : F) * E0 * d Q -
        (3 : F) * D0 * d R - (4 : F) * C0 * d S0 -
        (5 : F) * B * d T0 - (6 : F) * A * d U0 -
        (8 : F) * d W0 = 0)
    (hrow7 : (8 : F) * P * d G0 + (7 : F) * Q * d F0 +
        (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A -
        F0 * d Q - (2 : F) * E0 * d R -
        (3 : F) * D0 * d S0 - (4 : F) * C0 * d T0 -
        (5 : F) * B * d U0 - (6 : F) * A * d V0 -
        (8 : F) * d X0 = 0)
    (hrow : (6 : F) * R * d G0 + (5 : F) * S0 * d F0 +
        (4 : F) * T0 * d E0 + (3 : F) * U0 * d D0 +
        (2 : F) * V0 * d C0 + W0 * d B -
        F0 * d S0 - (2 : F) * E0 * d T0 -
        (3 : F) * D0 * d U0 - (4 : F) * C0 * d V0 -
        (5 : F) * B * d W0 - (6 : F) * A * d X0 = 0) :
    d (terminalMuResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 := by
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
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h35 : d (35 : F) = 0 := d.map_natCast 35
  have h63 : d (63 : F) = 0 := d.map_natCast 63
  have h64 : d (64 : F) = 0 := d.map_natCast 64
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h315 : d (315 : F) = 0 := d.map_natCast 315
  have h512 : d (512 : F) = 0 := d.map_natCast 512
  have h1024 : d (1024 : F) = 0 := d.map_natCast 1024
  have h2048 : d (2048 : F) = 0 := d.map_natCast 2048
  have h32768 : d (32768 : F) = 0 := d.map_natCast 32768
  have h77 : d (77 : F) = 0 := d.map_natCast 77
  have h105 : d (105 : F) = 0 := d.map_natCast 105
  have h8192 : d (8192 : F) = 0 := d.map_natCast 8192
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_inv, h2]
  have h14 : d (1 / 4 : F) = 0 := by
    simp [Derivation.leibniz_inv, h4]
  have h18 : d (1 / 8 : F) = 0 := by
    simp [Derivation.leibniz_inv, h8]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h78 : d (7 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h7]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h58 : d (5 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h5]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h5]
  have h316 : d (3 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h3]
  have h532 : d (5 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h5]
  have h15128 : d (15 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h15]
  have h5128 : d (5 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h5]
  have h7128 : d (7 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h7]
  have h9128 : d (9 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h9]
  have h1564 : d (15 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h15]
  have h964 : d (9 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h9]
  have h764 : d (7 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h7]
  have h35512 : d (35 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h35]
  have h211024 : d (21 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h21]
  have h631024 : d (63 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h63]
  have h31532768 : d (315 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, h315]
  have h778192 : d (77 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h77]
  have h3158192 : d (315 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h315]
  have h1051024 : d (105 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h105]
  have h63512 : d (63 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h63]
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h3]
  have h352048 : d (35 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h35]

  have h13 : d (13 : F) = 0 := d.map_natCast 13
  have h17 : d (17 : F) = 0 := d.map_natCast 17
  have h75 : d (75 : F) = 0 := d.map_natCast 75
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h85 : d (85 : F) = 0 := d.map_natCast 85
  have h189 : d (189 : F) = 0 := d.map_natCast 189
  have h441 : d (441 : F) = 0 := d.map_natCast 441
  have h455 : d (455 : F) = 0 := d.map_natCast 455
  have h1071 : d (1071 : F) = 0 := d.map_natCast 1071
  have h4096 : d (4096 : F) = 0 := d.map_natCast 4096
  have h16384 : d (16384 : F) = 0 := d.map_natCast 16384
  have h65536n : d (65536 : F) = 0 := d.map_natCast 65536
  have h44132768 : d (441 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, h441]
  have h44165536 : d (441 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, h441]
  have h4558192 : d (455 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h455]
  have h107116384 : d (1071 / 16384 : F) = 0 := by
    simp [Derivation.leibniz_div, h16384, h1071]
  have h1894096 : d (189 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, h189]
  have h851024 : d (85 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h85]
  have h751024 : d (75 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h75]
  have h811024 : d (81 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h81]
  have h932 : d (9 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h9]
  have h732 : d (7 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h7]
  have h21128 : d (21 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h21]
  have h35128 : d (35 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h35]
  have h771024 : d (77 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h77]

  have h256 : d (256 : F) = 0 := d.map_natCast 256
  have h45 : d (45 : F) = 0 := d.map_natCast 45
  have h225 : d (225 : F) = 0 := d.map_natCast 225
  have h385 : d (385 : F) = 0 := d.map_natCast 385
  have h945 : d (945 : F) = 0 := d.map_natCast 945
  have h45256 : d (45 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h45]
  have h452048 : d (45 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h45]
  have h1894096' : d (189 / 4096 : F) = 0 := by
    simp [Derivation.leibniz_div, h4096, h189]
  have h94532768 : d (945 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, h945]
  have h38565536 : d (385 / 65536 : F) = 0 := by
    simp [Derivation.leibniz_div, h65536n, h385]
  have h2251024 : d (225 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h225]
  have h7256 : d (7 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h7]
  have h3858192 : d (385 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h385]
  have h1532 : d (15 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h15]
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_inv, h16]
  have h35256 : d (35 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256, h35]
  have hPderiv : d P = (5 / 4 : F) * d A := by
    have halpha' : d P - (5 / 4 : F) * d A = 0 := by
      simpa [alphaResidual810, map_sub, Derivation.leibniz, h54, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hQderiv : d Q = (5 / 4 : F) * d B + (9 / 8 : F) * L * d A := by
    have hbeta' :
        d Q - (5 / 4 : F) * d B - (9 / 8 : F) * L * d A = 0 := by
      simpa [betaResidual810, map_sub, Derivation.leibniz, h54, h98, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    linear_combination hbeta'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz]
    ring
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz]
    ring
  have hcub : d (A ^ 3) = (3 : F) * A ^ 2 * d A := by
    have h2A : d (A ^ 2) = (2 : F) * A * d A := by
      simpa [pow_two] using hsq
    simp [pow_three, Derivation.leibniz, h2A]
    ring
  have hcubB : d (B ^ 3) = (3 : F) * B ^ 2 * d B := by
    have h2B : d (B ^ 2) = (2 : F) * B * d B := by
      simpa [pow_two] using hsqB
    simp [pow_three, Derivation.leibniz, h2B]
    ring
  have hquar : d (A ^ 4) = (4 : F) * A ^ 3 * d A := by
    have : A ^ 4 = A ^ 3 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hcub]
    ring
  have hquint : d (A ^ 5) = (5 : F) * A ^ 4 * d A := by
    have : A ^ 5 = A ^ 4 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquar]
    ring
  have hsqD : d (D0 * D0) = (2 : F) * D0 * d D0 := by
    simp [Derivation.leibniz]
    ring
  have hsqE : d (E0 * E0) = (2 : F) * E0 * d E0 := by
    simp [Derivation.leibniz]
    ring
  have hcubC : d (C0 ^ 3) = (3 : F) * C0 ^ 2 * d C0 := by
    have h2C : d (C0 ^ 2) = (2 : F) * C0 * d C0 := by
      simpa [pow_two] using hsqC
    simp [pow_three, Derivation.leibniz, h2C]
    ring
  have hquarB : d (B ^ 4) = (4 : F) * B ^ 3 * d B := by
    have : B ^ 4 = B ^ 3 * B := by ring
    rw [this]
    simp [Derivation.leibniz, hcubB]
    ring
  have hsextA : d (A ^ 6) = (6 : F) * A ^ 5 * d A := by
    have : A ^ 6 = A ^ 5 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquint]
    ring
  have hgamma_id :
      d (gammaResidual810 L A B C0 P R) =
        d R - ((5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
          (9 / 8 : F) * L * d B + alphaResidual810 A P * d A) := by
    simp only [gammaResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h532, hL, halpha, zero_mul, add_zero, mul_zero, pow_two, hsq]
    ring
  have hRderiv' :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + alphaResidual810 A P * d A := by
    linear_combination hgamma_id.symm + hgamma
  have hRderiv :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + (P - (5 / 4 : F) * A) * d A := by
    rw [hRderiv']
    simp only [alphaResidual810]
  have hdelta_id :
      d (deltaResidual810 L A B C0 D0 P Q S0) =
        d S0 - ((5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
          alphaResidual810 A P * d B +
          (7 / 8 : F) * betaResidual810 L A B Q * d A +
          (5 / 16 : F) * (A * d B + B * d A) +
          (9 / 64 : F) * L * A * d A) := by
    unfold deltaResidual810
    simp [map_sub, map_add, Derivation.leibniz, h54, h98, h78, h516, h964,
      h9128, hL, halpha, hbeta, zero_mul, add_zero, mul_zero, pow_two, hsq]
    ring
  have hSderiv' :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        alphaResidual810 A P * d B +
        (7 / 8 : F) * betaResidual810 L A B Q * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    linear_combination hdelta_id.symm + hdelta
  have hSderiv :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        (P - (5 / 4 : F) * A) * d B +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    rw [hSderiv']
    simp [alphaResidual810, betaResidual810]
  have hepsilon_id :
      d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) =
        d T0 - ((5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
          (5 / 16 : F) * (A * d C0 + C0 * d A) -
          (15 / 128 : F) * A ^ 2 * d A +
          L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
          alphaResidual810 A P * d C0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d B +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d A) := by
    simp only [epsilonResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h78, h34, h532, h516, h5128, h15128, h964, hL, halpha, hbeta,
      hgamma, zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hcub]
    ring
  have hTderiv' :
      d T0 = (5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
        (5 / 16 : F) * (A * d C0 + C0 * d A) -
        (15 / 128 : F) * A ^ 2 * d A +
        L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
        alphaResidual810 A P * d C0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d B +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d A := by
    linear_combination hepsilon_id.symm + hepsilon
  have hTderiv :
      d T0 = (5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
        (5 / 16 : F) * (A * d C0 + C0 * d A) -
        (15 / 128 : F) * A ^ 2 * d A +
        L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
        (P - (5 / 4 : F) * A) * d C0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d B +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d A := by
    rw [hTderiv']
    simp [gammaResidual810, alphaResidual810, betaResidual810]
  have hzeta_id :
      d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) =
        d U0 - ((5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
          alphaResidual810 A P * d D0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d C0 +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d B +
          (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d A +
          (5 / 16 : F) * (A * d D0 + D0 * d A) +
          (5 / 16 : F) * (B * d C0 + C0 * d B) -
          (7 / 64 : F) * betaResidual810 L A B Q * A * d A -
          (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
          (63 / 1024 : F) * L * A ^ 2 * d A +
          (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
          (9 / 64 : F) * L * B * d B) := by
    simp only [zetaResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h78, h34, h58, h516, h7128, h15128, h211024, h964, h9128, hL,
      halpha, hbeta, hgamma, hdelta, zero_mul, add_zero, mul_zero, pow_two,
      hsq, hsqB, hcub]
    ring
  have hUderiv' :
      d U0 = (5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
        alphaResidual810 A P * d D0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d C0 +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d B +
        (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d A +
        (5 / 16 : F) * (A * d D0 + D0 * d A) +
        (5 / 16 : F) * (B * d C0 + C0 * d B) -
        (7 / 64 : F) * betaResidual810 L A B Q * A * d A -
        (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
        (63 / 1024 : F) * L * A ^ 2 * d A +
        (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
        (9 / 64 : F) * L * B * d B := by
    linear_combination hzeta_id.symm + hzeta
  have hUderiv :
      d U0 = (5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
        (P - (5 / 4 : F) * A) * d D0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d C0 +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d B +
        (5 / 8 : F) * (S0 - ((5 / 4 : F) * D0 + (9 / 8 : F) * L * C0 +
          (P - (5 / 4 : F) * A) * B +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A +
          (5 / 16 : F) * A * B + (9 / 128 : F) * L * A ^ 2)) * d A +
        (5 / 16 : F) * (A * d D0 + D0 * d A) +
        (5 / 16 : F) * (B * d C0 + C0 * d B) -
        (7 / 64 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A *
          d A -
        (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
        (63 / 1024 : F) * L * A ^ 2 * d A +
        (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
        (9 / 64 : F) * L * B * d B := by
    rw [hUderiv']
    simp [alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810]
  have heta_id :
      d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) =
        d V0 - ((5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
          alphaResidual810 A P * d E0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d D0 +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d C0 +
          (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d B +
          (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * d A +
          (5 / 16 : F) * (A * d E0 + E0 * d A) +
          (5 / 16 : F) * (B * d D0 + D0 * d B) +
          (5 / 16 : F) * C0 * d C0 -
          (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
          (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
          (35 / 512 : F) * A ^ 3 * d A +
          (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
          (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
          (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
          (7 / 64 : F) * betaResidual810 L A B Q * (A * d B + B * d A) -
          (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * d A) := by
    simp only [etaResidual810, map_sub, map_add, Derivation.leibniz, h12,
      h14, h18, h54, h98, h78, h34, h58, h516, h532, h15128, h352048, h964,
      h631024, h764, h332, hL, halpha, hbeta, hgamma, hdelta, hepsilon,
      zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hsqC, hcub, hquar]
    ring
  have hVderiv' :
      d V0 = (5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
        alphaResidual810 A P * d E0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d D0 +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d C0 +
        (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d B +
        (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * d A +
        (5 / 16 : F) * (A * d E0 + E0 * d A) +
        (5 / 16 : F) * (B * d D0 + D0 * d B) +
        (5 / 16 : F) * C0 * d C0 -
        (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
        (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
        (35 / 512 : F) * A ^ 3 * d A +
        (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
        (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
        (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
        (7 / 64 : F) * betaResidual810 L A B Q * (A * d B + B * d A) -
        (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * d A := by
    linear_combination heta_id.symm + heta
  have hVderiv :
      d V0 = (5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
        (P - (5 / 4 : F) * A) * d E0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d D0 +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d C0 +
        (5 / 8 : F) * (S0 - ((5 / 4 : F) * D0 + (9 / 8 : F) * L * C0 +
          (P - (5 / 4 : F) * A) * B +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A +
          (5 / 16 : F) * A * B + (9 / 128 : F) * L * A ^ 2)) * d B +
        (1 / 2 : F) * (T0 - ((5 / 4 : F) * E0 + (5 / 32 : F) * B ^ 2 +
          (5 / 16 : F) * A * C0 - (5 / 128 : F) * A ^ 3 +
          L * ((9 / 8 : F) * D0 + (9 / 64 : F) * A * B) +
          (P - (5 / 4 : F) * A) * C0 +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * B +
          (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
            (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * A)) * d A +
        (5 / 16 : F) * (A * d E0 + E0 * d A) +
        (5 / 16 : F) * (B * d D0 + D0 * d B) +
        (5 / 16 : F) * C0 * d C0 -
        (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
        (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
        (35 / 512 : F) * A ^ 3 * d A +
        (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
        (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
        (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
        (7 / 64 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) *
          (A * d B + B * d A) -
        (3 / 16 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * A * d A := by
    rw [hVderiv']
    simp [alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810, epsilonResidual810]
  have hWderiv :
      d W0 = (9 / 8 : F) * L * d G0 + P * d F0 +
        (7 / 8 : F) * Q * d E0 + (3 / 4 : F) * R * d D0 +
        (5 / 8 : F) * S0 * d C0 + (1 / 2 : F) * T0 * d B +
        (3 / 8 : F) * U0 * d A -
        (1 / 8 : F) * F0 * d P - (1 / 4 : F) * E0 * d Q -
        (3 / 8 : F) * D0 * d R - (1 / 2 : F) * C0 * d S0 -
        (5 / 8 : F) * B * d T0 - (3 / 4 : F) * A * d U0 := by
    linear_combination (-1 / 8 : F) * hrow8
  have hXderiv :
      d X0 = P * d G0 + (7 / 8 : F) * Q * d F0 +
        (3 / 4 : F) * R * d E0 + (5 / 8 : F) * S0 * d D0 +
        (1 / 2 : F) * T0 * d C0 + (3 / 8 : F) * U0 * d B +
        (1 / 4 : F) * V0 * d A -
        (1 / 8 : F) * F0 * d Q - (1 / 4 : F) * E0 * d R -
        (3 / 8 : F) * D0 * d S0 - (1 / 2 : F) * C0 * d T0 -
        (5 / 8 : F) * B * d U0 - (3 / 4 : F) * A * d V0 := by
    linear_combination (-1 / 8 : F) * hrow7
  have hrow_red := hrow
  rw [hWderiv, hXderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv] at hrow_red
  simp only [terminalMuResidual810, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810,
    zetaResidual810, etaResidual810, map_sub, map_add, Derivation.leibniz,
    h12, h14, h18, h38, h54, h98, h78, h34, h58, h516, h316, h532, h15128,
    h5128, h7128, h9128, h1564, h964, h764, h35512, h211024, h631024,
    h31532768, h778192, h3158192, h1051024, h63512, h332, h352048, hL,
    h44132768, h44165536, h4558192, h107116384, h1894096, h851024, h751024,
    h811024, h932, h732, h21128, h35128, h771024, h45256, h452048,
    h1894096', h94532768, h38565536, h2251024, h7256, h3858192, h1532,
    h116, h35256, zero_mul, add_zero, mul_zero, pow_two, hsq,
    hsqB, hsqC, hsqD, hsqE, hcub, hcubB, hcubC, hquar, hquarB, hquint,
    hsextA]
  rw [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv]
  linear_combination (1 / 8 : F) * hrow_red

end DepressedRow810BridgeFive

section NonzeroTerminalMuClearing810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- The eleventh octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁸⁴`. -/
theorem nonzeroFace810_terminalMuPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eta : k,
      terminalClearedMuDefect810 h0 (p.coeff 7) (p.coeff 6) (p.coeff 5)
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * h0 ^ 84 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
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
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
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
  have hg6 :
      g.coeff 6 =
        depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedR810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 :
      g.coeff 5 =
        depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedS810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 :
      g.coeff 4 =
        depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedT810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg2 :
      g.coeff 2 =
        depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedV810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg3 :
      g.coeff 3 =
        depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedU810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg1 :
      g.coeff 1 =
        depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedW810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hg8' :
      g.coeff 8 =
        depressedP810 h (octicDepressionR810 h a7) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8]
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
    have hx := ratFuncDerivation46_polynomial (Polynomial.C (-lambda / 4) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow15 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_15_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 15) hbracket
    simpa [f, g, Polynomial.coeff_C, show (15 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow14 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 5) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_14_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 14) hbracket
    simpa [f, g, Polynomial.coeff_C, show (14 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow13 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 5) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 6) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 8) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_13_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow12 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 5) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 6) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 8) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 7) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_12_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 12) hbracket
    simpa [f, g, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 3) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 4) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 5) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 8) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 7) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 6) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 3) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 4) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 5) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 6) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 5) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 4) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 3) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 4) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 5) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 7) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 6) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 5) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 3) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 4) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 5) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 6) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 5) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 4) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 3) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 2) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 3) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 4) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 5) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 6) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 4) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 3) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 2) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicOcticDecic_bridge
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow5 :
      (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 0) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 1) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 2) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 3) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 4) +
        g.coeff 1 * ratFuncDerivation68 (f.coeff 5) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 5) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 3) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 2) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 1) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_5_monicOcticDecic_bridge
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 5) hbracket
    simpa [f, g, Polynomial.coeff_C, show (5 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr

  have hf6 : f.coeff 6 = depressedA810 h (octicDepressionR810 h a7) a7 a6 := by
    dsimp only [f, depressedA810, a7, a6]
    rw [hpDep, coeff_depressedOctic68_six]
  have hf5 : f.coeff 5 =
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 := by
    dsimp only [f, depressedB810, a7, a6, a5]
    rw [hpDep, coeff_depressedOctic68_five]
  have hf4 : f.coeff 4 =
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 := by
    dsimp only [f, depressedC810, a7, a6, a5, a4]
    rw [hpDep, coeff_depressedOctic68_four]
  have hf3 : f.coeff 3 =
      depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 := by
    dsimp only [f, depressedD810, a7, a6, a5, a4, a3]
    rw [hpDep, coeff_depressedOctic68_three]
  have hf2 : f.coeff 2 =
      depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 := by
    dsimp only [f, depressedE810, a7, a6, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedOctic68_two]
  have hf1 : f.coeff 1 =
      depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedF810, a7, a6, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedOctic68_one]
  have hf0 : f.coeff 0 =
      depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedG810, a7, a6, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedOctic68_zero]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual810 (f.coeff 6) (g.coeff 8)) = 0 :=
    alphaResidual810_deriv_zero ratFuncDerivation68 (f.coeff 6)
      (g.coeff 8) hrow15
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (g.coeff 7)) = 0 :=
    betaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (g.coeff 7) hLconst (by simpa using hrow14)
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow13)
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow12)
  have hepsilon0 :
      ratFuncDerivation68
        (epsilonResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha0
      hbeta0 hgamma0 (by simpa using hrow11)
  have hzeta0 :
      ratFuncDerivation68
        (zetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
      (g.coeff 3) hLconst halpha0 hbeta0 hgamma0 hdelta0
      (by simpa using hrow10)
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 2)) = 0 :=
    etaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 2) hLconst halpha0 hbeta0
      hgamma0 hdelta0 hepsilon0 (by simpa using hrow9)
  have hmu0deriv :
      ratFuncDerivation68
        (terminalMuResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1)) = 0 :=
    terminalMuResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (g.coeff 0) hLconst halpha0 hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0
      heta0deriv (by simpa using hrow8)
      (by simpa using hrow7) (by simpa using hrow5)
  obtain ⟨mu0, hmu0⟩ :
      ∃ a : k,
        terminalMuResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 1) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hmu0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (terminalClearedMuDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda) =
        (17179869184 : RatFunc k) * h ^ 84 *
          terminalMuResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 1) := by
    have hF := terminalMuDefect_eq_cleared810 h a7 a6 a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh (by convert hNrat)
    have hg9L : g.coeff 9 =
        depressedL810 h (octicDepressionR810 h a7) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    simpa [terminalClearedMuDefect810, map_sub, map_mul, map_pow,
      map_ofNat, map_neg, map_add, RatFunc.algebraMap_C, h, a7, a6, a5,
      a4, a3, a2, a1, a0, b8, b7, b6, b5, b4, b3, b2, b1, terminalMuResidual810,
      alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810, epsilonResidual810, zetaResidual810, etaResidual810, hf6, hf5, hf4, hf3, hf2, hf1,
      hf0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (terminalClearedMuDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (17179869184 * mu0) * h0 ^ 84) := by
    rw [hclear, hmu0]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  refine ⟨17179869184 * mu0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end NonzeroTerminalMuClearing810

/-! ## Jet-peeled clearing of the degree-`5` integral -/

section BridgeMuJet810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 40000000 in
/-- Order-`72` head of the jet-substituted cleared `μ` defect: the
coefficient of `h⁷²` after the seventeenth-face jet
`a₇ = h⁶ t₀`, `a₆ = h⁴ v₁`, `a₅ = h² u₁`, `b₈ = h⁶ s₁`, `b₇ = h⁴ w₁`,
`b₆ = h² b₆₂` is substituted into `terminalClearedMuDefect810`. -/
def bridgeMuJetHead810 (t0 v1 u1 s1 w1 b62 a4 b5 : R) : R :=
    (4697620480 : R) * a4 ^ 3
    - (4831838208 : R) * a4 ^ 2 * b62
    - (15502147584 : R) * a4 ^ 2 * s1 * t0 ^ 2
    + (11274289152 : R) * a4 ^ 2 * s1 * v1
    + (9865003008 : R) * a4 ^ 2 * w1 * t0
    - (1513881600 : R) * a4 ^ 2 * t0 ^ 4
    + (29066526720 : R) * a4 ^ 2 * t0 ^ 2 * v1
    - (22900899840 : R) * a4 ^ 2 * t0 * u1
    - (19377684480 : R) * a4 ^ 2 * v1 ^ 2
    - (6459228160 : R) * a4 * b5 * t0 ^ 3
    + (14092861440 : R) * a4 * b5 * t0 * v1
    - (8053063680 : R) * a4 * b5 * u1
    + (7266631680 : R) * a4 * b62 * t0 ^ 4
    - (23253221376 : R) * a4 * b62 * t0 ^ 2 * v1
    + (16911433728 : R) * a4 * b62 * t0 * u1
    + (8455716864 : R) * a4 * b62 * v1 ^ 2
    + (8820883456 : R) * a4 * s1 * t0 ^ 6
    - (46022000640 : R) * a4 * s1 * t0 ^ 4 * v1
    + (38755368960 : R) * a4 * s1 * t0 ^ 3 * u1
    + (58133053440 : R) * a4 * s1 * t0 ^ 2 * v1 ^ 2
    - (62008590336 : R) * a4 * s1 * t0 * u1 * v1
    + (11274289152 : R) * a4 * s1 * u1 ^ 2
    - (10334765056 : R) * a4 * s1 * v1 ^ 3
    - (8053850112 : R) * a4 * w1 * t0 ^ 5
    + (33910947840 : R) * a4 * w1 * t0 ^ 3 * v1
    - (27128758272 : R) * a4 * w1 * t0 ^ 2 * u1
    - (27128758272 : R) * a4 * w1 * t0 * v1 ^ 2
    + (19730006016 : R) * a4 * w1 * u1 * v1
    - (1661299200 : R) * a4 * t0 ^ 8
    + (1438187520 : R) * a4 * t0 ^ 5 * u1
    + (35954688000 : R) * a4 * t0 ^ 4 * v1 ^ 2
    - (66610790400 : R) * a4 * t0 ^ 3 * u1 * v1
    + (29066526720 : R) * a4 * t0 ^ 2 * u1 ^ 2
    - (60555264000 : R) * a4 * t0 ^ 2 * v1 ^ 3
    + (101732843520 : R) * a4 * t0 * u1 * v1 ^ 2
    - (38755368960 : R) * a4 * u1 ^ 2 * v1
    + (12111052800 : R) * a4 * v1 ^ 4
    + (787578880 : R) * b5 * t0 ^ 7
    - (5752750080 : R) * b5 * t0 ^ 5 * v1
    + (6055526400 : R) * b5 * t0 ^ 4 * u1
    + (12111052800 : R) * b5 * t0 ^ 3 * v1 ^ 2
    - (19377684480 : R) * b5 * t0 ^ 2 * u1 * v1
    + (7046430720 : R) * b5 * t0 * u1 ^ 2
    - (6459228160 : R) * b5 * t0 * v1 ^ 3
    + (7046430720 : R) * b5 * u1 * v1 ^ 2
    - (797423616 : R) * b62 * t0 ^ 8
    + (6615662592 : R) * b62 * t0 ^ 6 * v1
    - (6903300096 : R) * b62 * t0 ^ 5 * u1
    - (17258250240 : R) * b62 * t0 ^ 4 * v1 ^ 2
    + (29066526720 : R) * b62 * t0 ^ 3 * u1 * v1
    - (11626610688 : R) * b62 * t0 ^ 2 * u1 ^ 2
    + (14533263360 : R) * b62 * t0 ^ 2 * v1 ^ 3
    - (23253221376 : R) * b62 * t0 * u1 * v1 ^ 2
    + (8455716864 : R) * b62 * u1 ^ 2 * v1
    - (1937768448 : R) * b62 * v1 ^ 4
    - (801115392 : R) * s1 * t0 ^ 10
    + (8240044032 : R) * s1 * t0 ^ 8 * v1
    - (8505851904 : R) * s1 * t0 ^ 7 * u1
    - (29770481664 : R) * s1 * t0 ^ 6 * v1 ^ 2
    + (52925300736 : R) * s1 * t0 ^ 5 * u1 * v1
    - (23011000320 : R) * s1 * t0 ^ 4 * u1 ^ 2
    + (44104417280 : R) * s1 * t0 ^ 4 * v1 ^ 3
    - (92044001280 : R) * s1 * t0 ^ 3 * u1 * v1 ^ 2
    + (58133053440 : R) * s1 * t0 ^ 2 * u1 ^ 2 * v1
    - (23011000320 : R) * s1 * t0 ^ 2 * v1 ^ 4
    - (10334765056 : R) * s1 * t0 * u1 ^ 3
    + (38755368960 : R) * s1 * t0 * u1 * v1 ^ 3
    - (15502147584 : R) * s1 * u1 ^ 2 * v1 ^ 2
    + (1937768448 : R) * s1 * v1 ^ 5
    + (801115392 : R) * w1 * t0 ^ 9
    - (7442620416 : R) * w1 * t0 ^ 7 * v1
    + (7718273024 : R) * w1 * t0 ^ 6 * u1
    + (23154819072 : R) * w1 * t0 ^ 5 * v1 ^ 2
    - (40269250560 : R) * w1 * t0 ^ 4 * u1 * v1
    + (16955473920 : R) * w1 * t0 ^ 3 * u1 ^ 2
    - (26846167040 : R) * w1 * t0 ^ 3 * v1 ^ 3
    + (50866421760 : R) * w1 * t0 ^ 2 * u1 * v1 ^ 2
    - (27128758272 : R) * w1 * t0 * u1 ^ 2 * v1
    + (8477736960 : R) * w1 * t0 * v1 ^ 4
    + (3288334336 : R) * w1 * u1 ^ 3
    - (9042919424 : R) * w1 * u1 * v1 ^ 3
    + (203408205 : R) * t0 ^ 12
    - (1502091360 : R) * t0 ^ 10 * v1
    + (1573619520 : R) * t0 ^ 9 * u1
    + (1287506880 : R) * t0 ^ 8 * v1 ^ 2
    - (1329039360 : R) * t0 ^ 7 * u1 * v1
    + (12404367360 : R) * t0 ^ 6 * v1 ^ 3
    - (37213102080 : R) * t0 ^ 5 * u1 * v1 ^ 2
    + (35954688000 : R) * t0 ^ 4 * u1 ^ 2 * v1
    - (31010918400 : R) * t0 ^ 4 * v1 ^ 4
    - (11101798400 : R) * t0 ^ 3 * u1 ^ 3
    + (91085209600 : R) * t0 ^ 3 * u1 * v1 ^ 3
    - (90832896000 : R) * t0 ^ 2 * u1 ^ 2 * v1 ^ 2
    + (20134625280 : R) * t0 ^ 2 * v1 ^ 5
    + (33910947840 : R) * t0 * u1 ^ 3 * v1
    - (43902566400 : R) * t0 * u1 * v1 ^ 4
    - (3229614080 : R) * u1 ^ 4
    + (24222105600 : R) * u1 ^ 2 * v1 ^ 3
    - (1917583360 : R) * v1 ^ 6

set_option maxHeartbeats 40000000 in
/-- Tail of the jet-substituted cleared `μ` defect above order `h⁷³`. -/
def bridgeMuJetTail810
    (hh t0 v1 u1 s1 w1 b62 a4 a3 a2 a1 a0 b5 b4 b3 b2 b1 lam : R) : R :=
    (2906652672 : R) * hh ^ 8 * lam * a0 * t0 ^ 3
    - (6341787648 : R) * hh ^ 8 * lam * a0 * t0 * v1
    + (3623878656 : R) * hh ^ 8 * lam * a0 * u1
    - (16106127360 : R) * hh ^ 7 * a4 * a0
    - (16106127360 : R) * hh ^ 7 * a3 * a1
    - (8053063680 : R) * hh ^ 7 * a2 ^ 2
    + (12884901888 : R) * hh ^ 7 * a0 * b62
    + (11274289152 : R) * hh ^ 7 * a0 * s1 * t0 ^ 2
    - (12884901888 : R) * hh ^ 7 * a0 * s1 * v1
    - (11274289152 : R) * hh ^ 7 * a0 * w1 * t0
    - (2422210560 : R) * hh ^ 7 * a0 * t0 ^ 4
    - (7046430720 : R) * hh ^ 7 * a0 * t0 ^ 2 * v1
    + (10066329600 : R) * hh ^ 7 * a0 * t0 * u1
    + (14092861440 : R) * hh ^ 7 * a0 * v1 ^ 2
    + (469762048 : R) * hh ^ 7 * b1 * t0 ^ 3
    - (1610612736 : R) * hh ^ 7 * b1 * t0 * v1
    + (2147483648 : R) * hh ^ 7 * b1 * u1
    + (3623878656 : R) * hh ^ 6 * lam * a4 * a1
    + (3623878656 : R) * hh ^ 6 * lam * a3 * a2
    - (2724986880 : R) * hh ^ 6 * lam * a1 * t0 ^ 4
    + (8719958016 : R) * hh ^ 6 * lam * a1 * t0 ^ 2 * v1
    - (6341787648 : R) * hh ^ 6 * lam * a1 * t0 * u1
    - (3170893824 : R) * hh ^ 6 * lam * a1 * v1 ^ 2
    + (10066329600 : R) * hh ^ 5 * a4 * a1 * t0
    + (4294967296 : R) * hh ^ 5 * a4 * b2
    + (10066329600 : R) * hh ^ 5 * a3 * a2 * t0
    + (6442450944 : R) * hh ^ 5 * a3 * b3
    + (8589934592 : R) * hh ^ 5 * a2 * b4
    + (10737418240 : R) * hh ^ 5 * a1 * b5
    - (9663676416 : R) * hh ^ 5 * a1 * b62 * t0
    - (10334765056 : R) * hh ^ 5 * a1 * s1 * t0 ^ 3
    + (22548578304 : R) * hh ^ 5 * a1 * s1 * t0 * v1
    - (12884901888 : R) * hh ^ 5 * a1 * s1 * u1
    + (9865003008 : R) * hh ^ 5 * a1 * w1 * t0 ^ 2
    - (11274289152 : R) * hh ^ 5 * a1 * w1 * v1
    + (2119434240 : R) * hh ^ 5 * a1 * t0 ^ 5
    + (4844421120 : R) * hh ^ 5 * a1 * t0 ^ 3 * v1
    - (7046430720 : R) * hh ^ 5 * a1 * t0 ^ 2 * u1
    - (22900899840 : R) * hh ^ 5 * a1 * t0 * v1 ^ 2
    + (28185722880 : R) * hh ^ 5 * a1 * u1 * v1
    - (645922816 : R) * hh ^ 5 * b2 * t0 ^ 4
    + (2818572288 : R) * hh ^ 5 * b2 * t0 ^ 2 * v1
    - (3221225472 : R) * hh ^ 5 * b2 * t0 * u1
    - (1610612736 : R) * hh ^ 5 * b2 * v1 ^ 2
    - (6341787648 : R) * hh ^ 4 * lam * a4 * a2 * t0
    - (3170893824 : R) * hh ^ 4 * lam * a3 ^ 2 * t0
    + (2588737536 : R) * hh ^ 4 * lam * a2 * t0 ^ 5
    - (10899947520 : R) * hh ^ 4 * lam * a2 * t0 ^ 3 * v1
    + (8719958016 : R) * hh ^ 4 * lam * a2 * t0 ^ 2 * u1
    + (8719958016 : R) * hh ^ 4 * lam * a2 * t0 * v1 ^ 2
    - (6341787648 : R) * hh ^ 4 * lam * a2 * u1 * v1
    - (12884901888 : R) * hh ^ 3 * a4 * a2 * s1
    - (7046430720 : R) * hh ^ 3 * a4 * a2 * t0 ^ 2
    + (28185722880 : R) * hh ^ 3 * a4 * a2 * v1
    - (4831838208 : R) * hh ^ 3 * a4 * b3 * t0
    - (6442450944 : R) * hh ^ 3 * a3 ^ 2 * s1
    - (3523215360 : R) * hh ^ 3 * a3 ^ 2 * t0 ^ 2
    + (14092861440 : R) * hh ^ 3 * a3 ^ 2 * v1
    - (6442450944 : R) * hh ^ 3 * a3 * b4 * t0
    - (8053063680 : R) * hh ^ 3 * a2 * b5 * t0
    + (8455716864 : R) * hh ^ 3 * a2 * b62 * t0 ^ 2
    - (9663676416 : R) * hh ^ 3 * a2 * b62 * v1
    + (9688842240 : R) * hh ^ 3 * a2 * s1 * t0 ^ 4
    - (31004295168 : R) * hh ^ 3 * a2 * s1 * t0 ^ 2 * v1
    + (22548578304 : R) * hh ^ 3 * a2 * s1 * t0 * u1
    + (11274289152 : R) * hh ^ 3 * a2 * s1 * v1 ^ 2
    - (9042919424 : R) * hh ^ 3 * a2 * w1 * t0 ^ 3
    + (19730006016 : R) * hh ^ 3 * a2 * w1 * t0 * v1
    - (11274289152 : R) * hh ^ 3 * a2 * w1 * u1
    - (1917583360 : R) * hh ^ 3 * a2 * t0 ^ 6
    - (3027763200 : R) * hh ^ 3 * a2 * t0 ^ 4 * v1
    + (4844421120 : R) * hh ^ 3 * a2 * t0 ^ 3 * u1
    + (29066526720 : R) * hh ^ 3 * a2 * t0 ^ 2 * v1 ^ 2
    - (45801799680 : R) * hh ^ 3 * a2 * t0 * u1 * v1
    + (14092861440 : R) * hh ^ 3 * a2 * u1 ^ 2
    - (12918456320 : R) * hh ^ 3 * a2 * v1 ^ 3
    + (726663168 : R) * hh ^ 3 * b3 * t0 ^ 5
    - (3875536896 : R) * hh ^ 3 * b3 * t0 ^ 3 * v1
    + (4227858432 : R) * hh ^ 3 * b3 * t0 ^ 2 * u1
    + (4227858432 : R) * hh ^ 3 * b3 * t0 * v1 ^ 2
    - (4831838208 : R) * hh ^ 3 * b3 * u1 * v1
    + (8719958016 : R) * hh ^ 2 * lam * a4 * a3 * t0 ^ 2
    - (6341787648 : R) * hh ^ 2 * lam * a4 * a3 * v1
    - (2480873472 : R) * hh ^ 2 * lam * a3 * t0 ^ 6
    + (12943687680 : R) * hh ^ 2 * lam * a3 * t0 ^ 4 * v1
    - (10899947520 : R) * hh ^ 2 * lam * a3 * t0 ^ 3 * u1
    - (16349921280 : R) * hh ^ 2 * lam * a3 * t0 ^ 2 * v1 ^ 2
    + (17439916032 : R) * hh ^ 2 * lam * a3 * t0 * u1 * v1
    - (3170893824 : R) * hh ^ 2 * lam * a3 * u1 ^ 2
    + (2906652672 : R) * hh ^ 2 * lam * a3 * v1 ^ 3
    + (22548578304 : R) * hh * a4 * a3 * s1 * t0
    - (11274289152 : R) * hh * a4 * a3 * w1
    + (4844421120 : R) * hh * a4 * a3 * t0 ^ 3
    - (45801799680 : R) * hh * a4 * a3 * t0 * v1
    + (28185722880 : R) * hh * a4 * a3 * u1
    + (5637144576 : R) * hh * a4 * b4 * t0 ^ 2
    - (6442450944 : R) * hh * a4 * b4 * v1
    + (7046430720 : R) * hh * a3 * b5 * t0 ^ 2
    - (8053063680 : R) * hh * a3 * b5 * v1
    - (7751073792 : R) * hh * a3 * b62 * t0 ^ 3
    + (16911433728 : R) * hh * a3 * b62 * t0 * v1
    - (9663676416 : R) * hh * a3 * b62 * u1
    - (9204400128 : R) * hh * a3 * s1 * t0 ^ 5
    + (38755368960 : R) * hh * a3 * s1 * t0 ^ 3 * v1
    - (31004295168 : R) * hh * a3 * s1 * t0 ^ 2 * u1
    - (31004295168 : R) * hh * a3 * s1 * t0 * v1 ^ 2
    + (22548578304 : R) * hh * a3 * s1 * u1 * v1
    + (8477736960 : R) * hh * a3 * w1 * t0 ^ 4
    - (27128758272 : R) * hh * a3 * w1 * t0 ^ 2 * v1
    + (19730006016 : R) * hh * a3 * w1 * t0 * u1
    + (9865003008 : R) * hh * a3 * w1 * v1 ^ 2
    + (1772052480 : R) * hh * a3 * t0 ^ 7
    + (1438187520 : R) * hh * a3 * t0 ^ 5 * v1
    - (3027763200 : R) * hh * a3 * t0 ^ 4 * u1
    - (33305395200 : R) * hh * a3 * t0 ^ 3 * v1 ^ 2
    + (58133053440 : R) * hh * a3 * t0 ^ 2 * u1 * v1
    - (22900899840 : R) * hh * a3 * t0 * u1 ^ 2
    + (33910947840 : R) * hh * a3 * t0 * v1 ^ 3
    - (38755368960 : R) * hh * a3 * u1 * v1 ^ 2
    - (767033344 : R) * hh * b4 * t0 ^ 6
    + (4844421120 : R) * hh * b4 * t0 ^ 4 * v1
    - (5167382528 : R) * hh * b4 * t0 ^ 3 * u1
    - (7751073792 : R) * hh * b4 * t0 ^ 2 * v1 ^ 2
    + (11274289152 : R) * hh * b4 * t0 * u1 * v1
    - (3221225472 : R) * hh * b4 * u1 ^ 2
    + (1879048192 : R) * hh * b4 * v1 ^ 3
    - (5449973760 : R) * lam * a4 ^ 2 * t0 ^ 3
    + (8719958016 : R) * lam * a4 ^ 2 * t0 * v1
    - (3170893824 : R) * lam * a4 ^ 2 * u1
    + (2392270848 : R) * lam * a4 * t0 ^ 7
    - (14885240832 : R) * lam * a4 * t0 ^ 5 * v1
    + (12943687680 : R) * lam * a4 * t0 ^ 4 * u1
    + (25887375360 : R) * lam * a4 * t0 ^ 3 * v1 ^ 2
    - (32699842560 : R) * lam * a4 * t0 ^ 2 * u1 * v1
    + (8719958016 : R) * lam * a4 * t0 * u1 ^ 2
    - (10899947520 : R) * lam * a4 * t0 * v1 ^ 3
    + (8719958016 : R) * lam * a4 * u1 * v1 ^ 2
    - (199709874 : R) * lam * t0 ^ 11
    + (2253137040 : R) * lam * t0 ^ 9 * v1
    - (2317512384 : R) * lam * t0 ^ 8 * u1
    - (9270049536 : R) * lam * t0 ^ 7 * v1 ^ 2
    + (16745895936 : R) * lam * t0 ^ 6 * u1 * v1
    - (7442620416 : R) * lam * t0 ^ 5 * u1 ^ 2
    + (16745895936 : R) * lam * t0 ^ 5 * v1 ^ 3
    - (37213102080 : R) * lam * t0 ^ 4 * u1 * v1 ^ 2
    + (25887375360 : R) * lam * t0 ^ 3 * u1 ^ 2 * v1
    - (12404367360 : R) * lam * t0 ^ 3 * v1 ^ 4
    - (5449973760 : R) * lam * t0 ^ 2 * u1 ^ 3
    + (25887375360 : R) * lam * t0 ^ 2 * u1 * v1 ^ 3
    - (16349921280 : R) * lam * t0 * u1 ^ 2 * v1 ^ 2
    + (2588737536 : R) * lam * t0 * v1 ^ 5
    + (2906652672 : R) * lam * u1 ^ 3 * v1
    - (2724986880 : R) * lam * u1 * v1 ^ 4

/-- Left-branch residual of the order-`72` head after eliminating
`s₁`, `w₁`, `b₅`, and `a₄` against the second/third-defect reductions
and the `Gred`/`Vred` loads. -/
def bridgeMuLeftResidual810 (t0 v1 u1 b62 : R) : R :=
    - (2147483648 : R) * b62 ^ 3
    + (5431623680 : R) * b62 ^ 2 * t0 ^ 4
    - (19881000960 : R) * b62 ^ 2 * t0 ^ 2 * v1
    + (15099494400 : R) * b62 ^ 2 * t0 * u1
    + (10066329600 : R) * b62 ^ 2 * v1 ^ 2
    - (1519257600 : R) * b62 * t0 ^ 8
    + (13533184000 : R) * b62 * t0 ^ 6 * v1
    - (15987507200 : R) * b62 * t0 ^ 5 * u1
    - (38816972800 : R) * b62 * t0 ^ 4 * v1 ^ 2
    + (70726451200 : R) * b62 * t0 ^ 3 * u1 * v1
    - (31771852800 : R) * b62 * t0 ^ 2 * u1 ^ 2
    + (38063308800 : R) * b62 * t0 ^ 2 * v1 ^ 3
    - (59768832000 : R) * b62 * t0 * u1 * v1 ^ 2
    + (20132659200 : R) * b62 * u1 ^ 2 * v1
    - (7759462400 : R) * b62 * v1 ^ 4
    + (105356125 : R) * t0 ^ 12
    - (1508486000 : R) * t0 ^ 10 * v1
    + (2023952000 : R) * t0 ^ 9 * u1
    + (8275512000 : R) * t0 ^ 8 * v1 ^ 2
    - (19525632000 : R) * t0 ^ 7 * u1 * v1
    + (11915008000 : R) * t0 ^ 6 * u1 ^ 2
    - (21595392000 : R) * t0 ^ 6 * v1 ^ 3
    + (63285248000 : R) * t0 ^ 5 * u1 * v1 ^ 2
    - (62160896000 : R) * t0 ^ 4 * u1 ^ 2 * v1
    + (26840576000 : R) * t0 ^ 4 * v1 ^ 4
    + (20676608000 : R) * t0 ^ 3 * u1 ^ 3
    - (77168640000 : R) * t0 ^ 3 * u1 * v1 ^ 3
    + (75939840000 : R) * t0 ^ 2 * u1 ^ 2 * v1 ^ 2
    - (13590528000 : R) * t0 ^ 2 * v1 ^ 5
    - (28311552000 : R) * t0 * u1 ^ 3 * v1
    + (26804224000 : R) * t0 * u1 * v1 ^ 4
    + (2752512000 : R) * u1 ^ 4
    - (12320768000 : R) * u1 ^ 2 * v1 ^ 3
    + (1605632000 : R) * v1 ^ 6

end BridgeMuJet810

section BridgeMuJetFactor810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- On the seventeenth-face jet the cleared `μ` defect factors exactly
as `h⁷²` times its order-`72` head plus `h` times the tail. -/
theorem terminalClearedMuDefect810_jet_factored
    (h t0 v1 u1 s1 w1 b62 a4 a3 a2 a1 a0 b5 b4 b3 b2 b1 : k[X])
    (lambda : k) :
    terminalClearedMuDefect810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
        a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3
        b2 b1 lambda =
      h ^ 72 *
        (bridgeMuJetHead810 t0 v1 u1 s1 w1 b62 a4 b5 +
          h * bridgeMuJetTail810 h t0 v1 u1 s1 w1 b62 a4 a3 a2 a1 a0 b5
            b4 b3 b2 b1 (Polynomial.C lambda)) := by
  simp only [terminalClearedMuDefect810, bridgeMuJetHead810,
    bridgeMuJetTail810]
  ring

/-- Evaluation commutes with the order-`72` head. -/
theorem bridgeMuJetHead810_eval
    (t0 v1 u1 s1 w1 b62 a4 b5 : k[X]) (x : k) :
    (bridgeMuJetHead810 t0 v1 u1 s1 w1 b62 a4 b5).eval x =
      bridgeMuJetHead810 (t0.eval x) (v1.eval x) (u1.eval x)
        (s1.eval x) (w1.eval x) (b62.eval x) (a4.eval x) (b5.eval x) := by
  simp only [bridgeMuJetHead810, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]

end BridgeMuJetFactor810

/-! ## Scalar consequences of the vanishing order-`72` head -/

section BridgeMuScalars810

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the left ninth-face jet the vanishing order-`72` head reduces,
modulo the second/third-defect reductions and the `Gred`/`Vred` loads,
to an exact degree-`12` relation on `(t₀, v₁, u₁, b₆₂)` alone. -/
theorem bridgeMu_left_residual810
    (t0 v1 u1 s1 w1 b62 a4 b5 : F)
    (hhead : bridgeMuJetHead810 t0 v1 u1 s1 w1 b62 a4 b5 = 0)
    (hS : (32 : F) * s1 - (40 : F) * v1 = (5 : F) * t0 ^ 2)
    (hW : (128 : F) * w1 - (160 : F) * u1 - (40 : F) * t0 * v1 +
      (5 : F) * t0 ^ 3 = 0)
    (hV : (81920 : F) * a4 * t0 + (131072 : F) * b5 -
        (98304 : F) * b62 * t0 + (2912 : F) * t0 ^ 5 -
        (20480 : F) * t0 ^ 3 * v1 + (46080 : F) * t0 ^ 2 * u1 +
        (30720 : F) * t0 * v1 ^ 2 - (40960 : F) * u1 * v1 = 0)
    (hG : (2560 : F) * a4 - (2048 : F) * b62 + (35 : F) * t0 ^ 4 -
        (240 : F) * t0 ^ 2 * v1 + (640 : F) * t0 * u1 +
        (320 : F) * v1 ^ 2 = 0) :
    bridgeMuLeftResidual810 t0 v1 u1 b62 = 0 := by
  simp only [bridgeMuJetHead810] at hhead
  simp only [bridgeMuLeftResidual810]
  linear_combination (25 / 8 : F) * hhead
      - ((-1513881600 : F) * a4 ^ 2 * t0 ^ 2 + (1101004800 : F) * a4 ^ 2 * v1 + (861414400 : F) * a4 * t0 ^ 6 + (-4494336000 : F) * a4 * t0 ^ 4 * v1 + (3784704000 : F) * a4 * t0 ^ 3 * u1 + (5677056000 : F) * a4 * t0 ^ 2 * v1 ^ 2 + (-6055526400 : F) * a4 * t0 * u1 * v1 + (1101004800 : F) * a4 * u1 ^ 2 + (-1009254400 : F) * a4 * v1 ^ 3 + (-78233925 : F) * t0 ^ 10 + (804691800 : F) * t0 ^ 8 * v1 + (-830649600 : F) * t0 ^ 7 * u1 + (-2907273600 : F) * t0 ^ 6 * v1 ^ 2 + (5168486400 : F) * t0 ^ 5 * u1 * v1 + (-2247168000 : F) * t0 ^ 4 * u1 ^ 2 + (4307072000 : F) * t0 ^ 4 * v1 ^ 3 + (-8988672000 : F) * t0 ^ 3 * u1 * v1 ^ 2 + (5677056000 : F) * t0 ^ 2 * u1 ^ 2 * v1 + (-2247168000 : F) * t0 ^ 2 * v1 ^ 4 + (-1009254400 : F) * t0 * u1 ^ 3 + (3784704000 : F) * t0 * u1 * v1 ^ 3 + (-1513881600 : F) * u1 ^ 2 * v1 ^ 2 + (189235200 : F) * v1 ^ 5) * hS
      - ((240844800 : F) * a4 ^ 2 * t0 + (-196627200 : F) * a4 * t0 ^ 5 + (827904000 : F) * a4 * t0 ^ 3 * v1 + (-662323200 : F) * a4 * t0 ^ 2 * u1 + (-662323200 : F) * a4 * t0 * v1 ^ 2 + (481689600 : F) * a4 * u1 * v1 + (78233925 / 4 : F) * t0 ^ 9 + (-181704600 : F) * t0 ^ 7 * v1 + (188434400 : F) * t0 ^ 6 * u1 + (565303200 : F) * t0 ^ 5 * v1 ^ 2 + (-983136000 : F) * t0 ^ 4 * u1 * v1 + (413952000 : F) * t0 ^ 3 * u1 ^ 2 + (-655424000 : F) * t0 ^ 3 * v1 ^ 3 + (1241856000 : F) * t0 ^ 2 * u1 * v1 ^ 2 + (-662323200 : F) * t0 * u1 ^ 2 * v1 + (206976000 : F) * t0 * v1 ^ 4 + (80281600 : F) * u1 ^ 3 + (-220774400 : F) * u1 * v1 ^ 3) * hW
      - ((-154000 : F) * a4 * t0 ^ 3 + (336000 : F) * a4 * t0 * v1 + (-192000 : F) * a4 * u1 + (600875 / 32 : F) * t0 ^ 7 + (-548625 / 4 : F) * t0 ^ 5 * v1 + (144375 : F) * t0 ^ 4 * u1 + (288750 : F) * t0 ^ 3 * v1 ^ 2 + (-462000 : F) * t0 ^ 2 * u1 * v1 + (168000 : F) * t0 * u1 ^ 2 + (-154000 : F) * t0 * v1 ^ 3 + (168000 : F) * u1 * v1 ^ 2) * hV
      - ((5734400 : F) * a4 ^ 2 + (-1310720 : F) * a4 * b62 + (-425600 : F) * a4 * t0 ^ 4 + (7526400 : F) * a4 * t0 ^ 2 * v1 + (-8192000 : F) * a4 * t0 * u1 + (-7168000 : F) * a4 * v1 ^ 2 + (-1048576 : F) * b62 ^ 2 + (2634240 : F) * b62 * t0 ^ 4 + (-9584640 : F) * b62 * t0 ^ 2 * v1 + (7045120 : F) * b62 * t0 * u1 + (4751360 : F) * b62 * v1 ^ 2 + (-3050775 / 8 : F) * t0 ^ 8 + (2624300 : F) * t0 ^ 6 * v1 + (-3259200 : F) * t0 ^ 5 * u1 + (-4863600 : F) * t0 ^ 4 * v1 ^ 2 + (8537600 : F) * t0 ^ 3 * u1 * v1 + (-3635200 : F) * t0 ^ 2 * u1 ^ 2 + (1747200 : F) * t0 ^ 2 * v1 ^ 3 + (819200 : F) * t0 * u1 * v1 ^ 2 + (-3072000 : F) * u1 ^ 2 * v1 + (-89600 : F) * v1 ^ 4) * hG

set_option maxHeartbeats 4000000 in
/-- On the complementary right factor the vanishing order-`72` head
forces `v₁(a) = 0` and collapses the whole local jet. -/
theorem bridgeMu_comp_collapse810
    (t0 v1 u1 s1 w1 b62 a4 b5 : F)
    (hhead : bridgeMuJetHead810 t0 v1 u1 s1 w1 b62 a4 b5 = 0)
    (ht0 : t0 = 0)
    (hs : (4 : F) * s1 = (5 : F) * v1)
    (hw : (4 : F) * w1 = (5 : F) * u1)
    (hb5 : (16 : F) * b5 = (5 : F) * u1 * v1)
    (ha4 : (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0)
    (hcomp : (5 : F) * v1 ^ 2 - (8 : F) * b62 = 0)
    (hu : (2 : F) * u1 ^ 2 + v1 ^ 3 = 0) :
    v1 = 0 ∧ u1 = 0 ∧ b62 = 0 ∧ a4 = 0 := by
  subst ht0
  simp only [bridgeMuJetHead810] at hhead
  have h6 : (5767168000 : F) * v1 ^ 6 = 0 := by
    linear_combination (25 : F) * hhead
      - ((70464307200 : F) * a4 ^ 2 * v1 + (70464307200 : F) * a4 * u1 ^ 2 + (-64592281600 : F) * a4 * v1 ^ 3 + (-96888422400 : F) * u1 ^ 2 * v1 ^ 2 + (12111052800 : F) * v1 ^ 5) * hs
      - ((123312537600 : F) * a4 * u1 * v1 + (20552089600 : F) * u1 ^ 3 + (-56518246400 : F) * u1 * v1 ^ 3) * hw
      - ((-12582912000 : F) * a4 * u1 + (11010048000 : F) * u1 * v1 ^ 2) * hb5
      - ((2936012800 : F) * a4 ^ 2 + (-671088640 : F) * a4 * b62 + (-3670016000 : F) * a4 * v1 ^ 2 + (-536870912 : F) * b62 ^ 2 + (2432696320 : F) * b62 * v1 ^ 2 + (-1572864000 : F) * u1 ^ 2 * v1 + (-45875200 : F) * v1 ^ 4) * ha4
      - ((2147483648 : F) * b62 ^ 2 + (-8724152320 : F) * b62 * v1 ^ 2 + (-20132659200 : F) * u1 ^ 2 * v1 + (2306867200 : F) * v1 ^ 4) * hcomp
      - ((11010048000 : F) * u1 ^ 2 + (-4456448000 : F) * v1 ^ 3) * hu
  have hv1 : v1 = 0 := by
    have hpow : v1 ^ 6 = 0 :=
      (mul_eq_zero.mp h6).resolve_left (by norm_num)
    exact (pow_eq_zero_iff (by norm_num : (6 : ℕ) ≠ 0)).mp hpow
  subst hv1
  have hu1 : u1 = 0 := by
    have hpow : u1 ^ 2 = 0 := by linear_combination (1 / 2 : F) * hu
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow
  have hb62 : b62 = 0 := by linear_combination (-1 / 8 : F) * hcomp
  subst hb62
  refine ⟨rfl, hu1, rfl, ?_⟩
  linear_combination (1 / 40 : F) * ha4

set_option maxHeartbeats 4000000 in
/-- On the `u₁ = 0` sibling the vanishing order-`72` head forces
`v₁(a) = 0`, `b₆₂(a) = 0`, and `a₄(a) = 0` without any case split. -/
theorem bridgeMu_sibling_collapse810
    (t0 v1 u1 s1 w1 b62 a4 b5 : F)
    (hhead : bridgeMuJetHead810 t0 v1 u1 s1 w1 b62 a4 b5 = 0)
    (ht0 : t0 = 0) (hu1 : u1 = 0)
    (hs : (4 : F) * s1 = (5 : F) * v1)
    (hw : (4 : F) * w1 = (5 : F) * u1)
    (hb5 : (16 : F) * b5 = (5 : F) * u1 * v1)
    (ha4 : (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0)
    (hpi : (16 : F) * b62 * v1 + (10 : F) * u1 ^ 2 -
      (5 : F) * v1 ^ 3 = 0) :
    v1 = 0 ∧ b62 = 0 ∧ a4 = 0 := by
  subst ht0
  subst hu1
  simp only [bridgeMuJetHead810] at hhead
  have h9 : (786432000 : F) * v1 ^ 9 = 0 := by
    linear_combination (25 : F) * v1 ^ 3 * hhead
      - ((70464307200 : F) * a4 ^ 2 * v1 ^ 4 + (-64592281600 : F) * a4 * v1 ^ 6 + (12111052800 : F) * v1 ^ 8) * hs
      - ((2936012800 : F) * a4 ^ 2 * v1 ^ 3 + (-671088640 : F) * a4 * b62 * v1 ^ 3 + (-3670016000 : F) * a4 * v1 ^ 5 + (-536870912 : F) * b62 ^ 2 * v1 ^ 3 + (2432696320 : F) * b62 * v1 ^ 5 + (-45875200 : F) * v1 ^ 7) * ha4
      - ((-1073741824 : F) * b62 ^ 2 * v1 ^ 2 + (4697620480 : F) * b62 * v1 ^ 4 + (-2411724800 : F) * v1 ^ 6) * hpi
  have hv1 : v1 = 0 := by
    have hpow : v1 ^ 9 = 0 :=
      (mul_eq_zero.mp h9).resolve_left (by norm_num)
    exact (pow_eq_zero_iff (by norm_num : (9 : ℕ) ≠ 0)).mp hpow
  subst hv1
  have h3 : (17179869184 : F) * b62 ^ 3 = 0 := by
    linear_combination (-25 : F) * hhead + ((2936012800 : F) * a4 ^ 2 + (-671088640 : F) * a4 * b62 + (-536870912 : F) * b62 ^ 2) * ha4
  have hb62 : b62 = 0 := by
    have hpow : b62 ^ 3 = 0 :=
      (mul_eq_zero.mp h3).resolve_left (by norm_num)
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hpow
  subst hb62
  refine ⟨rfl, rfl, ?_⟩
  linear_combination (1 / 40 : F) * ha4

end BridgeMuScalars810

section NonzeroTerminalIntegralBridge810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local terminal integral bridge: the seventeenth final-row
packet together with the literal-source `h`-adic clearing of the
degree-`5` first integral `μ` — the lowest of the uncleared
degree-`5` through degree-`1` integrals that admits an exact
construction — and its jet-peeled consequences.  The cleared defect is
`C eta * h₀⁸⁴` for a ground constant `eta` (not claimed zero), the
seventeenth-face jet factors it through `h₀⁷²`, so the order-`72` head
vanishes at the root on every branch.  On the left the head reduces to
an exact degree-`12` relation on `(t₀, v₁, u₁, b₆₂)`; on the whole
right branch it collapses the local jet:
`v₁(a) = u₁(a) = b₆₂(a) = p₄(a) = s₁(a) = w₁(a) = q₅(a) = 0` with the
divisibility upgrades `h₀⁵ ∣ p₆`, `h₀³ ∣ p₅`, `h₀⁷ ∣ q₈`, `h₀⁵ ∣ q₇`,
`h₀³ ∣ q₆`, `h₀ ∣ p₄`, `h₀ ∣ q₅`.  Neither branch is closed. -/
theorem nonzeroFace810_linearRoot_terminalIntegralBridge
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
    ∃ t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : k[X],
      ∃ eta : k,
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
        terminalClearedMuDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
            (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C eta * h0 ^ 84 ∧
        bridgeMuJetHead810 t0 v1 u1 s1 w1 b62 (p.coeff 4) (q.coeff 5) +
            h0 * bridgeMuJetTail810 h0 t0 v1 u1 s1 w1 b62 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C eta * h0 ^ 12 ∧
        bridgeMuJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
            (s1.eval a) (w1.eval a) (b62.eval a) ((p.coeff 4).eval a)
            ((q.coeff 5).eval a) = 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Wred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Xred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7 ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : k[X]),
              (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                    (5 : k[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : k[X]) * w1 - (160 : k[X]) * u1 -
                    (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : k) * lambda * t0.eval a = 0 ∧
                (4 : k) * tau1.eval a +
                    (9 : k) * lambda * (t0.eval a) ^ 2 +
                  (144 : k) * lambda * v1.eval a = 0) ∧
            (∃ g1 : k[X],
              (2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
                    (35 : k[X]) * t0 ^ 4 -
                    (240 : k[X]) * t0 ^ 2 * v1 +
                    (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : k) * g1.eval a +
                    (3 : k) * lambda *
                      ((7 : k) * (t0.eval a) ^ 3 -
                        (48 : k) * t0.eval a * v1.eval a -
                        (384 : k) * u1.eval a) = 0) ∧
            (∃ k1 : k[X],
              (81920 : k[X]) * (p.coeff 4) * t0 +
                    (131072 : k[X]) * (q.coeff 5) -
                    (98304 : k[X]) * b62 * t0 +
                    (2912 : k[X]) * t0 ^ 5 -
                    (20480 : k[X]) * t0 ^ 3 * v1 +
                    (46080 : k[X]) * t0 ^ 2 * u1 +
                    (30720 : k[X]) * t0 * v1 ^ 2 -
                    (40960 : k[X]) * u1 * v1 =
                  h0 * k1 ∧
                k1.eval a + (9 : k) * lambda *
                    ((4096 : k) * (p.coeff 4).eval a +
                      (91 : k) * (t0.eval a) ^ 4 -
                      (608 : k) * (t0.eval a) ^ 2 * v1.eval a -
                      (2560 : k) * t0.eval a * u1.eval a +
                      (256 : k) * (v1.eval a) ^ 2) = 0) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                  (u1.eval a) →
              (128 : k) * w1.eval a -
                    (5 : k) * t0.eval a *
                      ((24 : k) * v1.eval a -
                        (5 : k) * (t0.eval a) ^ 2) =
                  0 ∧
                (1024 : k) * (q.coeff 5).eval a -
                    (256 : k) * b62.eval a * t0.eval a -
                    (11 : k) * (t0.eval a) ^ 5 +
                  (40 : k) * (t0.eval a) ^ 3 * v1.eval a =
                  0 ∧
                ((3 : k) * (t0.eval a) ^ 2 - (8 : k) * v1.eval a) *
                    ((1024 : k) * b62.eval a +
                      (25 : k) * (t0.eval a) ^ 4 -
                      (320 : k) * (v1.eval a) ^ 2) =
                  0 ∧
                (4177920 : k) * (p.coeff 4).eval a *
                        (t0.eval a) ^ 3 -
                      (11796480 : k) * (p.coeff 4).eval a *
                        t0.eval a * v1.eval a +
                      (10485760 : k) * (p.coeff 4).eval a *
                        u1.eval a +
                      (7208960 : k) * (q.coeff 5).eval a *
                        (t0.eval a) ^ 2 -
                      (10485760 : k) * (q.coeff 5).eval a *
                        v1.eval a -
                      (6848512 : k) * b62.eval a *
                        (t0.eval a) ^ 3 +
                      (17301504 : k) * b62.eval a * t0.eval a *
                        v1.eval a -
                      (12582912 : k) * b62.eval a * u1.eval a +
                      (300960 : k) * (t0.eval a) ^ 7 -
                      (2675200 : k) * (t0.eval a) ^ 5 * v1.eval a +
                      (4561920 : k) * (t0.eval a) ^ 4 * u1.eval a +
                      (7096320 : k) * (t0.eval a) ^ 3 *
                        (v1.eval a) ^ 2 -
                      (15769600 : k) * (t0.eval a) ^ 2 *
                        u1.eval a * v1.eval a +
                      (7208960 : k) * t0.eval a *
                        (u1.eval a) ^ 2 -
                      (5406720 : k) * t0.eval a *
                        (v1.eval a) ^ 3 +
                      (7208960 : k) * u1.eval a *
                        (v1.eval a) ^ 2 +
                    (384 : k) * t0.eval a *
                      ((3 : k) * (t0.eval a) ^ 2 -
                        (8 : k) * v1.eval a) *
                      ((1024 : k) * b62.eval a +
                        (25 : k) * (t0.eval a) ^ 4 -
                        (320 : k) * (v1.eval a) ^ 2) =
                  0) ∧
            bridgeMuLeftResidual810 (t0.eval a) (v1.eval a)
              (u1.eval a) (b62.eval a) = 0) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            (40 : k) * (p.coeff 4).eval a - (32 : k) * b62.eval a +
              (5 : k) * (v1.eval a) ^ 2 = 0 ∧
            (16 : k) * (q.coeff 5).eval a =
              (5 : k) * u1.eval a * v1.eval a ∧
            (16 : k) * b62.eval a * v1.eval a +
                (10 : k) * (u1.eval a) ^ 2 -
              (5 : k) * (v1.eval a) ^ 3 = 0 ∧
            u1.eval a *
                ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a) =
              0 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8 ∧
            v1.eval a = 0 ∧ u1.eval a = 0 ∧ b62.eval a = 0 ∧
            (p.coeff 4).eval a = 0 ∧ s1.eval a = 0 ∧
            w1.eval a = 0 ∧ (q.coeff 5).eval a = 0 ∧
            h0 ^ 5 ∣ p.coeff 6 ∧ h0 ^ 3 ∣ p.coeff 5 ∧
            h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
            h0 ^ 3 ∣ q.coeff 6 ∧ h0 ∣ p.coeff 4 ∧
            h0 ∣ q.coeff 5 ∧
            ((u1.eval a = 0 ∧
                ∃ (t1 u2 w2 b51 sigma rho pi : k[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    (32 : k[X]) * s1 - (40 : k[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (40 : k[X]) * (p.coeff 4) - (32 : k[X]) * b62 +
                        (5 : k[X]) * v1 ^ 2 =
                      h0 ^ 2 * rho ∧
                    (16 : k[X]) * b62 * v1 -
                        (5 : k[X]) * v1 ^ 3 =
                      h0 ^ 2 * pi ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧ h0 ^ 2 ∣
                      ((32 : k[X]) * s1 - (40 : k[X]) * v1) ∧
                    h0 ^ 2 ∣
                      ((40 : k[X]) * (p.coeff 4) -
                          (32 : k[X]) * b62 +
                        (5 : k[X]) * v1 ^ 2) ∧
                    h0 ^ 2 ∣
                      ((16 : k[X]) * b62 * v1 -
                        (5 : k[X]) * v1 ^ 3) ∧
                    (32 : k) * w2.eval a - (40 : k) * u2.eval a -
                        (10 : k) * t1.eval a * v1.eval a +
                      (9 : k) * lambda * v1.eval a = 0 ∧
                    (2560 : k) * b51.eval a +
                        (576 : k) * lambda * b62.eval a -
                        (640 : k) * t1.eval a * b62.eval a -
                        (45 : k) * lambda * (v1.eval a) ^ 2 +
                        (400 : k) * t1.eval a * (v1.eval a) ^ 2 -
                        (800 : k) * u2.eval a * v1.eval a = 0 ∧
                    (v1.eval a) ^ 3 *
                        ((3 : k) * lambda * v1.eval a +
                          (160 : k) * t1.eval a * v1.eval a -
                          (320 : k) * u2.eval a) =
                      0 ∧
                    (8 : k) * rho.eval a +
                        (8 : k) * sigma.eval a * v1.eval a +
                        (63 : k) * lambda * t1.eval a * v1.eval a -
                        (72 : k) * lambda * u2.eval a -
                        (70 : k) * (t1.eval a) ^ 2 * v1.eval a +
                      (80 : k) * t1.eval a * u2.eval a = 0 ∧
                    ∃ kz : k[X],
                      (81920 : k[X]) * (p.coeff 4) * t1 +
                            (131072 : k[X]) * b51 -
                            (98304 : k[X]) * b62 * t1 +
                            (212992 : k[X]) * s1 * t1 * v1 -
                            (131072 : k[X]) * s1 * u2 -
                            (199680 : k[X]) * t1 * v1 ^ 2 +
                            (266240 : k[X]) * u2 * v1 -
                            (114688 : k[X]) * v1 * w2 +
                            (36864 : k[X]) * Polynomial.C lambda *
                              (p.coeff 4) -
                            (29952 : k[X]) * Polynomial.C lambda *
                              v1 ^ 2 =
                          h0 * kz ∧
                        kz.eval a =
                          (163840 : k) * (p.coeff 3).eval a) ∨
              ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a = 0 ∧
                (8 : k) * (p.coeff 4).eval a -
                    (3 : k) * (v1.eval a) ^ 2 = 0 ∧
                (2 : k) * (u1.eval a) ^ 2 + (v1.eval a) ^ 3 = 0 ∧
                ∃ (t1 omega sigma beta : k[X]),
                  t0 = h0 * t1 ∧
                    (4 : k[X]) * w1 - (5 : k[X]) * u1 =
                      h0 * omega ∧
                    (32 : k[X]) * s1 - (40 : k[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (16 : k[X]) * (q.coeff 5) -
                        (5 : k[X]) * u1 * v1 =
                      h0 * beta ∧
                    h0 ^ 2 ∣ ((32 : k[X]) * s1 - (40 : k[X]) * v1) ∧
                    h0 ∣
                      ((16 : k[X]) * (q.coeff 5) -
                        (5 : k[X]) * u1 * v1) ∧
                    (8 : k) * omega.eval a -
                        (10 : k) * t1.eval a * v1.eval a +
                      (9 : k) * lambda * v1.eval a = 0 ∧
                    (32 : k) * beta.eval a +
                      (63 : k) * lambda * (v1.eval a) ^ 2 =
                      0 ∧
                    ∃ rhoc : k[X],
                      (40 : k[X]) * (p.coeff 4) -
                            (32 : k[X]) * b62 +
                          (5 : k[X]) * v1 ^ 2 =
                        h0 * rhoc ∧
                      rhoc.eval a +
                          (10 : k) * t1.eval a * u1.eval a -
                        (9 : k) * lambda * u1.eval a = 0)))) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
    hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6d, hrow, hroweval, hsplit⟩ :=
    nonzeroFace810_linearRoot_seventeenthFinalRow p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  obtain ⟨eta, hpow⟩ :=
    nonzeroFace810_terminalMuPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  have hp6 : p.coeff 6 = h0 ^ 4 * v1 := by rw [hv0, hv1]; ring
  have hp5 : p.coeff 5 = h0 ^ 2 * u1 := by rw [hu0, hu1]; ring
  have hq8 : q.coeff 8 = h0 ^ 6 * s1 := by rw [hs0, hs1]; ring
  have hq7 : q.coeff 7 = h0 ^ 4 * w1 := by rw [hw0, hw1]; ring
  have hpowJet :
      terminalClearedMuDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 4 * v1)
          (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (h0 ^ 6 * s1) (h0 ^ 4 * w1) (h0 ^ 2 * b62)
          (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          lambda =
        Polynomial.C eta * h0 ^ 84 := by
    rw [← ht0, ← hp6, ← hp5, ← hq8, ← hq7, ← hb62]
    exact hpow
  have hpeel :
      bridgeMuJetHead810 t0 v1 u1 s1 w1 b62 (p.coeff 4) (q.coeff 5) +
          h0 * bridgeMuJetTail810 h0 t0 v1 u1 s1 w1 b62 (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda) =
        Polynomial.C eta * h0 ^ 12 := by
    have h72 : (h0 : k[X]) ^ 72 ≠ 0 := pow_ne_zero 72 hh0
    apply mul_left_cancel₀ h72
    rw [← terminalClearedMuDefect810_jet_factored h0 t0 v1 u1 s1 w1 b62
      (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
      (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
      lambda]
    rw [hpowJet]
    ring
  have hheadeval :
      bridgeMuJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
          (s1.eval a) (w1.eval a) (b62.eval a) ((p.coeff 4).eval a)
          ((q.coeff 5).eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hpeel
    have h12 : (0 : k) ^ 12 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeMuJetHead810_eval, h12, mul_zero, zero_mul, add_zero] at hev
    exact hev
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, eta, ht0, hv0, hu0,
    hs0, hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6d, hpow, hpeel,
    hheadeval, hrow, hroweval, ?_⟩
  rcases hsplit with hleft | hright
  · obtain ⟨hv0z, hs0z, hq6z, hu0z, hw0z, hSl, hWl, hGred, hVred,
      hWred, hXred, hd1, hd2, hd3, hd4, hF12, hm1tau1, hg1c, hk1c,
      hcond⟩ := hleft
    refine Or.inl ⟨hv0z, hs0z, hq6z, hu0z, hw0z, hSl, hWl, hGred,
      hVred, hWred, hXred, hd1, hd2, hd3, hd4, hF12, hm1tau1, hg1c,
      hk1c, hcond, ?_⟩
    exact bridgeMu_left_residual810 (t0.eval a) (v1.eval a)
      (u1.eval a) (s1.eval a) (w1.eval a) (b62.eval a)
      ((p.coeff 4).eval a) ((q.coeff 5).eval a) hheadeval hSl hWl
      hVred hGred
  · obtain ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hq6z, hsr, hwr, ha4r, hb5r,
      hpir, hualt, hd1, hd2, hd3, hd4, hd5, hsub⟩ := hright
    have hcol : v1.eval a = 0 ∧ u1.eval a = 0 ∧ b62.eval a = 0 ∧
        (p.coeff 4).eval a = 0 := by
      rcases hsub with hsib | hcomp
      · obtain ⟨hv1z, hb62z, ha4z⟩ :=
          bridgeMu_sibling_collapse810 (t0.eval a) (v1.eval a)
            (u1.eval a) (s1.eval a) (w1.eval a) (b62.eval a)
            ((p.coeff 4).eval a) ((q.coeff 5).eval a) hheadeval ht0z
            hsib.1 hsr hwr hb5r ha4r hpir
        exact ⟨hv1z, hsib.1, hb62z, ha4z⟩
      · obtain ⟨hv1z, hu1z, hb62z, ha4z⟩ :=
          bridgeMu_comp_collapse810 (t0.eval a) (v1.eval a)
            (u1.eval a) (s1.eval a) (w1.eval a) (b62.eval a)
            ((p.coeff 4).eval a) ((q.coeff 5).eval a) hheadeval ht0z
            hsr hwr hb5r ha4r hcomp.1 hcomp.2.2.1
        exact ⟨hv1z, hu1z, hb62z, ha4z⟩
    obtain ⟨hv1z, hu1z, hb62z, ha4z⟩ := hcol
    have hs1z : s1.eval a = 0 := by
      have h4 : (4 : k) ≠ 0 := by norm_num
      have hzero : (4 : k) * s1.eval a = 0 := by
        rw [hsr, hv1z, mul_zero]
      exact (mul_eq_zero.mp hzero).resolve_left h4
    have hw1z : w1.eval a = 0 := by
      have h4 : (4 : k) ≠ 0 := by norm_num
      have hzero : (4 : k) * w1.eval a = 0 := by
        rw [hwr, hu1z, mul_zero]
      exact (mul_eq_zero.mp hzero).resolve_left h4
    have hb5z : (q.coeff 5).eval a = 0 := by
      have h16 : (16 : k) ≠ 0 := by norm_num
      have hzero : (16 : k) * (q.coeff 5).eval a = 0 := by
        rw [hb5r, hu1z]
        ring
      exact (mul_eq_zero.mp hzero).resolve_left h16
    obtain ⟨v2, hv2⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 v1 a hh0degree hroot
        hv1z
    obtain ⟨u2, hu2⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 u1 a hh0degree hroot
        hu1z
    obtain ⟨s2, hs2⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 s1 a hh0degree hroot
        hs1z
    obtain ⟨w2, hw2⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 w1 a hh0degree hroot
        hw1z
    obtain ⟨b63, hb63⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 b62 a hh0degree hroot
        hb62z
    have hdp6 : h0 ^ 5 ∣ p.coeff 6 := ⟨v2, by rw [hp6, hv2]; ring⟩
    have hdp5 : h0 ^ 3 ∣ p.coeff 5 := ⟨u2, by rw [hp5, hu2]; ring⟩
    have hdq8 : h0 ^ 7 ∣ q.coeff 8 := ⟨s2, by rw [hq8, hs2]; ring⟩
    have hdq7 : h0 ^ 5 ∣ q.coeff 7 := ⟨w2, by rw [hq7, hw2]; ring⟩
    have hdq6 : h0 ^ 3 ∣ q.coeff 6 := ⟨b63, by rw [hb62, hb63]; ring⟩
    have hdp4 : h0 ∣ p.coeff 4 :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 4) a
        hh0degree hroot ha4z
    have hdq5 : h0 ∣ q.coeff 5 :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 5) a
        hh0degree hroot hb5z
    exact Or.inr ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hq6z, hsr, hwr, ha4r,
      hb5r, hpir, hualt, hd1, hd2, hd3, hd4, hd5, hv1z, hu1z, hb62z,
      ha4z, hs1z, hw1z, hb5z, hdp6, hdp5, hdq8, hdq7, hdq6, hdp4,
      hdq5, hsub⟩

set_option maxHeartbeats 40000000 in
/-- Source-facing terminal integral bridge of a normalized scale-two
`(8,10)` nonzero face: the seventeenth final-row packet — including
the Keller boundary relation `G'(a) W(a) - F(a) X'(a) = j ≠ 0` — 
combined with the cleared degree-`5` first integral `μ` and its
jet-peeled order-`72` head.  The `μ` ground constant `eta` is
retained, the left branch carries the new degree-`12` residual, and
the right branch collapses to the zero local jet.  No branch is
closed and the aligned face `N = 0` stays open. -/
theorem normalized810ScaleTwo_nonzeroFace_terminalIntegralBridge
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK : K)
      (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : K[X])
      (eta : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        jK ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C jK ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = jK ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a ∧
        terminalClearedMuDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
            (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C eta * h0 ^ 84 ∧
        bridgeMuJetHead810 t0 v1 u1 s1 w1 b62 (p.coeff 4) (q.coeff 5) +
            h0 * bridgeMuJetTail810 h0 t0 v1 u1 s1 w1 b62 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C eta * h0 ^ 12 ∧
        bridgeMuJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
            (s1.eval a) (w1.eval a) (b62.eval a) ((p.coeff 4).eval a)
            ((q.coeff 5).eval a) = 0 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : K) * s1.eval a - (40 : K) * v1.eval a =
              (5 : K) * (t0.eval a) ^ 2 ∧
            (128 : K) * w1.eval a - (160 : K) * u1.eval a -
                (40 : K) * t0.eval a * v1.eval a +
              (5 : K) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Wred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Xred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7 ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : K[X]),
              (32 : K[X]) * s1 - (40 : K[X]) * v1 -
                    (5 : K[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : K[X]) * w1 - (160 : K[X]) * u1 -
                    (40 : K[X]) * t0 * v1 + (5 : K[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : K) * lambda * t0.eval a = 0 ∧
                (4 : K) * tau1.eval a +
                    (9 : K) * lambda * (t0.eval a) ^ 2 +
                  (144 : K) * lambda * v1.eval a = 0) ∧
            (∃ g1 : K[X],
              (2560 : K[X]) * (p.coeff 4) - (2048 : K[X]) * b62 +
                    (35 : K[X]) * t0 ^ 4 -
                    (240 : K[X]) * t0 ^ 2 * v1 +
                    (640 : K[X]) * t0 * u1 + (320 : K[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : K) * g1.eval a +
                    (3 : K) * lambda *
                      ((7 : K) * (t0.eval a) ^ 3 -
                        (48 : K) * t0.eval a * v1.eval a -
                        (384 : K) * u1.eval a) = 0) ∧
            (∃ k1 : K[X],
              (81920 : K[X]) * (p.coeff 4) * t0 +
                    (131072 : K[X]) * (q.coeff 5) -
                    (98304 : K[X]) * b62 * t0 +
                    (2912 : K[X]) * t0 ^ 5 -
                    (20480 : K[X]) * t0 ^ 3 * v1 +
                    (46080 : K[X]) * t0 ^ 2 * u1 +
                    (30720 : K[X]) * t0 * v1 ^ 2 -
                    (40960 : K[X]) * u1 * v1 =
                  h0 * k1 ∧
                k1.eval a + (9 : K) * lambda *
                    ((4096 : K) * (p.coeff 4).eval a +
                      (91 : K) * (t0.eval a) ^ 4 -
                      (608 : K) * (t0.eval a) ^ 2 * v1.eval a -
                      (2560 : K) * t0.eval a * u1.eval a +
                      (256 : K) * (v1.eval a) ^ 2) = 0) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                  (u1.eval a) →
              (128 : K) * w1.eval a -
                    (5 : K) * t0.eval a *
                      ((24 : K) * v1.eval a -
                        (5 : K) * (t0.eval a) ^ 2) =
                  0 ∧
                (1024 : K) * (q.coeff 5).eval a -
                    (256 : K) * b62.eval a * t0.eval a -
                    (11 : K) * (t0.eval a) ^ 5 +
                  (40 : K) * (t0.eval a) ^ 3 * v1.eval a =
                  0 ∧
                ((3 : K) * (t0.eval a) ^ 2 - (8 : K) * v1.eval a) *
                    ((1024 : K) * b62.eval a +
                      (25 : K) * (t0.eval a) ^ 4 -
                      (320 : K) * (v1.eval a) ^ 2) =
                  0 ∧
                (4177920 : K) * (p.coeff 4).eval a *
                        (t0.eval a) ^ 3 -
                      (11796480 : K) * (p.coeff 4).eval a *
                        t0.eval a * v1.eval a +
                      (10485760 : K) * (p.coeff 4).eval a *
                        u1.eval a +
                      (7208960 : K) * (q.coeff 5).eval a *
                        (t0.eval a) ^ 2 -
                      (10485760 : K) * (q.coeff 5).eval a *
                        v1.eval a -
                      (6848512 : K) * b62.eval a *
                        (t0.eval a) ^ 3 +
                      (17301504 : K) * b62.eval a * t0.eval a *
                        v1.eval a -
                      (12582912 : K) * b62.eval a * u1.eval a +
                      (300960 : K) * (t0.eval a) ^ 7 -
                      (2675200 : K) * (t0.eval a) ^ 5 * v1.eval a +
                      (4561920 : K) * (t0.eval a) ^ 4 * u1.eval a +
                      (7096320 : K) * (t0.eval a) ^ 3 *
                        (v1.eval a) ^ 2 -
                      (15769600 : K) * (t0.eval a) ^ 2 *
                        u1.eval a * v1.eval a +
                      (7208960 : K) * t0.eval a *
                        (u1.eval a) ^ 2 -
                      (5406720 : K) * t0.eval a *
                        (v1.eval a) ^ 3 +
                      (7208960 : K) * u1.eval a *
                        (v1.eval a) ^ 2 +
                    (384 : K) * t0.eval a *
                      ((3 : K) * (t0.eval a) ^ 2 -
                        (8 : K) * v1.eval a) *
                      ((1024 : K) * b62.eval a +
                        (25 : K) * (t0.eval a) ^ 4 -
                        (320 : K) * (v1.eval a) ^ 2) =
                  0) ∧
            bridgeMuLeftResidual810 (t0.eval a) (v1.eval a)
              (u1.eval a) (b62.eval a) = 0) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : K) * s1.eval a = (5 : K) * v1.eval a ∧
            (4 : K) * w1.eval a = (5 : K) * u1.eval a ∧
            (40 : K) * (p.coeff 4).eval a - (32 : K) * b62.eval a +
              (5 : K) * (v1.eval a) ^ 2 = 0 ∧
            (16 : K) * (q.coeff 5).eval a =
              (5 : K) * u1.eval a * v1.eval a ∧
            (16 : K) * b62.eval a * v1.eval a +
                (10 : K) * (u1.eval a) ^ 2 -
              (5 : K) * (v1.eval a) ^ 3 = 0 ∧
            u1.eval a *
                ((5 : K) * (v1.eval a) ^ 2 - (8 : K) * b62.eval a) =
              0 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8 ∧
            v1.eval a = 0 ∧ u1.eval a = 0 ∧ b62.eval a = 0 ∧
            (p.coeff 4).eval a = 0 ∧ s1.eval a = 0 ∧
            w1.eval a = 0 ∧ (q.coeff 5).eval a = 0 ∧
            h0 ^ 5 ∣ p.coeff 6 ∧ h0 ^ 3 ∣ p.coeff 5 ∧
            h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
            h0 ^ 3 ∣ q.coeff 6 ∧ h0 ∣ p.coeff 4 ∧
            h0 ∣ q.coeff 5 ∧
            ((u1.eval a = 0 ∧
                ∃ (t1 u2 w2 b51 sigma rho pi : K[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    (32 : K[X]) * s1 - (40 : K[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (40 : K[X]) * (p.coeff 4) - (32 : K[X]) * b62 +
                        (5 : K[X]) * v1 ^ 2 =
                      h0 ^ 2 * rho ∧
                    (16 : K[X]) * b62 * v1 -
                        (5 : K[X]) * v1 ^ 3 =
                      h0 ^ 2 * pi ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧ h0 ^ 2 ∣
                      ((32 : K[X]) * s1 - (40 : K[X]) * v1) ∧
                    h0 ^ 2 ∣
                      ((40 : K[X]) * (p.coeff 4) -
                          (32 : K[X]) * b62 +
                        (5 : K[X]) * v1 ^ 2) ∧
                    h0 ^ 2 ∣
                      ((16 : K[X]) * b62 * v1 -
                        (5 : K[X]) * v1 ^ 3) ∧
                    (32 : K) * w2.eval a - (40 : K) * u2.eval a -
                        (10 : K) * t1.eval a * v1.eval a +
                      (9 : K) * lambda * v1.eval a = 0 ∧
                    (2560 : K) * b51.eval a +
                        (576 : K) * lambda * b62.eval a -
                        (640 : K) * t1.eval a * b62.eval a -
                        (45 : K) * lambda * (v1.eval a) ^ 2 +
                        (400 : K) * t1.eval a * (v1.eval a) ^ 2 -
                        (800 : K) * u2.eval a * v1.eval a = 0 ∧
                    (v1.eval a) ^ 3 *
                        ((3 : K) * lambda * v1.eval a +
                          (160 : K) * t1.eval a * v1.eval a -
                          (320 : K) * u2.eval a) =
                      0 ∧
                    (8 : K) * rho.eval a +
                        (8 : K) * sigma.eval a * v1.eval a +
                        (63 : K) * lambda * t1.eval a * v1.eval a -
                        (72 : K) * lambda * u2.eval a -
                        (70 : K) * (t1.eval a) ^ 2 * v1.eval a +
                      (80 : K) * t1.eval a * u2.eval a = 0 ∧
                    ∃ kz : K[X],
                      (81920 : K[X]) * (p.coeff 4) * t1 +
                            (131072 : K[X]) * b51 -
                            (98304 : K[X]) * b62 * t1 +
                            (212992 : K[X]) * s1 * t1 * v1 -
                            (131072 : K[X]) * s1 * u2 -
                            (199680 : K[X]) * t1 * v1 ^ 2 +
                            (266240 : K[X]) * u2 * v1 -
                            (114688 : K[X]) * v1 * w2 +
                            (36864 : K[X]) * Polynomial.C lambda *
                              (p.coeff 4) -
                            (29952 : K[X]) * Polynomial.C lambda *
                              v1 ^ 2 =
                          h0 * kz ∧
                        kz.eval a =
                          (163840 : K) * (p.coeff 3).eval a) ∨
              ((5 : K) * (v1.eval a) ^ 2 - (8 : K) * b62.eval a = 0 ∧
                (8 : K) * (p.coeff 4).eval a -
                    (3 : K) * (v1.eval a) ^ 2 = 0 ∧
                (2 : K) * (u1.eval a) ^ 2 +
                  (v1.eval a) ^ 3 = 0 ∧
                ∃ (t1 omega sigma beta : K[X]),
                  t0 = h0 * t1 ∧
                    (4 : K[X]) * w1 - (5 : K[X]) * u1 =
                      h0 * omega ∧
                    (32 : K[X]) * s1 - (40 : K[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (16 : K[X]) * (q.coeff 5) -
                        (5 : K[X]) * u1 * v1 =
                      h0 * beta ∧
                    h0 ^ 2 ∣ ((32 : K[X]) * s1 - (40 : K[X]) * v1) ∧
                    h0 ∣
                      ((16 : K[X]) * (q.coeff 5) -
                        (5 : K[X]) * u1 * v1) ∧
                    (8 : K) * omega.eval a -
                        (10 : K) * t1.eval a * v1.eval a +
                      (9 : K) * lambda * v1.eval a = 0 ∧
                    (32 : K) * beta.eval a +
                      (63 : K) * lambda * (v1.eval a) ^ 2 =
                      0 ∧
                    ∃ rhoc : K[X],
                      (40 : K[X]) * (p.coeff 4) -
                            (32 : K[X]) * b62 +
                          (5 : K[X]) * v1 ^ 2 =
                        h0 * rhoc ∧
                      rhoc.eval a +
                          (10 : K) * t1.eval a * u1.eval a -
                        (9 : K) * lambda * u1.eval a = 0)))) := by
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
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨t0', v0', u0', s0', w0', v1', s1', u1', w1', b62', eta',
    ht0', hv0', hu0', hs0', hw0', hv1', hs1', hu1', hw1', hb62', hq9',
    hq6', hpow', hpeel', hheadeval', hrow', hroweval', hsplit'⟩ :=
    nonzeroFace810_linearRoot_terminalIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval', heq, sub_self]
  exact ⟨h0, lambda, a, j, t0', v0', u0', s0', w0', v1', s1', u1',
    w1', b62', eta', hh0, hlambda, hh0degree, hH, hroot, ht0', hv0',
    hu0', hs0', hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6', hN',
    hj, hrow', hroweval', hsep, hpow', hpeel', hheadeval', hsplit'⟩

end NonzeroTerminalIntegralBridge810

#print axioms terminalMuResidual810_deriv_zero
#print axioms nonzeroFace810_terminalMuPowerRelation
#print axioms terminalClearedMuDefect810_jet_factored
#print axioms bridgeMu_left_residual810
#print axioms bridgeMu_comp_collapse810
#print axioms bridgeMu_sibling_collapse810
#print axioms nonzeroFace810_linearRoot_terminalIntegralBridge
#print axioms normalized810ScaleTwo_nonzeroFace_terminalIntegralBridge

end Max11DegreeRoutes
