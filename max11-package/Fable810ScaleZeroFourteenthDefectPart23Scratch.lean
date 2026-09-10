import Fable810ScaleZeroFourteenthDefectPart22Scratch

/-! Part 23 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section DepressedRow810Fifteenth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]


/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`2` Jacobian coefficient is
exactly `3 U G' + 2 V F' + W E'
- F V' - 2 E W' - 3 D X'`. -/
theorem differentialJacobian_coeff_2_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 2 =
      (3 : F) * g.coeff 3 * d (f.coeff 0) +
        (2 : F) * g.coeff 2 * d (f.coeff 1) +
        g.coeff 1 * d (f.coeff 2) -
          f.coeff 1 * d (g.coeff 2) -
          (2 : F) * f.coeff 2 * d (g.coeff 1) -
          (3 : F) * f.coeff 3 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal (2 : ℕ) :
      Finset (ℕ × ℕ)) =
      ({(0, 2), (1, 1),
        (2, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne02_11 : ((0, 2) : ℕ × ℕ) ≠ (1, 1) := by decide
  have hne02_20 : ((0, 2) : ℕ × ℕ) ≠ (2, 0) := by decide
  have hne11_20 : ((1, 1) : ℕ × ℕ) ≠ (2, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 2 =
        (3 : F) * g.coeff 3 * d (f.coeff 0) +
          (2 : F) * g.coeff 2 * d (f.coeff 1) +
          g.coeff 1 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne02_11, hne02_20]),
        Finset.sum_insert (by simp [hne11_20]),
        Finset.sum_singleton]
      ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0 : g.derivative.coeff 0 = g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder2, hder1, hder0]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 2 =
        f.coeff 1 * d (g.coeff 2) +
          (2 : F) * f.coeff 2 * d (g.coeff 1) +
          (3 : F) * f.coeff 3 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne02_11, hne02_20]),
        Finset.sum_insert (by simp [hne11_20]),
        Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder2]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring


end DepressedRow810Fifteenth
end Max11DegreeRoutes
end
