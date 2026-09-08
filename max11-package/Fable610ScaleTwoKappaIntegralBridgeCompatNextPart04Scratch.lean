import Fable610ScaleTwoKappaIntegralBridgeCompatScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaDepressedRow610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic, the degree-`3`
Jacobian coefficient is exactly `4 T E' + 3 U D' + 2 V C' + W B'
- D U' - 2 C V' - 3 B W' - 4 A X'`. -/
theorem differentialJacobian_coeff_3_monicSexticDecic_bridge
    (d : Derivation k F F) (f g : F[X])
    (_hf_high : ∀ n, 6 < n → f.coeff n = 0) (_hf6 : f.coeff 6 = 1)
    (_hf5 : f.coeff 5 = 0)
    (_hg_high : ∀ n, 10 < n → g.coeff n = 0) (_hg10 : g.coeff 10 = 1)
    (_hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 3 =
      (4 : F) * g.coeff 4 * d (f.coeff 0) +
        (3 : F) * g.coeff 3 * d (f.coeff 1) +
        (2 : F) * g.coeff 2 * d (f.coeff 2) +
        (1 : F) * g.coeff 1 * d (f.coeff 3) -
          (1 : F) * f.coeff 1 * d (g.coeff 3) -
          (2 : F) * f.coeff 2 * d (g.coeff 2) -
          (3 : F) * f.coeff 3 * d (g.coeff 1) -
          (4 : F) * f.coeff 4 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal 3 :
      Finset (ℕ × ℕ)) =
      ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne03_12 : ((0, 3) : ℕ × ℕ) ≠ (1, 2) := by decide
  have hne03_21 : ((0, 3) : ℕ × ℕ) ≠ (2, 1) := by decide
  have hne03_30 : ((0, 3) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hne12_21 : ((1, 2) : ℕ × ℕ) ≠ (2, 1) := by decide
  have hne12_30 : ((1, 2) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hne21_30 : ((2, 1) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 3 =
        (4 : F) * g.coeff 4 * d (f.coeff 0) +
          (3 : F) * g.coeff 3 * d (f.coeff 1) +
          (2 : F) * g.coeff 2 * d (f.coeff 2) +
          (1 : F) * g.coeff 1 * d (f.coeff 3) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne03_12, hne03_21, hne03_30]),
        Finset.sum_insert (by simp [hne12_21, hne12_30]),
        Finset.sum_insert (by simp [hne21_30]), Finset.sum_singleton]
      ring
    have hder3g : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2g : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0g : g.derivative.coeff 0 = (1 : F) * g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder3g, hder2g,
      hder1g, hder0g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 3 =
        (1 : F) * f.coeff 1 * d (g.coeff 3) +
          (2 : F) * f.coeff 2 * d (g.coeff 2) +
          (3 : F) * f.coeff 3 * d (g.coeff 1) +
          (4 : F) * f.coeff 4 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne03_12, hne03_21, hne03_30]),
        Finset.sum_insert (by simp [hne12_21, hne12_30]),
        Finset.sum_insert (by simp [hne21_30]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder0, hder1,
      hder2, hder3]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

end BridgeLambdaDepressedRow610

end Max11DegreeRoutes
