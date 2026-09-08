import Sol610ScaleTwoAlignedFourteenthResidualDerivScratch

/-! # Monic differential-Jacobian bridge for the aligned `(6,10)` ν tail

The preceding file verifies the scalar row certificate.  This module derives
those exact rows from one depressed monic differential Jacobian, including the
previously missing degree-one coefficient, and applies the certificate.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000

section DegreeOneDepressedRow610

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Degree one of the differential Jacobian of a depressed monic sextic and
a monic decic.  The high-degree assumptions are retained for a uniform API
with the already verified rows thirteen through two. -/
theorem differentialJacobian_coeff_1_monicSexticDecic
    (d : Derivation k F F) (f g : F[X])
    (_hf_high : ∀ n, 6 < n → f.coeff n = 0) (_hf6 : f.coeff 6 = 1)
    (_hf5 : f.coeff 5 = 0)
    (_hg_high : ∀ n, 10 < n → g.coeff n = 0) (_hg10 : g.coeff 10 = 1)
    (_hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 1 =
      (2 : F) * g.coeff 2 * d (f.coeff 0) +
        (1 : F) * g.coeff 1 * d (f.coeff 1) -
          (1 : F) * f.coeff 1 * d (g.coeff 1) -
          (2 : F) * f.coeff 2 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal 1 :
      Finset (ℕ × ℕ)) =
      ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne : ((0, 1) : ℕ × ℕ) ≠ (1, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 1 =
        (2 : F) * g.coeff 2 * d (f.coeff 0) +
          (1 : F) * g.coeff 1 * d (f.coeff 1) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder0g : g.derivative.coeff 0 = (1 : F) * g.coeff 1 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder1g, hder0g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 1 =
        (1 : F) * f.coeff 1 * d (g.coeff 1) +
          (2 : F) * f.coeff 2 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    have hder0f : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder1f : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder0f, hder1f]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

end DegreeOneDepressedRow610

section MonicDifferentialBridge610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- A constant depressed differential Jacobian makes the weight-seventy
fourth-tail residual a differential constant. -/
theorem fourteenthResidual610_deriv_zero_of_monic_differentialJacobian
    (d : Derivation k F F) (f g : F[X]) (c : F)
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0)
    (hjac : differentialJacobian d f g = Polynomial.C c) :
    d (fourteenthResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
      (g.coeff 1)) = 0 := by
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian d f g).coeff n = 0 := by
    rw [hjac]
    simp [Polynomial.coeff_C, hn]
  have h13 := (differentialJacobian_coeff_13_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 9 (by norm_num))
  have h8 := (differentialJacobian_coeff_8_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 8 (by norm_num))
  have h7 := (differentialJacobian_coeff_7_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 7 (by norm_num))
  have h6 := (differentialJacobian_coeff_6_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 6 (by norm_num))
  have h5 := (differentialJacobian_coeff_5_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 5 (by norm_num))
  have h4 := (differentialJacobian_coeff_4_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 4 (by norm_num))
  have h3 := (differentialJacobian_coeff_3_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 3 (by norm_num))
  have h1 := (differentialJacobian_coeff_1_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 1 (by norm_num))
  apply fourteenthResidual610_deriv_zero_of_depressed_rows d
    (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hL
  · linear_combination h13
  · linear_combination h12
  · linear_combination h11
  · linear_combination h10
  · linear_combination h9
  · linear_combination h8
  · linear_combination h7
  · linear_combination h6
  · linear_combination h5
  · linear_combination h4
  · linear_combination h3
  · linear_combination h1

#print axioms differentialJacobian_coeff_1_monicSexticDecic
#print axioms fourteenthResidual610_deriv_zero_of_monic_differentialJacobian

end MonicDifferentialBridge610

end Max11DegreeRoutes
