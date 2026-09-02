import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateCanonicalRDivisorBridgeScratch

/-! # Reusable lower-zero consumer for the canonical R-divisor packet -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section RefinedIIIConjugateRDivisorLowerZeroAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The finite allocation already extracted by the R-divisor lower-zero
argument, separated from its former monolithic source wrapper. -/
def terminalRefinedIIIRDivisorLowerZeroAllocation68
    (H A1 B c2 D e3 psi m phi1 k1 w : k[X])
    (alpha gamma epsilon eta j : k) : Prop :=
  c2 = C (1 / 3 : k) * A1 ^ 2 + C (9 / 4 : k) * w -
      C (3 / 2 * gamma : k) ∧
    psi = rDivisorLowerZeroPhiQuotient68 H A1 B c2 e3 gamma epsilon ∧
    phi1 = H ^ 2 * psi ∧ H ^ 2 ∣ phi1 ∧ H ∣ phi1 ∧
    w * D = -(C (1 / 6 : k)) * (H * B * psi) ∧ H ∣ w * D ∧
    rDivisorLowerZeroQuotient68 H A1 B c2 D e3
      alpha gamma epsilon eta = 0 ∧
    H ∣ D * psi ∧
    (∀ a : k, H.eval a = 0 →
      (w * D).eval a = 0 ∧ (D * psi).eval a = 0 ∧
        D.eval a * k1.eval a = 0) ∧
    m = H * B * w * e3.derivative - C j ∧
    D * k1 = H ^ 4 * m ∧ H ^ 4 ∣ D * k1 ∧
    (∀ a : k, H.eval a = 0 → m.eval a = -j ∧ m.eval a ≠ 0) ∧
    D ≠ 0 ∧ k1 ≠ 0

/-- Local lower-zero consumer.  `hcontinuation` supplies the exact coordinate
cascade, numerator factors and pre-division invariant rows.  The remaining
three hypotheses are precisely the source transports formerly rebuilt inside
the monolithic theorem: scaled `W`, scaled `Phi`, and the cleared lower row. -/
theorem terminalRefinedIII_rDivisor_lowerZero_consumer_68
    (H r t X0 Yd p3 p4 s t1 y1 p0 p1 p2 B D w phi K phi1 k1 : k[X])
    (alpha gamma epsilon eta j : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hH : H ≠ 0) (hj : j ≠ 0)
    (hcontinuation : terminalRefinedIIIConjugateRDivisorLocalContinuation68
      H r t X0 Yd p3 p4 s t1 y1 p0 p1 p2 B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H p0 p1 p2 p3 t r))
      K phi1 k1 j)
    (hW : terminalScaledW68 H (cubicANumerator68 t r)
        (cubicCNumerator68 H p2 p3 t r) gamma = H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) (H * B)
        (cubicCNumerator68 H p2 p3 t r)
        (cubicENumerator68 H p0 p1 p2 p3 t r) gamma epsilon = H * phi1)
    (hlower : terminalLowerZeroCleared68 H (cubicANumerator68 t r) (H * B)
        (cubicCNumerator68 H p2 p3 t r) (H * D)
        (cubicENumerator68 H p0 p1 p2 p3 t r)
        alpha gamma epsilon eta = 0) :
    ∃ A1 c2 e3 psi m : k[X],
      terminalRefinedIIIRDivisorLowerZeroAllocation68
        H A1 B c2 D e3 psi m phi1 k1 w alpha gamma epsilon eta j := by
  rcases hcontinuation with
    ⟨hr, ht, hp4, hp3, h3, h27, A1, C1, e3, m,
      hA1, hC1, he3, hA, hC, hE, heDot, hwitness,
      hI4, hrow, hm, hdk⟩
  let c2 : k[X] := C (1 / 3 : k) * A1 ^ 2 + C (9 / 4 : k) * w -
    C (3 / 2 * gamma : k)
  let psi : k[X] :=
    rDivisorLowerZeroPhiQuotient68 H A1 B c2 e3 gamma epsilon
  have hCshape : cubicCNumerator68 H p2 p3 t r =
      C (1 / 3 : k) * (cubicANumerator68 t r) ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hWm := congrArg (algebraMap k[X] (RatFunc k)) hW
    dsimp only [terminalScaledW68] at hWm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hWm ⊢
    linear_combination (9 / 4 : RatFunc k) * hWm
  have hC2 : cubicCNumerator68 H p2 p3 t r = H ^ 2 * c2 := by
    rw [hCshape, hA]
    dsimp only [c2]
    ring
  have hphi2 : phi1 = H ^ 2 * psi := by
    apply mul_left_cancel₀ hH
    rw [← hPhi, hA, hC2, hE,
      rDivisorLowerZero_phi_factor_68]
    dsimp only [psi]
    ring
  have hwd6 : (6 : k[X]) * (w * D) = -(H * B * psi) := by
    apply mul_left_cancel₀ hH
    linear_combination hI4 - B * hphi2
  have hwd : w * D = -(C (1 / 6 : k)) * (H * B * psi) := by
    linear_combination C (1 / 6 : k) * hwd6 -
      w * D * rDivisorLowerZeroSixUnit68 (k := k)
  have hbranch : terminalLowerZeroCleared68 H (H * A1) (H * B)
      (H ^ 2 * c2) (H * D) (H ^ 3 * e3)
      alpha gamma epsilon eta = 0 := by
    rw [← hA, ← hC2, ← hE]
    exact hlower
  have hQ : rDivisorLowerZeroQuotient68 H A1 B c2 D e3
      alpha gamma epsilon eta = 0 := by
    have hz : H ^ 4 * rDivisorLowerZeroQuotient68 H A1 B c2 D e3
        alpha gamma epsilon eta = 0 := by
      rw [← rDivisorLowerZero_row_factor_68]
      exact hbranch
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 4 hH)
  have hfaces : ∀ a : k, H.eval a = 0 →
      (w * D).eval a = 0 ∧ (D * psi).eval a = 0 ∧
        D.eval a * k1.eval a = 0 := by
    intro a ha
    have hf := rDivisorLowerZero_root_faces_68 H A1 B c2 D e3 w psi
      alpha gamma epsilon eta rfl rfl hwd hQ a ha (hsimple a ha)
    refine ⟨hf.1, hf.2, ?_⟩
    have hdka := congrArg (fun P : k[X] => P.eval a) hdk
    simpa [ha] using hdka
  have hdpsi : H ∣ D * psi :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hfaces a ha).2.1)
  have hval : ∀ a : k, H.eval a = 0 →
      m.eval a = -j ∧ m.eval a ≠ 0 := by
    intro a ha
    have hmval : m.eval a = -j := by
      rw [hm]
      exact rDivisor_cofactor_eval_68 H B w e3 j a ha
    exact ⟨hmval, by rw [hmval]; exact neg_ne_zero.mpr hj⟩
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a0, ha0⟩ := IsAlgClosed.exists_root H hdegne
  have hne := rDivisor_factors_ne_zero_68 H D k1 m j hj hH hdk
    a0 ha0 (hval a0 ha0).1
  refine ⟨A1, c2, e3, psi, m, rfl, rfl, hphi2,
    ⟨psi, hphi2⟩, ⟨H * psi, ?_⟩, hwd,
    ⟨-(C (1 / 6 : k)) * (B * psi), ?_⟩, hQ, hdpsi, hfaces,
    hm, hdk, ⟨m, hdk⟩, hval, hne.1, hne.2⟩
  · rw [hphi2]
    ring
  · rw [hwd]
    ring

end RefinedIIIConjugateRDivisorLowerZeroAlgebra68

section RefinedIIIConjugateRDivisorLowerZeroSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing interface: the canonical continuation and the three exact
source transports feed the reusable lower-zero consumer.  Unlike the old
monolithic theorem, no quotient is reselected here. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIRDivisorLowerZeroConsume
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd s t1 y1 B D w phi K phi1 k1 : k[X])
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (hcontinuation : terminalRefinedIIIConjugateRDivisorLocalContinuation68
      H r t X0 Yd (p.coeff 3) (p.coeff 4) s t1 y1
      (p.coeff 0) (p.coeff 1) (p.coeff 2) B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) K phi1 k1 j)
    (hW : terminalScaledW68 H (cubicANumerator68 t r)
        (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) S.gamma =
      H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) (H * B)
        (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) S.gamma S.epsilon = H * phi1)
    (hlower : terminalLowerZeroCleared68 H (cubicANumerator68 t r) (H * B)
        (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) (H * D)
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) S.alpha S.gamma S.epsilon S.eta = 0) :
    ∃ A1 c2 e3 psi m : k[X],
      terminalRefinedIIIRDivisorLowerZeroAllocation68 H A1 B c2 D e3
        psi m phi1 k1 w S.alpha S.gamma S.epsilon S.eta j := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  exact terminalRefinedIII_rDivisor_lowerZero_consumer_68
    H r t X0 Yd (p.coeff 3) (p.coeff 4) s t1 y1
    (p.coeff 0) (p.coeff 1) (p.coeff 2) B D w phi K phi1 k1
    S.alpha S.gamma S.epsilon S.eta j hdeg hsimple
    (H_ne_zero_of_nonsquare68 (H := H)) hj hcontinuation hW hPhi hlower

end RefinedIIIConjugateRDivisorLowerZeroSource68

end Max11DegreeRoutes
