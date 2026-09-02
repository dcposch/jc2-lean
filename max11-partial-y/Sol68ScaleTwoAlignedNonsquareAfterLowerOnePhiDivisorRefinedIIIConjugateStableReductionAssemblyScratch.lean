import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateCommonTransverseNextReductionScratch

/-! # Provenance-preserving stable reduction assembly

This file refines the `CommonTransverseNext` limb of the stable same-witness
assembly.  The coordinate packet routes its new `r(a)=0` exit into either the
canonical R-divisor lower-zero consumer or the global `H | B` exit.  The
latter is cancelled once in the already retained `I4` and `BW` identities.
No existential packet is reselected.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section StableReductionAssemblyAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The exact once-cancelled packet on the global `H | B` exit. -/
def terminalRefinedIIIConjugateBDivisorContinuation68
    (H B D w phi e K D1 BW : k[X]) (j : k) : Prop :=
  ∃ B1 : k[X],
    B = H * B1 ∧
    B1 * w = BW ∧
    B1 * phi + 6 * w * D1 = 0 ∧
    BW * e - D1 * K = C j * H ^ 2

/-- The sole unconsumed order-two common limb.  Its original packet is kept
literally, together with the conjugate `D1` root and its exact divisor/unit
split. -/
def terminalRefinedIIIConjugateCommonDeepResidual68
    (H A B D w phi e K : k[X]) (j a c : k) : Prop :=
  terminalRefinedIIIConjugateCommonTransverseNext68
      H A B D w phi e K j a c ∧
    w.eval c ≠ 0 ∧ B.eval a ≠ 0 ∧ A.eval a ≠ 0 ∧
    ∃ D1 : k[X], D = H * D1 ∧ D1.eval c = 0 ∧
      (H ^ 2 ∣ D ∨ D.derivative.eval a ≠ 0)

/-- Stable inventory after consuming the cheap common exits. -/
def terminalRefinedIIIConjugateStableReductionResidual68
    (H r t X0 Yd p3 p4 p0 p1 p2 A B D w phi e K phi1 k1 D1 BW : k[X])
    (alpha gamma epsilon eta j a c : k) : Prop :=
  (∃ s t1 y1 A1 c2 e3 psi m : k[X],
      terminalRefinedIIIConjugateRDivisorLocalContinuation68
        H r t X0 Yd p3 p4 s t1 y1 p0 p1 p2 B D w phi e K phi1 k1 j ∧
      terminalRefinedIIIRDivisorLowerZeroAllocation68
        H A1 B c2 D e3 psi m phi1 k1 w alpha gamma epsilon eta j) ∨
    terminalRefinedIIIConjugateBDivisorContinuation68
      H B D w phi e K D1 BW j ∨
    (w.eval c = 0 ∧ phi.eval c = 0 ∧ H ∣ w ∧ H ∣ phi ∧
      ((D.eval c = 0 ∧ H ∣ D) ∨ (K.eval c = 0 ∧ H ∣ K))) ∨
    terminalRefinedIIIConjugateCommonDeepResidual68
      H A B D w phi e K j a c

end StableReductionAssemblyAlgebra68

section StableReductionAssemblySource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing refinement of `terminalRefinedIIIConjugateStableAssembly`.
All quotient witnesses are the fixed arguments of the stable source packet. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateStableReductionAssembly
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X0 Yd C0 E0 b1 B D w phi K D1 BW B2 F3 phi1 k1 : k[X])
    (a c : k)
    (hdeg : H.natDegree = 2)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hDa : D.eval a = 0) (hKa : K.eval a = 0)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H (cubicANumerator68 t r) C0 S.gamma =
      H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) b1 C0 E0
      S.gamma S.epsilon = H ^ 2 * phi)
    (hp4 : p.coeff 4 = H * t)
    (hX : C 3 * t - r ^ 2 = H * X0)
    (hY : C 27 * p.coeff 3 - r ^ 3 = H * Yd)
    (hC0 : C0 = cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
    (hE0 : E0 = cubicENumerator68 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) t r)
    (hB : B = (X - C c) ^ 2 * B2)
    (hF : cubicANumerator68 t r * B - C 3 * D =
      (X - C c) ^ 3 * F3)
    (hDshape : D = H * D1)
    (hBWshape : B * w = H * BW)
    (hI4q : B * phi + C 6 * H * w * D1 = 0)
    (hrowq : BW * terminalEDerivativeNumerator68 H E0 - D1 * K =
      C j * H ^ 2)
    (hI4 : B * phi + C 6 * w * D = 0)
    (hrow : B * w * terminalEDerivativeNumerator68 H E0 - D * K =
      C j * H ^ 3)
    (hnormalized :
      3 * H.derivative.eval c * F3.eval c =
        (2 * (cubicANumerator68 t r).eval c *
            H.derivative.derivative.eval c +
          3 * H.derivative.eval c *
            (cubicANumerator68 t r).derivative.eval c) * B2.eval c)
    (hj : j ≠ 0)
    (hwitness : terminalRefinedIIIConjugateRDivisorPreDivisionWitnesses68
      H phi K phi1 k1)
    (hlower : terminalLowerZeroCleared68 H (cubicANumerator68 t r) (H * B)
      (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) (H * D)
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r) S.alpha S.gamma S.epsilon S.eta = 0)
    (hinventory : terminalRefinedIIIConjugateCommonIIResidual68 H
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K r j a c)
    (hcoordinate : terminalRefinedIIIConjugateCoordinateResidual68 H t r X0
      B D w phi (terminalEDerivativeNumerator68 H E0) K a c
      (6 * j * H.derivative.eval a ^ 3)) :
    terminalRefinedIIIConjugateStableReductionResidual68 H r t X0 Yd
      (p.coeff 3) (p.coeff 4) (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K phi1 k1 D1 BW
      S.alpha S.gamma S.epsilon S.eta j a c := by
  subst C0
  subst E0
  have hstable := S.terminalRefinedIIIConjugateStableAssembly (H := H)
    t r X0 Yd
    (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
    b1 B D w phi K D1 BW B2 F3 phi1 k1 a c hdeg ha hc hac hwa
    hphia hDa hKa hb hW hPhi hp4 hX hY rfl rfl hB hF hDshape
    hBWshape hI4q hrowq hI4 hrow hnormalized hj hwitness hlower
    hinventory hcoordinate
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hbc : B.eval c = 0 := by rw [hB]; simp
  have hBroute (hBd : H ∣ B) :
      terminalRefinedIIIConjugateBDivisorContinuation68 H B D w phi
        (terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r)) K D1 BW j := by
    obtain ⟨B1, hB1⟩ := hBd
    refine ⟨B1, hB1, ?_, ?_, hrowq⟩
    · apply mul_left_cancel₀ hH
      rw [hB1] at hBWshape
      linear_combination hBWshape
    · apply mul_left_cancel₀ hH
      rw [hB1] at hI4q
      rw [show C (6 : k) = (6 : k[X]) from C_eq_natCast 6] at hI4q
      linear_combination hI4q
  have hRroute (hrd : H ∣ r) :
      ∃ s t1 y1 A1 c2 e3 psi m : k[X],
        terminalRefinedIIIConjugateRDivisorLocalContinuation68
          H r t X0 Yd (p.coeff 3) (p.coeff 4) s t1 y1
          (p.coeff 0) (p.coeff 1) (p.coeff 2) B D w phi
          (terminalEDerivativeNumerator68 H
            (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r)) K phi1 k1 j ∧
        terminalRefinedIIIRDivisorLowerZeroAllocation68
          H A1 B c2 D e3 psi m phi1 k1 w
          S.alpha S.gamma S.epsilon S.eta j := by
    obtain ⟨s, hs⟩ := hrd
    let t1 : k[X] := C (1 / 3 : k) * (H * s ^ 2 + X0)
    let y1 : k[X] := C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)
    have hcascade := rDivisor_coordinate_cascade_68 H r t X0 Yd
      (p.coeff 3) (p.coeff 4) s hs hp4 hX hY
    have hcontinuation :=
      terminalRefinedIII_conjugate_rDivisor_localContinuation_68
        H r t X0 Yd (p.coeff 3) (p.coeff 4) s t1 y1
        (p.coeff 0) (p.coeff 1) (p.coeff 2) B D w phi K phi1 k1 j
        hs hcascade.1 hcascade.2.2.1 hcascade.2.2.2.1 hcascade.2.1
        hcascade.2.2.2.2 hwitness hI4 hrow
    have hPhiPre : terminalScaledPhi68 H (cubicANumerator68 t r) (H * B)
        (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) S.gamma S.epsilon = H * phi1 := by
      rw [hwitness.1]
      rw [hb] at hPhi
      simpa only [pow_two, mul_assoc] using hPhi
    obtain ⟨A1, c2, e3, psi, m, hallocation⟩ :=
      S.terminalRefinedIIIRDivisorLowerZeroConsume (H := H)
        r t X0 Yd s t1 y1 B D w phi K phi1 k1 hdeg hj hcontinuation
        hW hPhiPre hlower
    exact ⟨s, t1, y1, A1, c2, e3, psi, m, hcontinuation, hallocation⟩
  rcases hstable with hR | hcommon | hIII
  · exact Or.inl hR
  · have hreduced :=
      S.terminalRefinedIIIConjugateCommonTransverseNextReduction (H := H)
        t r X0 (cubicANumerator68 t r) B D w phi
        (terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r)) K B2 D1 a c hdeg ha hc hac rfl hX hB
        hDshape hcommon
    rcases hreduced.2 with hIII' | hBd | hra | hdeep
    · exact Or.inr (Or.inr (Or.inl hIII'))
    · exact Or.inr (Or.inl (hBroute hBd.2))
    · rcases hcoordinate with hBa | hrd | htrans
      · have hBd : H ∣ B := dvd_of_two_simple_root_evals_68 H B
          hdeg hsimple a c hac ha hc hBa hbc
        exact Or.inr (Or.inl (hBroute hBd))
      · exact Or.inl (hRroute hrd)
      · exact (htrans.2.1 hra.2).elim
    · exact Or.inr (Or.inr (Or.inr ⟨hreduced.1, hdeep⟩))
  · exact Or.inr (Or.inr (Or.inl hIII))

end StableReductionAssemblySource68

end Max11DegreeRoutes
