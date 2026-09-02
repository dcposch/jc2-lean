import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateBDivisorContinuationReductionScratch

/-! # Routing the unit `B`-divisor quotient into the common consumer

The preceding cancellation leaves one unit branch, with the two exact
conjugate faces
`phi(c)+2*A(c)*w(c)=0` and `3*w(c)*e(c)=A(c)*K(c)`.  The first is precisely
the input of the verified common-transverse construction.  The second is
retained in the original same-witness packet; that consumer does not require
an additional hypothesis from it.  The only source selector which does not
enter the common construction is the already named global `H | r` coordinate
limb.
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

section UnitBDivisorCommonRoutingAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Provenance-preserving inventory after routing the unit `Bq(c)` branch.
The first conjunct retains every quotient identity and both scalar faces. -/
def terminalRefinedIIIConjugateUnitBDivisorCommonRouting68
    (H A B D w phi e K D1 BW B2 F3 r : k[X]) (j a c : k) : Prop :=
  terminalRefinedIIIConjugateBDivisorContinuationReduction68
      H A B D w phi e K D1 BW B2 F3 j c ∧
    (terminalRefinedIIIConjugateIIFB2MultiplicityPacket68
        H A B D w e K D1 BW B2 F3 j c ∨
      H ∣ r ∨
      terminalRefinedIIIConjugateCommonTransverseNext68
        H A B D w phi e K j a c)

/-- The coordinate selector routes the unit quotient either to the common
consumer or to its pre-existing global `H | r` sibling. -/
theorem terminalRefinedIII_conjugate_unitB_divisor_common_routing_68
    (H t r X0 A B D w phi e K D1 BW B2 F3 : k[X])
    (j a c load : k)
    (hreduction :
      terminalRefinedIIIConjugateBDivisorContinuationReduction68
        H A B D w phi e K D1 BW B2 F3 j c)
    (hcoordinate : terminalRefinedIIIConjugateCoordinateResidual68
      H t r X0 B D w phi e K a c load)
    (hcommon :
      (B.eval a = 0 ∨
        (phi.derivative.eval a = 0 ∧
          (A.eval a = 0 ∨ w.derivative.eval a = 0))) →
      phi.eval c + 2 * A.eval c * w.eval c = 0 →
      terminalRefinedIIIConjugateCommonTransverseNext68
        H A B D w phi e K j a c) :
    terminalRefinedIIIConjugateUnitBDivisorCommonRouting68
      H A B D w phi e K D1 BW B2 F3 r j a c := by
  refine ⟨hreduction, ?_⟩
  obtain ⟨_hcontinuation, B1, M, Bq, Dq, Wq, hHM, hMc, hB1, hBq,
    hDq, hBWq, hB2, hWq, hI4q, hrowq, hfaceq, hsplit⟩ := hreduction
  rcases hsplit with hzero | hunit
  · exact Or.inl hzero.2
  rcases hcoordinate with hBa | hR | htransverse
  · exact Or.inr (Or.inr (hcommon (Or.inl hBa) hunit.2.1))
  · exact Or.inr (Or.inl hR)
  · obtain ⟨hBane, hrane, htc, hAc, hAa, hAane, hw1a, hphi1a,
      hphi2a, hI4a, hrowa⟩ := htransverse
    exact Or.inr (Or.inr
      (hcommon (Or.inr ⟨hphi1a, Or.inr hw1a⟩) hunit.2.1))

end UnitBDivisorCommonRoutingAlgebra68

section UnitBDivisorCommonRoutingSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Same-witness source wrapper.  It reconstructs the common packet from
the exact unit-quotient `G` face and the already retained global rows. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateUnitBDivisorCommonRouting
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 : k[X]) (a c : k)
    (hdeg : H.natDegree = 2)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hDa : D.eval a = 0) (hKa : K.eval a = 0)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H (cubicANumerator68 t r) C0 S.gamma =
      H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) b1 C0 E0
      S.gamma S.epsilon = H ^ 2 * phi)
    (hX : C 3 * t - r ^ 2 = H * X0)
    (hBshape : B = (X - C c) ^ 2 * B2)
    (hFshape : cubicANumerator68 t r * B - C 3 * D =
      (X - C c) ^ 3 * F3)
    (hDshape : D = H * D1)
    (hBWshape : B * w = H * BW)
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
    (hcontinuation : terminalRefinedIIIConjugateBDivisorContinuation68 H B D
      w phi (terminalEDerivativeNumerator68 H E0) K D1 BW j)
    (hcoordinate : terminalRefinedIIIConjugateCoordinateResidual68 H t r X0
      B D w phi (terminalEDerivativeNumerator68 H E0) K a c
      (6 * j * H.derivative.eval a ^ 3)) :
    terminalRefinedIIIConjugateUnitBDivisorCommonRouting68 H
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 r j a c := by
  have hh : H.derivative.eval c ≠ 0 :=
    nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hc
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hreduction :=
    S.terminalRefinedIIIConjugateBDivisorContinuationReduction (H := H)
      t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hdeg hb hW hPhi hX
      hc hBshape hFshape hDshape hBWshape hrowq hnormalized hcontinuation
  apply terminalRefinedIII_conjugate_unitB_divisor_common_routing_68 H
    t r X0 (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3
      j a c (6 * j * H.derivative.eval a ^ 3) hreduction hcoordinate
  intro hselector hG
  have hF0 : (cubicANumerator68 t r).eval c * B.eval c -
      3 * D.eval c = 0 := by
    have hf := congrArg (fun P : k[X] => P.eval c) hFshape
    simp [eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hf
    exact hf
  have hprev := terminalRefinedIII_conjugateCommon_transverse_68 H
    (cubicANumerator68 t r) B D w phi
    (terminalEDerivativeNumerator68 H E0) K j a c hdeg hsimple
    ha hc hac hwa hphia hDa hKa hI4 hrow hselector hF0 hG
  exact terminalRefinedIII_conjugateCommon_transverseNext_68 H
    (cubicANumerator68 t r) B D w phi
    (terminalEDerivativeNumerator68 H E0) K j a c hdeg hsimple
    ha hc hac hwa hphia hDa hKa hI4 hrow hF0 hprev

end UnitBDivisorCommonRoutingSource68

end Max11DegreeRoutes
