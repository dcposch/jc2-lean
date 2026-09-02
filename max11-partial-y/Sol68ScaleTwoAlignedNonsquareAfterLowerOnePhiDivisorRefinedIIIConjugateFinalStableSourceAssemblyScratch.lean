import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateUnitBDivisorCommonRoutingScratch

/-! # Final provenance-preserving nonsquare stable source inventory

This assembly removes the intermediate `B`-divisor and `B2`-multiplicity
bookkeeping from the stable source result.  Every coordinate `H | r` exit is
sent to the canonical local continuation/lower-zero consumer, while both
`B`-quotient branches rejoin the single verified common-transverse handoff.
The component-III `D/K` allocation and the genuine deep common limb remain
explicit and disjoint source handoffs.  No monolithic existential allocation
packet is imported or reconciled.
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

section FinalStableSourceResidualAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Canonical same-coordinate `R`-divisor handoff to the verified finite
lower-zero allocation. -/
def terminalRefinedIIIConjugateCanonicalRLowerZeroHandoff68
    (H r t X0 Yd p3 p4 p0 p1 p2 B D w phi e K phi1 k1 : k[X])
    (alpha gamma epsilon eta j : k) : Prop :=
  ∃ s t1 y1 A1 c2 e3 psi m : k[X],
    terminalRefinedIIIConjugateRDivisorLocalContinuation68
      H r t X0 Yd p3 p4 s t1 y1 p0 p1 p2 B D w phi e K phi1 k1 j ∧
    terminalRefinedIIIRDivisorLowerZeroAllocation68
      H A1 B c2 D e3 psi m phi1 k1 w alpha gamma epsilon eta j

/-- Authoritative residual inventory for the normalized aligned-nonsquare
source branch.  Intermediate quotient selections no longer appear. -/
def terminalRefinedIIIConjugateFinalStableSourceResidual68
    (H r t X0 Yd p3 p4 p0 p1 p2 A B D w phi e K phi1 k1 : k[X])
    (alpha gamma epsilon eta j a c : k) : Prop :=
  terminalRefinedIIIConjugateCanonicalRLowerZeroHandoff68 H r t X0 Yd
      p3 p4 p0 p1 p2 B D w phi e K phi1 k1
      alpha gamma epsilon eta j ∨
    terminalRefinedIIIConjugateCommonTransverseNext68
      H A B D w phi e K j a c ∨
    (w.eval c = 0 ∧ phi.eval c = 0 ∧ H ∣ w ∧ H ∣ phi ∧
      ((D.eval c = 0 ∧ H ∣ D) ∨ (K.eval c = 0 ∧ H ∣ K))) ∨
    terminalRefinedIIIConjugateCommonDeepResidual68
      H A B D w phi e K j a c

end FinalStableSourceResidualAlgebra68

section FinalStableSourceResidualSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Final source-facing stable assembly.  All quotient witnesses used in the
proof are the fixed witnesses supplied in this theorem's arguments. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateFinalStableSourceAssembly
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
    terminalRefinedIIIConjugateFinalStableSourceResidual68 H r t X0 Yd
      (p.coeff 3) (p.coeff 4) (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K phi1 k1
      S.alpha S.gamma S.epsilon S.eta j a c := by
  subst C0
  subst E0
  let E := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let e := terminalEDerivativeNumerator68 H E
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hh : H.derivative.eval c ≠ 0 :=
    nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hc
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hF0 : (cubicANumerator68 t r).eval c * B.eval c -
      3 * D.eval c = 0 := by
    have hf := congrArg (fun P : k[X] => P.eval c) hF
    simp [eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hf
    exact hf
  have commonNext (hselector : B.eval a = 0 ∨
      (phi.derivative.eval a = 0 ∧
        ((cubicANumerator68 t r).eval a = 0 ∨
          w.derivative.eval a = 0)))
      (hG : phi.eval c +
        2 * (cubicANumerator68 t r).eval c * w.eval c = 0) :
      terminalRefinedIIIConjugateCommonTransverseNext68 H
        (cubicANumerator68 t r) B D w phi e K j a c := by
    have hprev := terminalRefinedIII_conjugateCommon_transverse_68 H
      (cubicANumerator68 t r) B D w phi e K j a c hdeg hsimple
      ha hc hac hwa hphia hDa hKa hI4 hrow hselector hF0 hG
    exact terminalRefinedIII_conjugateCommon_transverseNext_68 H
      (cubicANumerator68 t r) B D w phi e K j a c hdeg hsimple
      ha hc hac hwa hphia hDa hKa hI4 hrow hF0 hprev
  have hRroute (hrd : H ∣ r) :
      terminalRefinedIIIConjugateCanonicalRLowerZeroHandoff68 H r t X0 Yd
        (p.coeff 3) (p.coeff 4) (p.coeff 0) (p.coeff 1) (p.coeff 2)
        B D w phi e K phi1 k1
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
        (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) E
        S.gamma S.epsilon = H * phi1 := by
      rw [hwitness.1]
      rw [hb] at hPhi
      simpa only [pow_two, mul_assoc] using hPhi
    obtain ⟨A1, c2, e3, psi, m, hallocation⟩ :=
      S.terminalRefinedIIIRDivisorLowerZeroConsume (H := H)
        r t X0 Yd s t1 y1 B D w phi K phi1 k1 hdeg hj hcontinuation
        hW hPhiPre hlower
    exact ⟨s, t1, y1, A1, c2, e3, psi, m, hcontinuation, hallocation⟩
  have routeG (hG : phi.eval c +
      2 * (cubicANumerator68 t r).eval c * w.eval c = 0) :
      terminalRefinedIIIConjugateCanonicalRLowerZeroHandoff68 H r t X0 Yd
          (p.coeff 3) (p.coeff 4) (p.coeff 0) (p.coeff 1) (p.coeff 2)
          B D w phi e K phi1 k1
          S.alpha S.gamma S.epsilon S.eta j ∨
        terminalRefinedIIIConjugateCommonTransverseNext68 H
          (cubicANumerator68 t r) B D w phi e K j a c := by
    rcases hcoordinate with hBa | hrd | htransverse
    · exact Or.inr (commonNext (Or.inl hBa) hG)
    · exact Or.inl (hRroute hrd)
    · obtain ⟨hBane, hrane, htc, hAc, hAa, hAane, hw1a, hphi1a,
        hphi2a, hI4a, hrowa⟩ := htransverse
      exact Or.inr (commonNext (Or.inr ⟨hphi1a, Or.inr hw1a⟩) hG)
  have hstable := S.terminalRefinedIIIConjugateStableReductionAssembly
    (H := H) t r X0 Yd
    (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) E
    b1 B D w phi K D1 BW B2 F3 phi1 k1 a c hdeg ha hc hac hwa
    hphia hDa hKa hb hW hPhi hp4 hX hY rfl rfl hB hF hDshape
    hBWshape hI4q hrowq hI4 hrow hnormalized hj hwitness hlower
    hinventory hcoordinate
  rcases hstable with hR | hrest
  · exact Or.inl hR
  rcases hrest with hBcontinuation | hrest
  · have hrouted :=
      S.terminalRefinedIIIConjugateUnitBDivisorCommonRouting (H := H)
        t r X0
        (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) E
        b1 B D w phi K D1 BW B2 F3 a c hdeg ha hc hac hwa hphia hDa
        hKa hb hW hPhi hX hB hF hDshape hBWshape hrowq hI4 hrow
        hnormalized hBcontinuation hcoordinate
    rcases hrouted.2 with hB2packet | hrd | hnext
    · have hG := terminalRefinedIII_B2_multiplicity_I4_common_68 H
        (cubicANumerator68 t r) B D w phi e K D1 BW B2 F3 j c
        hh hj hI4q hB2packet
      rcases routeG hG with hR' | hnext'
      · exact Or.inl hR'
      · exact Or.inr (Or.inl hnext')
    · exact Or.inl (hRroute hrd)
    · exact Or.inr (Or.inl hnext)
  rcases hrest with hIII | hdeep
  · exact Or.inr (Or.inr (Or.inl hIII))
  · exact Or.inr (Or.inr (Or.inr hdeep))

end FinalStableSourceResidualSource68

end Max11DegreeRoutes
