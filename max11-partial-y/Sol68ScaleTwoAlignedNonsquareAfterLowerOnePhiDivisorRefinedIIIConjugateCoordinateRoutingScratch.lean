import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateCoordinateSiblingScratch
import Fable68ScaleTwoAlignedNonsquareRDivisorScratch

/-! # Routing every conjugate coordinate sibling to a verified consumer -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateCoordinateRoutingAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The coordinate sibling has only two consumers: the exact first
R-divisor cascade, or the already verified common-transverse packet. -/
def terminalRefinedIIIConjugateCoordinateRouted68
    (H t r X Yd p3 p4 A b D w phi e K : k[X]) (j a c : k) : Prop :=
  (∃ s t1 y1 : k[X],
      r = H * s ∧ t = H * t1 ∧
      C 3 * t1 = H * s ^ 2 + X ∧
      H ∣ t ∧ H ^ 2 ∣ p4 ∧ H ∣ p3 ∧
      p4 = H ^ 2 * t1 ∧ p3 = H * y1 ∧
      C 27 * y1 = H ^ 2 * s ^ 3 + Yd) ∨
    terminalRefinedIIIConjugateCommonTransverseNext68
      H A b D w phi e K j a c

end RefinedIIIConjugateCoordinateRoutingAlgebra68

section RefinedIIIConjugateCoordinateRoutingSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing routing of all three coordinate limbs.

* `b(a)=0` is exactly Fable's preserved deep selector;
* `H ∣ r` enters the verified R-divisor coordinate cascade;
* the nonzero-`r` transverse packet supplies `A(a)≠0`, `w'(a)=phi'(a)=0`,
  hence the other Fable selector.

The common `F,G` faces at `c` are reconstructed from the same normalized
component-II source packet, including its already-closed `B2(c)=0` child. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateCoordinateRouting
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X0 Yd C0 E0 b1 B D w phi K D1 BW B2 F3 : k[X]) (a c : k)
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
    (hcoordinate : terminalRefinedIIIConjugateCoordinateResidual68 H t r X0
      B D w phi (terminalEDerivativeNumerator68 H E0) K a c
      (6 * j * H.derivative.eval a ^ 3)) :
    terminalRefinedIIIConjugateCoordinateRouted68 H t r X0 Yd
      (p.coeff 3) (p.coeff 4) (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K j a c := by
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  obtain ⟨_, M, D2, BW1, hHM, hMc, hD2, hBW1, hDcore,
      hBWcore, hrow1, hsplit⟩ :=
    S.terminalRefinedIIIConjugateIIFLoadedRoutingPacket (H := H)
      t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW hPhi hX
      hc (hsimple c hc) hB hF hDshape hBWshape hrowq hnormalized
  have hF0 : (cubicANumerator68 t r).eval c * B.eval c -
      3 * D.eval c = 0 := by
    have hf := congrArg (fun P : k[X] => P.eval c) hF
    simp [eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hf
    exact hf
  have hG0 : phi.eval c +
      2 * (cubicANumerator68 t r).eval c * w.eval c = 0 := by
    by_cases hB2zero : B2.eval c = 0
    · have hpacket := S.terminalRefinedIIIConjugateIIFB2MultiplicityPacket
        (H := H) t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW
        hPhi hX hc (hsimple c hc) hB hF hDshape hBWshape hrowq
        hnormalized hB2zero
      exact terminalRefinedIII_B2_multiplicity_I4_common_68 H
        (cubicANumerator68 t r) B D w phi
        (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 j c
        (hsimple c hc) hj hI4q hpacket
    · exact terminalRefinedIII_normalized_loaded_factor_I4_G_68 H
        (cubicANumerator68 t r) B D w phi D1 B2 F3 M D2 c
        hHM hMc hB hD2 hDcore hI4q hB2zero
  have commonNext (hsplita : B.eval a = 0 ∨
      (phi.derivative.eval a = 0 ∧
        ((cubicANumerator68 t r).eval a = 0 ∨ w.derivative.eval a = 0))) :
      terminalRefinedIIIConjugateCommonTransverseNext68 H
        (cubicANumerator68 t r) B D w phi
        (terminalEDerivativeNumerator68 H E0) K j a c := by
    have hprev := terminalRefinedIII_conjugateCommon_transverse_68 H
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K j a c hdeg hsimple
      ha hc hac hwa hphia hDa hKa hI4 hrow hsplita hF0 hG0
    exact terminalRefinedIII_conjugateCommon_transverseNext_68 H
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K j a c hdeg hsimple
      ha hc hac hwa hphia hDa hKa hI4 hrow hF0 hprev
  rcases hcoordinate with hba | hr | htrans
  · exact Or.inr (commonNext (Or.inl hba))
  · left
    obtain ⟨s, hs⟩ := hr
    let t1 : k[X] := C (1 / 3 : k) * (H * s ^ 2 + X0)
    let y1 : k[X] := C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)
    have hcascade := rDivisor_coordinate_cascade_68 H r t X0 Yd
      (p.coeff 3) (p.coeff 4) s hs hp4 hX hY
    refine ⟨s, t1, y1, hs, hcascade.1, hcascade.2.1, ?_, ?_, ?_,
      hcascade.2.2.1, hcascade.2.2.2.1, hcascade.2.2.2.2⟩
    · exact ⟨t1, hcascade.1⟩
    · exact ⟨t1, hcascade.2.2.1⟩
    · exact ⟨y1, hcascade.2.2.2.1⟩
  · right
    obtain ⟨hbne, hrne, htc, hAc, hAa, hAane, hw1a, hphi1a,
      hphi2a, hI4a, hrowa⟩ := htrans
    exact commonNext (Or.inr ⟨hphi1a, Or.inr hw1a⟩)

end RefinedIIIConjugateCoordinateRoutingSource68

end Max11DegreeRoutes
