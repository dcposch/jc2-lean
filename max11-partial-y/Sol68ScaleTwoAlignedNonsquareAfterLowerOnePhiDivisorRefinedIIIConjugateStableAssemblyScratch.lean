import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateRDivisorLowerZeroAssemblyScratch
import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateCommonIIAssemblyScratch

/-! # Stable common/II/coordinate parent interface -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section RefinedIIIConjugateStableAssemblyAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Stable inventory after the component-II completion and coordinate
routing.  The coordinate R-divisor limb is handed to the finite lower-zero
allocation; the only remaining conjugate limbs are CommonTransverseNext and
the two component-III `D/K` allocations. -/
def terminalRefinedIIIConjugateStableResidual68
    (H r t X0 Yd p3 p4 p0 p1 p2 A B D w phi e K phi1 k1 : k[X])
    (alpha gamma epsilon eta j a c : k) : Prop :=
  (∃ s t1 y1 A1 c2 e3 psi m : k[X],
      terminalRefinedIIIConjugateRDivisorLocalContinuation68
        H r t X0 Yd p3 p4 s t1 y1 p0 p1 p2 B D w phi e K phi1 k1 j ∧
      terminalRefinedIIIRDivisorLowerZeroAllocation68
        H A1 B c2 D e3 psi m phi1 k1 w alpha gamma epsilon eta j) ∨
    terminalRefinedIIIConjugateCommonTransverseNext68
      H A B D w phi e K j a c ∨
    (w.eval c = 0 ∧ phi.eval c = 0 ∧ H ∣ w ∧ H ∣ phi ∧
      ((D.eval c = 0 ∧ H ∣ D) ∨ (K.eval c = 0 ∧ H ∣ K)))

end RefinedIIIConjugateStableAssemblyAlgebra68

section RefinedIIIConjugateStableAssemblySource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing merger of component-II completion, common-transverse
refinement, coordinate routing, and the canonical local lower-zero consumer.
All data refer to the same quotient witnesses; no existential packet is
reselected. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateStableAssembly
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
    terminalRefinedIIIConjugateStableResidual68 H r t X0 Yd
      (p.coeff 3) (p.coeff 4) (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K phi1 k1
      S.alpha S.gamma S.epsilon S.eta j a c := by
  subst C0
  subst E0
  rcases hinventory with hrc | hcommon | hIII
  · have hrouted := S.terminalRefinedIIIConjugateCoordinateRouting (H := H)
      t r X0 Yd
      (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r)
      b1 B D w phi K D1 BW B2 F3 a c
      hdeg ha hc hac hwa hphia hDa hKa hb hW hPhi hp4 hX hY hB hF
      hDshape hBWshape hI4q hrowq hI4 hrow hnormalized hj hcoordinate
    rcases hrouted with hR | hnext
    · left
      obtain ⟨s, t1, y1, hs, ht, h3, _htdvd, _hp4dvd, _hp3dvd,
        hp4two, hp3one, h27⟩ := hR
      have hcontinuation :=
        terminalRefinedIII_conjugate_rDivisor_localContinuation_68
          H r t X0 Yd (p.coeff 3) (p.coeff 4) s t1 y1
          (p.coeff 0) (p.coeff 1) (p.coeff 2) B D w phi K phi1 k1 j
          hs ht hp4two hp3one h3 h27 hwitness hI4
          (by simpa only using hrow)
      have hPhiPre : terminalScaledPhi68 H (cubicANumerator68 t r) (H * B)
          (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) S.gamma S.epsilon = H * phi1 := by
        rcases hwitness with ⟨hphi1, _⟩
        rw [hb] at hPhi
        rw [hphi1]
        simpa only [pow_two, mul_assoc] using hPhi
      obtain ⟨A1, c2, e3, psi, m, hallocation⟩ :=
        S.terminalRefinedIIIRDivisorLowerZeroConsume (H := H)
          r t X0 Yd s t1 y1 B D w phi K phi1 k1 hdeg hj
          hcontinuation
          hW
          hPhiPre hlower
      exact ⟨s, t1, y1, A1, c2, e3, psi, m,
        hcontinuation, hallocation⟩
    · exact Or.inr (Or.inl hnext)
  · exact Or.inr (Or.inl hcommon)
  · exact Or.inr (Or.inr hIII)

end RefinedIIIConjugateStableAssemblySource68

end Max11DegreeRoutes
