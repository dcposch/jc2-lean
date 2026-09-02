import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateRDivisorBridgeScratch
import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIScratch

/-! # Canonical source witnesses for the conjugate R-divisor limb

The refined-III source packet still owns the original quotients `phi1,k1`
and their canonical divided coordinates `phi,K`.  This file keeps those
witnesses together and sends every subsequent `H ∣ r` decision directly
to the verified local R-divisor continuation. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateCanonicalRDivisorBridgeSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Canonical source packet in which the post-`phi` coordinates retain their
pre-division witnesses.  Consequently `H ∣ r` needs no new quotient
assumption: it enters the exact local R-divisor continuation immediately. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIICanonicalRDivisorBridge
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t X0 Yd phi1 k1 B D w : k[X]),
      p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X0 ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      (H ∣ phi1 →
        ∃ phi K : k[X],
          terminalRefinedIIIConjugateRDivisorPreDivisionWitnesses68
            H phi K phi1 k1 ∧
          B * phi + (6 : k[X]) * w * D = 0 ∧
          B * w * terminalEDerivativeNumerator68 H
              (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
                (p.coeff 3) t r) - D * K = C j * H ^ 3 ∧
          (H ∣ r →
            ∃ s t1 y1 : k[X],
              terminalRefinedIIIConjugateRDivisorLocalContinuation68
                H r t X0 Yd (p.coeff 3) (p.coeff 4) s t1 y1
                (p.coeff 0) (p.coeff 1) (p.coeff 2) B D w phi
                (terminalEDerivativeNumerator68 H
                  (cubicENumerator68 H (p.coeff 0) (p.coeff 1)
                    (p.coeff 2) (p.coeff 3) t r))
                K phi1 k1 j)) := by
  obtain ⟨r, t, X0, Yd, phi1, k1, B, D, w, hp4, hX, hY, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorRefinedIIIPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X0, Yd, phi1, k1, B, D, w, hp4, hX, hY, ?_⟩
  intro hphi
  obtain ⟨phi, K, hphi1, hk1, hI4, hrow, _⟩ := hbranch hphi
  dsimp only at hrow
  refine ⟨phi, K, ⟨hphi1, hk1⟩, hI4, hrow, ?_⟩
  rintro ⟨s, hs⟩
  let t1 : k[X] := C (1 / 3 : k) * (H * s ^ 2 + X0)
  let y1 : k[X] := C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)
  have hcascade := rDivisor_coordinate_cascade_68 H r t X0 Yd
    (p.coeff 3) (p.coeff 4) s hs hp4 hX hY
  refine ⟨s, t1, y1, ?_⟩
  exact terminalRefinedIII_conjugate_rDivisor_localContinuation_68
    H r t X0 Yd (p.coeff 3) (p.coeff 4) s t1 y1
    (p.coeff 0) (p.coeff 1) (p.coeff 2) B D w phi K phi1 k1 j
    hs hcascade.1 hcascade.2.2.1 hcascade.2.2.2.1
    hcascade.2.1 hcascade.2.2.2.2 ⟨hphi1, hk1⟩ hI4 hrow

end RefinedIIIConjugateCanonicalRDivisorBridgeSource68

end Max11DegreeRoutes
