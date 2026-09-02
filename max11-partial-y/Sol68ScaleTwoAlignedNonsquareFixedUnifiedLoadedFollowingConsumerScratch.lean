import Sol68ScaleTwoAlignedNonsquareFixedUnifiedLoadedNextConsumerScratch
import Fable68ScaleTwoAlignedNonsquareMixedEighthScratch

/-! # Independent square-row continuation of the fixed loaded split -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

section FixedUnifiedLoadedFollowing68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- The earliest independent retained rows on the simultaneous square
child.  This is universal in the quotient witnesses, so it applies to the
literal witnesses carried by the fixed child without selecting new ones. -/
def terminalFixedMixedSquareFollowingFaces68
    (B D w phi1 eDot k1 : k[X]) (j : k) : Prop :=
  ∀ (a : k) (B3 E1 : k[X]),
    H.eval a = 0 → H.derivative.eval a ≠ 0 → j ≠ 0 →
    phi1.eval a ≠ 0 → k1.eval a = 0 →
    B = H * B3 → D = H * E1 →
    B3.eval a = 0 → B3.derivative.eval a = 0 → E1.eval a = 0 →
    B3 * phi1 + C 6 * H * w * E1 = 0 →
    E1 * k1 = H * B3 * w * eDot - C j * H ^ 3 →
    (B3.derivative.derivative.eval a * phi1.eval a +
        12 * H.derivative.eval a * w.eval a *
          E1.derivative.eval a = 0) ∧
    (E1.derivative.derivative.eval a * k1.derivative.eval a +
        E1.derivative.eval a * k1.derivative.derivative.eval a =
      H.derivative.eval a * B3.derivative.derivative.eval a *
          w.eval a * eDot.eval a -
        2 * j * H.derivative.eval a ^ 3) ∧
    ((E1.derivative.eval a = 0 ∧
        B3.derivative.derivative.eval a = 0 ∧
        k1.derivative.eval a ≠ 0 ∧
        E1.derivative.derivative.eval a ≠ 0 ∧
        E1.derivative.derivative.eval a * k1.derivative.eval a +
          2 * j * H.derivative.eval a ^ 3 = 0) ∨
      (k1.derivative.eval a = 0 ∧
        E1.derivative.eval a ≠ 0 ∧
        E1.derivative.eval a *
            (k1.derivative.derivative.eval a * phi1.eval a +
              12 * H.derivative.eval a ^ 2 * w.eval a ^ 2 *
                eDot.eval a) +
          2 * j * H.derivative.eval a ^ 3 * phi1.eval a = 0))

theorem terminalFixedMixedSquareFollowingFaces_68
    (B D w phi1 eDot k1 : k[X]) (j : k) :
    terminalFixedMixedSquareFollowingFaces68 H B D w phi1 eDot k1 j := by
  intro a B3 E1 ha hHa hj hphia hk1a hB hD hB3a hB3da hE1a
    hI4red hE1row
  have hI4face := mixedReducedIFourSecondCoefficient_68 H B3 phi1 w
    E1 a ha hB3a hB3da hE1a hI4red
  have hE1face := mixedEOneRowThirdCoefficient_68 H B3 w eDot E1 k1
    j a ha hB3a hB3da hE1a hk1a hE1row
  have hproduct := mixedEOneRowSecondCoefficient_68 H B3 w eDot E1
    k1 j a ha hB3a hB3da hE1a hk1a hE1row
  exact ⟨hI4face, hE1face,
    mixedEOneRowAllocationSplit_68 hphia hj hHa hI4face hE1face
      hproduct⟩

/-- The previous finite packet plus the first genuinely independent
square-child continuation.  Cube, transverse, and all outer siblings are
retained verbatim. -/
def terminalFixedUnifiedMixedLoadedFollowingConsumed68
    (r t : k[X]) (B D w phi1 k1 : k[X]) : Prop :=
  let eDot := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  terminalFixedUnifiedMixedLoadedNextConsumed68 (p := p) (j := j)
      H r t B D w phi1 k1 ∧
    terminalFixedMixedSquareFollowingFaces68 H
      B D w phi1 eDot k1 j

def terminalFixedUnifiedLoadedFollowingConsumerResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRLoadedConsumed68 H S r t X0 Yd B D w phi1 k1 ∨
    terminalFixedUnifiedMixedLoadedFollowingConsumed68 (p := p) (j := j)
      H r t B D w phi1 k1 ∨
    terminalFixedUnifiedEarlyGeometryResidual68 H S
      r t X0 Yd B D w phi1 k1

theorem terminalFixedUnifiedLoadedFollowing_of_next68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (h : terminalFixedUnifiedLoadedNextConsumerResidual68 H S
      r t X0 Yd B D w phi1 k1) :
    terminalFixedUnifiedLoadedFollowingConsumerResidual68 H S
      r t X0 Yd B D w phi1 k1 := by
  rcases h with hR | hM | hG
  · exact Or.inl hR
  · exact Or.inr (Or.inl ⟨hM,
      terminalFixedMixedSquareFollowingFaces_68 H B D w phi1
        (terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r)) k1 j⟩)
  · exact Or.inr (Or.inr hG)

theorem NonsquareAlignedSourceCurveData68.fixedUnifiedLoadedFollowingPacket
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ r t X0 Yd B D w phi1 k1 : k[X],
      p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
      C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
      B * phi1 + C 6 * H * w * D = 0 ∧
      H * B * w * terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
      H ∣ r * phi1 ∧
      terminalFixedMixedLowerTransport68 H S r t X0 Yd
        B D w phi1 k1 ∧
      terminalFixedUnifiedLoadedFollowingConsumerResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower, hres⟩ :=
    S.fixedUnifiedLoadedNextPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  exact ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower,
    terminalFixedUnifiedLoadedFollowing_of_next68 H S
      r t X0 Yd B D w phi1 k1 hres⟩

end FixedUnifiedLoadedFollowing68

end Max11DegreeRoutes
