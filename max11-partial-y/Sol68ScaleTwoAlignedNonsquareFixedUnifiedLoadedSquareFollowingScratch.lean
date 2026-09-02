import Sol68ScaleTwoAlignedNonsquareFixedUnifiedLoadedFollowingConsumerScratch
import Fable68ScaleTwoAlignedNonsquareMixedNinthScratch

/-! # Ninth-row square continuation in the fixed loaded inventory -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

section FixedUnifiedLoadedSquareFollowing68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- The first independent row after the `E₁' / k₁'` allocation.  The
statement is universal in the fixed quotient witnesses and therefore applies
to both retained `E₂` and `K` subchildren without reselecting either. -/
def terminalFixedMixedSquareNinthFaces68
    (B D w phi1 eDot k1 : k[X]) (j : k) : Prop :=
  ∀ (a : k) (B3 E1 : k[X]),
    H.eval a = 0 → H.derivative.eval a ≠ 0 → j ≠ 0 →
    phi1.eval a ≠ 0 → k1.eval a = 0 →
    B = H * B3 → D = H * E1 →
    B3.eval a = 0 → B3.derivative.eval a = 0 → E1.eval a = 0 →
    B3 * phi1 + C 6 * H * w * E1 = 0 →
    E1 * k1 = H * B3 * w * eDot - C j * H ^ 3 →
    ((E1.derivative.eval a = 0 ∧
        B3.derivative.derivative.eval a = 0 ∧
        k1.derivative.eval a ≠ 0 ∧
        E1.derivative.derivative.eval a ≠ 0 ∧
        E1.derivative.derivative.eval a * k1.derivative.eval a +
          2 * j * H.derivative.eval a ^ 3 = 0) →
      (B3.derivative.derivative.derivative.eval a * phi1.eval a +
          18 * H.derivative.eval a * w.eval a *
            E1.derivative.derivative.eval a = 0) ∧
        B3.derivative.derivative.derivative.eval a * phi1.eval a *
            k1.derivative.eval a =
          36 * j * H.derivative.eval a ^ 4 * w.eval a ∧
        (B3.derivative.derivative.derivative.eval a = 0 ↔
          w.eval a = 0)) ∧
    ((k1.derivative.eval a = 0 ∧ E1.derivative.eval a ≠ 0 ∧
        E1.derivative.eval a *
            (k1.derivative.derivative.eval a * phi1.eval a +
              12 * H.derivative.eval a ^ 2 * w.eval a ^ 2 *
                eDot.eval a) +
          2 * j * H.derivative.eval a ^ 3 * phi1.eval a = 0) →
      B3.derivative.derivative.derivative.eval a * phi1.eval a +
          3 * B3.derivative.derivative.eval a *
            phi1.derivative.eval a +
          36 * H.derivative.eval a * w.derivative.eval a *
            E1.derivative.eval a +
          18 * H.derivative.eval a * w.eval a *
            E1.derivative.derivative.eval a +
          18 * H.derivative.derivative.eval a * w.eval a *
            E1.derivative.eval a = 0)

theorem terminalFixedMixedSquareNinthFaces_68
    (B D w phi1 eDot k1 : k[X]) (j : k) :
    terminalFixedMixedSquareNinthFaces68 H B D w phi1 eDot k1 j := by
  intro a B3 E1 ha hHa hj hphia hk1a hB hD hB3a hB3da hE1a
    hI4red hE1row
  constructor
  · rintro ⟨hE1da, hB3dda, hk1da, hE1dda, hpin⟩
    have htie := mixedReducedIFourThirdCoefficientDeepZero_68 H B3
      phi1 w E1 a ha hB3a hB3da hB3dda hE1a hE1da hI4red
    have helim := mixedEOneBranchPinElimination_68 hphia hj hHa hk1da
      hpin htie
    exact ⟨htie, helim.1, helim.2⟩
  · rintro ⟨_hk1da, _hE1da, _haffine⟩
    exact mixedReducedIFourThirdCoefficient_68 H B3 phi1 w E1 a ha
      hB3a hB3da hE1a hI4red

def terminalFixedUnifiedMixedLoadedSquareFollowing68
    (r t : k[X]) (B D w phi1 k1 : k[X]) : Prop :=
  let eDot := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  terminalFixedUnifiedMixedLoadedFollowingConsumed68 (p := p) (j := j)
      H r t B D w phi1 k1 ∧
    terminalFixedMixedSquareNinthFaces68 H B D w phi1 eDot k1 j

def terminalFixedUnifiedLoadedSquareFollowingResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRLoadedConsumed68 H S r t X0 Yd B D w phi1 k1 ∨
    terminalFixedUnifiedMixedLoadedSquareFollowing68 (p := p) (j := j)
      H r t B D w phi1 k1 ∨
    terminalFixedUnifiedEarlyGeometryResidual68 H S
      r t X0 Yd B D w phi1 k1

theorem terminalFixedUnifiedLoadedSquareFollowing_of_following68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (h : terminalFixedUnifiedLoadedFollowingConsumerResidual68 H S
      r t X0 Yd B D w phi1 k1) :
    terminalFixedUnifiedLoadedSquareFollowingResidual68 H S
      r t X0 Yd B D w phi1 k1 := by
  rcases h with hR | hM | hG
  · exact Or.inl hR
  · exact Or.inr (Or.inl ⟨hM,
      terminalFixedMixedSquareNinthFaces_68 H B D w phi1
        (terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r)) k1 j⟩)
  · exact Or.inr (Or.inr hG)

theorem NonsquareAlignedSourceCurveData68.fixedUnifiedLoadedSquareFollowingPacket
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
      terminalFixedUnifiedLoadedSquareFollowingResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower, hres⟩ :=
    S.fixedUnifiedLoadedFollowingPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  exact ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower,
    terminalFixedUnifiedLoadedSquareFollowing_of_following68 H S
      r t X0 Yd B D w phi1 k1 hres⟩

end FixedUnifiedLoadedSquareFollowing68

end Max11DegreeRoutes
