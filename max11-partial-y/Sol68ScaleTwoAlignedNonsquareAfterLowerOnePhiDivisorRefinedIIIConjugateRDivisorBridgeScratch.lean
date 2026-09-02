import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateCoordinateRoutingScratch
import Fable68ScaleTwoAlignedNonsquareRDivisorLowerZeroScratch

/-! # Local R-divisor continuation after the conjugate coordinate routing

The post-`phi` chart retains the divided identities

`B*phi + 6*w*D = 0` and `B*w*e - D*K = j*H^3`.

To feed the earlier lower-zero chart one must also identify its two
pre-division coordinates by `phi1 = H*phi` and `k1 = H*K`.  Those
identifications are not fields of the present source packet, so this file
records them as explicit witnesses and proves the exact reconstruction and
the ensuing R-divisor cofactor.  No rootwise or degree hypothesis is used. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateRDivisorBridgeAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The two exact quotient identifications missing from the post-`phi`
chart.  Keeping them as a named packet prevents silently identifying
unrelated existential quotients chosen by two source wrappers. -/
def terminalRefinedIIIConjugateRDivisorPreDivisionWitnesses68
    (H phi K phi1 k1 : k[X]) : Prop :=
  phi1 = H * phi ∧ k1 = H * K

/-- Exact local continuation packet produced from the coordinate cascade
and the two pre-division witnesses. -/
def terminalRefinedIIIConjugateRDivisorLocalContinuation68
    (H r t X0 Yd p3 p4 s t1 y1 p0 p1 p2 B D w phi e K phi1 k1 : k[X])
    (j : k) : Prop :=
  r = H * s ∧ t = H * t1 ∧ p4 = H ^ 2 * t1 ∧ p3 = H * y1 ∧
    (3 : k[X]) * t1 = H * s ^ 2 + X0 ∧
    (27 : k[X]) * y1 = H ^ 2 * s ^ 3 + Yd ∧
    ∃ A1 C1 e3 m : k[X],
      A1 = t1 - C (5 / 12 : k) * H * s ^ 2 ∧
      C1 = p2 - C (1 / 2 : k) * H * y1 * s +
        C (1 / 6 : k) * H ^ 2 * t1 * s ^ 2 -
        C (5 / 144 : k) * H ^ 3 * s ^ 4 ∧
      e3 = p0 - C (1 / 6 : k) * p1 * s +
        C (1 / 36 : k) * p2 * s ^ 2 -
        C (1 / 216 : k) * H * y1 * s ^ 3 +
        C (1 / 1296 : k) * H ^ 2 * t1 * s ^ 4 -
        C (5 / 46656 : k) * H ^ 3 * s ^ 6 ∧
      cubicANumerator68 t r = H * A1 ∧
      cubicCNumerator68 H p2 p3 t r = H * C1 ∧
      cubicENumerator68 H p0 p1 p2 p3 t r = H ^ 3 * e3 ∧
      e = H ^ 4 * e3.derivative ∧
      terminalRefinedIIIConjugateRDivisorPreDivisionWitnesses68
        H phi K phi1 k1 ∧
      B * phi1 + (6 : k[X]) * H * w * D = 0 ∧
      H * B * w * e - D * k1 = C j * H ^ 4 ∧
      m = H * B * w * e3.derivative - C j ∧
      D * k1 = H ^ 4 * m

/-- Multiplying the two divided rows by `H` reconstructs their exact
pre-division forms. -/
theorem terminalRefinedIII_rDivisor_preDivisionRows_68
    (H B D w phi e K phi1 k1 : k[X]) (j : k)
    (hwitness : terminalRefinedIIIConjugateRDivisorPreDivisionWitnesses68
      H phi K phi1 k1)
    (hI4 : B * phi + (6 : k[X]) * w * D = 0)
    (hrow : B * w * e - D * K = C j * H ^ 3) :
    B * phi1 + (6 : k[X]) * H * w * D = 0 ∧
      H * B * w * e - D * k1 = C j * H ^ 4 := by
  rcases hwitness with ⟨hphi1, hk1⟩
  constructor
  · rw [hphi1]
    linear_combination H * hI4
  · rw [hk1]
    linear_combination H * hrow

/-- The exact coordinate cascade, together with the two missing quotient
witnesses, reaches the already verified fourth-power R-divisor cofactor.
This is the smallest local input accepted by the pre-division algebra; the
larger source lower-zero wrapper currently does not expose such a local API. -/
theorem terminalRefinedIII_conjugate_rDivisor_localContinuation_68
    (H r t X0 Yd p3 p4 s t1 y1 p0 p1 p2 B D w phi K phi1 k1 : k[X])
    (j : k)
    (hr : r = H * s) (ht : t = H * t1)
    (hp4 : p4 = H ^ 2 * t1) (hp3 : p3 = H * y1)
    (h3 : (3 : k[X]) * t1 = H * s ^ 2 + X0)
    (h27 : (27 : k[X]) * y1 = H ^ 2 * s ^ 3 + Yd)
    (hwitness : terminalRefinedIIIConjugateRDivisorPreDivisionWitnesses68
      H phi K phi1 k1)
    (hI4 : B * phi + (6 : k[X]) * w * D = 0)
    (hrow : B * w * terminalEDerivativeNumerator68 H
        (cubicENumerator68 H p0 p1 p2 p3 t r) - D * K =
      C j * H ^ 3) :
    terminalRefinedIIIConjugateRDivisorLocalContinuation68
      H r t X0 Yd p3 p4 s t1 y1 p0 p1 p2 B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H p0 p1 p2 p3 t r))
      K phi1 k1 j := by
  have hnum := rDivisor_numerator_cascade_68 H s t1 y1 p0 p1 p2
  let A1 : k[X] := t1 - C (5 / 12 : k) * H * s ^ 2
  let C1 : k[X] := p2 - C (1 / 2 : k) * H * y1 * s +
    C (1 / 6 : k) * H ^ 2 * t1 * s ^ 2 -
    C (5 / 144 : k) * H ^ 3 * s ^ 4
  let e3 : k[X] := p0 - C (1 / 6 : k) * p1 * s +
    C (1 / 36 : k) * p2 * s ^ 2 -
    C (1 / 216 : k) * H * y1 * s ^ 3 +
    C (1 / 1296 : k) * H ^ 2 * t1 * s ^ 4 -
    C (5 / 46656 : k) * H ^ 3 * s ^ 6
  let e := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H p0 p1 p2 p3 t r)
  let m : k[X] := H * B * w * e3.derivative - C j
  have hA : cubicANumerator68 t r = H * A1 := by
    rw [ht, hr]
    exact hnum.1
  have hC : cubicCNumerator68 H p2 p3 t r = H * C1 := by
    rw [hp3, ht, hr]
    exact hnum.2.1
  have hE : cubicENumerator68 H p0 p1 p2 p3 t r = H ^ 3 * e3 := by
    rw [hp3, ht, hr]
    exact hnum.2.2
  have he : e = H ^ 4 * e3.derivative := by
    dsimp only [e]
    rw [hE]
    exact rDivisor_derivative_collapse_68 H e3
  have hrows : B * phi1 + (6 : k[X]) * H * w * D = 0 ∧
      H * B * w * e - D * k1 = C j * H ^ 4 := by
    apply terminalRefinedIII_rDivisor_preDivisionRows_68
      H B D w phi e K phi1 k1 j hwitness hI4
    simpa only [e] using hrow
  have hdk : D * k1 = H ^ 4 * m := by
    dsimp only [m]
    apply rDivisor_row_cofactor_68 H B w D k1 e3 j
    rw [← he]
    exact hrows.2
  exact ⟨hr, ht, hp4, hp3, h3, h27, A1, C1, e3, m,
    rfl, rfl, rfl, hA, hC, hE, he, hwitness, hrows.1, hrows.2,
    rfl, hdk⟩

end RefinedIIIConjugateRDivisorBridgeAlgebra68

section RefinedIIIConjugateRDivisorBridgeSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing local bridge.  Its only extra assumptions are the two
quotient identifications absent from the present post-`phi` source API. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateRDivisorLocalBridge
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd s t1 y1 B D w phi K phi1 k1 : k[X])
    (hr : r = H * s) (ht : t = H * t1)
    (hp4 : p.coeff 4 = H ^ 2 * t1)
    (hp3 : p.coeff 3 = H * y1)
    (h3 : (3 : k[X]) * t1 = H * s ^ 2 + X0)
    (h27 : (27 : k[X]) * y1 = H ^ 2 * s ^ 3 + Yd)
    (hwitness : terminalRefinedIIIConjugateRDivisorPreDivisionWitnesses68
      H phi K phi1 k1)
    (hI4 : B * phi + (6 : k[X]) * w * D = 0)
    (hrow : B * w * terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) - D * K = C j * H ^ 3) :
    terminalRefinedIIIConjugateRDivisorLocalContinuation68
      H r t X0 Yd (p.coeff 3) (p.coeff 4) s t1 y1
      (p.coeff 0) (p.coeff 1) (p.coeff 2) B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r))
      K phi1 k1 j := by
  exact terminalRefinedIII_conjugate_rDivisor_localContinuation_68
    H r t X0 Yd (p.coeff 3) (p.coeff 4) s t1 y1
    (p.coeff 0) (p.coeff 1) (p.coeff 2) B D w phi K phi1 k1 j
    hr ht hp4 hp3 h3 h27 hwitness hI4 hrow

end RefinedIIIConjugateRDivisorBridgeSource68

end Max11DegreeRoutes
