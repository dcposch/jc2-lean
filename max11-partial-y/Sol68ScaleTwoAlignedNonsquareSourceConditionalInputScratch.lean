import Sol68ScaleTwoAlignedNonsquareSourceSameWitnessScratch

/-! # Conditional-coordinate final source input

The common/II inventory needs coordinate data only on its `r(c)=0` limb.
This interface records that exact implication and converts it to the existing
stable assembly only after the inventory has selected that limb.
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

section ConditionalFinalStableSourceInput68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- Exact replacement for `NonsquareAlignedFinalStableSourceInputs68`:
coordinate data is required only when the common/II inventory actually lands
on its coordinate limb. -/
structure NonsquareAlignedFinalStableConditionalSourceInputs68
    (S : NonsquareAlignedSourceCurveData68 H p q j) where
  t : k[X]
  r : k[X]
  X0 : k[X]
  Yd : k[X]
  b1 : k[X]
  B : k[X]
  D : k[X]
  w : k[X]
  phi : k[X]
  K : k[X]
  D1 : k[X]
  BW : k[X]
  B2 : k[X]
  F3 : k[X]
  phi1 : k[X]
  k1 : k[X]
  a : k
  c : k
  ha : H.eval a = 0
  hc : H.eval c = 0
  hac : a ≠ c
  hwa : w.eval a = 0
  hphia : phi.eval a = 0
  hDa : D.eval a = 0
  hKa : K.eval a = 0
  hb : b1 = H * B
  hW : terminalScaledW68 H (cubicANumerator68 t r)
      (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) S.gamma = H ^ 2 * w
  hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) b1
      (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r) S.gamma S.epsilon = H ^ 2 * phi
  hp4 : p.coeff 4 = H * t
  hX : C 3 * t - r ^ 2 = H * X0
  hY : C 27 * p.coeff 3 - r ^ 3 = H * Yd
  hB : B = (X - C c) ^ 2 * B2
  hF : cubicANumerator68 t r * B - C 3 * D = (X - C c) ^ 3 * F3
  hDshape : D = H * D1
  hBWshape : B * w = H * BW
  hI4q : B * phi + C 6 * H * w * D1 = 0
  hrowq : BW * terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r) - D1 * K = C j * H ^ 2
  hI4 : B * phi + C 6 * w * D = 0
  hrow : B * w * terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r) - D * K = C j * H ^ 3
  hnormalized :
    3 * H.derivative.eval c * F3.eval c =
      (2 * (cubicANumerator68 t r).eval c *
          H.derivative.derivative.eval c +
        3 * H.derivative.eval c *
          (cubicANumerator68 t r).derivative.eval c) * B2.eval c
  hwitness : terminalRefinedIIIConjugateRDivisorPreDivisionWitnesses68
    H phi K phi1 k1
  hlower : terminalLowerZeroCleared68 H (cubicANumerator68 t r) (H * B)
    (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) (H * D)
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r) S.alpha S.gamma S.epsilon S.eta = 0
  hinventory : terminalRefinedIIIConjugateCommonIIResidual68 H
    (cubicANumerator68 t r) B D w phi
    (terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r)) K r j a c
  hcoordinate : r.eval c = 0 →
    terminalRefinedIIIConjugateCoordinateResidual68 H t r X0 B D w phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) K a c (6 * j * H.derivative.eval a ^ 3)

/-- Conditional coordinate provenance is sufficient for the final stable
residual.  Common and component-III inventory limbs never manufacture or
consume coordinate data. -/
theorem NonsquareAlignedSourceCurveData68.finalStableSourceResidual_of_conditional_inputs
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (I : NonsquareAlignedFinalStableConditionalSourceInputs68 H S) :
    terminalRefinedIIIConjugateFinalStableSourceResidual68 H I.r I.t I.X0
      I.Yd (p.coeff 3) (p.coeff 4) (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (cubicANumerator68 I.t I.r) I.B I.D I.w I.phi
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) I.t I.r)) I.K I.phi1 I.k1
      S.alpha S.gamma S.epsilon S.eta j I.a I.c := by
  rcases I.hinventory with hrc | hcommon | hIII
  · let J : NonsquareAlignedFinalStableSourceInputs68 H S :=
      { t := I.t
        r := I.r
        X0 := I.X0
        Yd := I.Yd
        b1 := I.b1
        B := I.B
        D := I.D
        w := I.w
        phi := I.phi
        K := I.K
        D1 := I.D1
        BW := I.BW
        B2 := I.B2
        F3 := I.F3
        phi1 := I.phi1
        k1 := I.k1
        a := I.a
        c := I.c
        ha := I.ha
        hc := I.hc
        hac := I.hac
        hwa := I.hwa
        hphia := I.hphia
        hDa := I.hDa
        hKa := I.hKa
        hb := I.hb
        hW := I.hW
        hPhi := I.hPhi
        hp4 := I.hp4
        hX := I.hX
        hY := I.hY
        hB := I.hB
        hF := I.hF
        hDshape := I.hDshape
        hBWshape := I.hBWshape
        hI4q := I.hI4q
        hrowq := I.hrowq
        hI4 := I.hI4
        hrow := I.hrow
        hnormalized := I.hnormalized
        hwitness := I.hwitness
        hlower := I.hlower
        hinventory := Or.inl hrc
        hcoordinate := I.hcoordinate hrc }
    exact S.finalStableSourceResidual_of_inputs (H := H) hdeg hj J
  · exact Or.inr (Or.inl hcommon)
  · exact Or.inr (Or.inr (Or.inl hIII))

end ConditionalFinalStableSourceInput68

end Max11DegreeRoutes
