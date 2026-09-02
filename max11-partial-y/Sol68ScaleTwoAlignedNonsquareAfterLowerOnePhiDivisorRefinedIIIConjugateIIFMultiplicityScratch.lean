import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateIICoordinateScratch

/-! # One further F-multiplicity step on conjugate component II -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

section RefinedIIIConjugateIIFMultiplicityAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalRefinedIIIConjugateIIReducedThirdScalar68
    (A A1 h h2 b2 b3 w w1 d3 phi phi1 : k) : k :=
  (12 * A ^ 2 * b2 * h * w1 + 4 * A ^ 2 * b2 * h2 * w -
      2 * A ^ 2 * b3 * h * w + 6 * A * b2 * h * phi1 +
      2 * A * b2 * h2 * phi + A * b3 * h * phi +
      18 * A * d3 * h * w + 3 * d3 * h * phi) / 2

def terminalRefinedIIIConjugateIII4ThirdScalar68
    (A b2 b3 w w1 d3 phi phi1 : k) : k :=
  6 * A * b2 * w1 + 3 * b2 * phi1 + b3 * phi + 6 * d3 * w

def terminalRefinedIIIConjugateIIFThirdCorrected68
    (A h h2 b2 b3 d3 : k) : k :=
  2 * A * b2 * h2 - A * b3 * h + 3 * d3 * h

/-- The third jet of the reduced lower row after the first two `F` jets have
vanished. -/
theorem terminalLowerZeroReduced_third_componentII_Ftwo_68
    (H A B D phi w : k[X]) (gamma c : k)
    (hc : H.eval c = 0)
    (hB0 : B.eval c = 0) (hB1 : B.derivative.eval c = 0)
    (hD0 : D.eval c = 0) (hD1 : D.derivative.eval c = 0)
    (hD2 : D.derivative.derivative.eval c =
      (1 / 3 : k) * A.eval c * B.derivative.derivative.eval c) :
    (terminalLowerZeroReduced68 H A B D phi w gamma).derivative.derivative.derivative.eval c =
      terminalRefinedIIIConjugateIIReducedThirdScalar68
        (A.eval c) (A.derivative.eval c) (H.derivative.eval c)
        (H.derivative.derivative.eval c) (B.derivative.derivative.eval c)
        (B.derivative.derivative.derivative.eval c) (w.eval c)
        (w.derivative.eval c) (D.derivative.derivative.derivative.eval c)
        (phi.eval c) (phi.derivative.eval c) := by
  dsimp only [terminalLowerZeroReduced68,
    terminalRefinedIIIConjugateIIReducedThirdScalar68]
  simp only [derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly, eval_add,
    eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero,
    hc, hB0, hB1, hD0, hD1, hD2, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  ring

/-- The exact third divided-I4 jet on the same `F₂=0` box. -/
theorem terminalI4_third_componentII_Ftwo_68
    (A B D w phi : k[X]) (c : k)
    (hB0 : B.eval c = 0) (hB1 : B.derivative.eval c = 0)
    (hD0 : D.eval c = 0) (hD1 : D.derivative.eval c = 0)
    (hD2 : D.derivative.derivative.eval c =
      (1 / 3 : k) * A.eval c * B.derivative.derivative.eval c)
    (hjets : terminalI4JetPacket68 B D w phi c) :
    terminalRefinedIIIConjugateIII4ThirdScalar68
      (A.eval c) (B.derivative.derivative.eval c)
      (B.derivative.derivative.derivative.eval c) (w.eval c)
      (w.derivative.eval c) (D.derivative.derivative.derivative.eval c)
      (phi.eval c) (phi.derivative.eval c) = 0 := by
  have hthird := (terminalI4JetPacket68_componentII
    B D w phi c hB0 hD0 hjets).2.2
  dsimp only [terminalRefinedIIIConjugateIII4ThirdScalar68]
  simp only [hB1, hD1, hD2, zero_mul, mul_zero, zero_add, add_zero] at hthird
  linear_combination hthird

/-- Eliminating `phi'` from the two independent third jets leaves exactly
the common `G` face or the corrected third `F` jet. -/
theorem terminalRefinedIII_conjugateII_Fthird_elimination_68
    (A A1 h h2 b2 b3 w w1 d3 phi phi1 : k)
    (hlower : terminalRefinedIIIConjugateIIReducedThirdScalar68
      A A1 h h2 b2 b3 w w1 d3 phi phi1 = 0)
    (hI4 : terminalRefinedIIIConjugateIII4ThirdScalar68
      A b2 b3 w w1 d3 phi phi1 = 0) :
    phi + 2 * A * w = 0 ∨
      terminalRefinedIIIConjugateIIFThirdCorrected68
        A h h2 b2 b3 d3 = 0 := by
  have hprod : (phi + 2 * A * w) *
      terminalRefinedIIIConjugateIIFThirdCorrected68
        A h h2 b2 b3 d3 = 0 := by
    calc
      (phi + 2 * A * w) *
          terminalRefinedIIIConjugateIIFThirdCorrected68
            A h h2 b2 b3 d3 =
        -2 * (A * h *
          terminalRefinedIIIConjugateIII4ThirdScalar68
            A b2 b3 w w1 d3 phi phi1 -
          terminalRefinedIIIConjugateIIReducedThirdScalar68
            A A1 h h2 b2 b3 w w1 d3 phi phi1) := by
              dsimp only [terminalRefinedIIIConjugateIIReducedThirdScalar68,
                terminalRefinedIIIConjugateIII4ThirdScalar68,
                terminalRefinedIIIConjugateIIFThirdCorrected68]
              ring
      _ = 0 := by rw [hI4, hlower]; ring
  exact mul_eq_zero.mp hprod

end RefinedIIIConjugateIIFMultiplicityAlgebra68

section RefinedIIIConjugateIIFMultiplicityPolynomial68

variable {k : Type*} [Field k] [CharZero k]

/-- One finite multiplicity step on the sole remaining `F`-coordinate leaf.
It either rejoins the common scalar component or kills the corrected third
`F` jet. -/
theorem terminalRefinedIII_conjugateII_Fmultiplicity_next_68
    (H A B D w phi : k[X]) (gamma c : k)
    (hc : H.eval c = 0)
    (hB0 : B.eval c = 0) (hB1 : B.derivative.eval c = 0)
    (hD0 : D.eval c = 0)
    (hF1 : A.eval c * B.derivative.eval c - 3 * D.derivative.eval c = 0)
    (hF2 : A.eval c * B.derivative.derivative.eval c -
      3 * D.derivative.derivative.eval c = 0)
    (hjets : terminalI4JetPacket68 B D w phi c)
    (hR : terminalLowerZeroReduced68 H A B D phi w gamma = 0) :
    phi.eval c + 2 * A.eval c * w.eval c = 0 ∨
      terminalRefinedIIIConjugateIIFThirdCorrected68
        (A.eval c) (H.derivative.eval c) (H.derivative.derivative.eval c)
        (B.derivative.derivative.eval c)
        (B.derivative.derivative.derivative.eval c)
        (D.derivative.derivative.derivative.eval c) = 0 := by
  have hD1 : D.derivative.eval c = 0 := by
    rw [hB1, mul_zero, zero_sub] at hF1
    have hthree : (3 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by linear_combination -hF1)).resolve_left hthree
  have hD2 : D.derivative.derivative.eval c =
      (1 / 3 : k) * A.eval c * B.derivative.derivative.eval c := by
    linear_combination (-1 / 3 : k) * hF2
  have hR3 := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval c) hR
  rw [derivative_zero, derivative_zero, derivative_zero, eval_zero,
    terminalLowerZeroReduced_third_componentII_Ftwo_68
      H A B D phi w gamma c hc hB0 hB1 hD0 hD1 hD2] at hR3
  have hI43 := terminalI4_third_componentII_Ftwo_68
    A B D w phi c hB0 hB1 hD0 hD1 hD2 hjets
  exact terminalRefinedIII_conjugateII_Fthird_elimination_68
    (A.eval c) (A.derivative.eval c) (H.derivative.eval c)
      (H.derivative.derivative.eval c) (B.derivative.derivative.eval c)
      (B.derivative.derivative.derivative.eval c) (w.eval c)
      (w.derivative.eval c) (D.derivative.derivative.derivative.eval c)
      (phi.eval c) (phi.derivative.eval c) hR3 hI43

end RefinedIIIConjugateIIFMultiplicityPolynomial68

section RefinedIIIConjugateIIFMultiplicitySource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source wrapper for the finite `F₂` multiplicity step.  The retained
`H²` loaded quotient is carried through but is not differentiated. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateIIFMultiplicityPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (A C0 E0 b1 B D w phi K D1 BW : k[X]) (c : k)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H A C0 S.gamma = H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H A b1 C0 E0 S.gamma S.epsilon =
      H ^ 2 * phi)
    (hc : H.eval c = 0)
    (hB0 : B.eval c = 0) (hB1 : B.derivative.eval c = 0)
    (hD0 : D.eval c = 0)
    (hF1 : A.eval c * B.derivative.eval c - 3 * D.derivative.eval c = 0)
    (hF2 : A.eval c * B.derivative.derivative.eval c -
      3 * D.derivative.derivative.eval c = 0)
    (hmatch : terminalRefinedIIIConjugateMatching68
      H A B D w phi (terminalEDerivativeNumerator68 H E0) K j c)
    (hlower : terminalLowerZeroOne68 H A B C0 D E0
      S.alpha S.gamma S.epsilon S.eta = 0)
    (hrowq : BW * terminalEDerivativeNumerator68 H E0 - D1 * K =
      C j * H ^ 2) :
    (phi.eval c + 2 * A.eval c * w.eval c = 0 ∨
      terminalRefinedIIIConjugateIIFThirdCorrected68
        (A.eval c) (H.derivative.eval c) (H.derivative.derivative.eval c)
        (B.derivative.derivative.eval c)
        (B.derivative.derivative.derivative.eval c)
        (D.derivative.derivative.derivative.eval c) = 0) ∧
      BW * terminalEDerivativeNumerator68 H E0 - D1 * K = C j * H ^ 2 := by
  have hR := S.terminalLowerZeroReduced_source_68 H A C0 E0 b1 B D phi w
    hb hW hPhi hlower
  refine ⟨terminalRefinedIII_conjugateII_Fmultiplicity_next_68
    H A B D w phi S.gamma c hc hB0 hB1 hD0 hF1 hF2
      hmatch.1.2.1 hR, hrowq⟩

end RefinedIIIConjugateIIFMultiplicitySource68

end Max11DegreeRoutes
