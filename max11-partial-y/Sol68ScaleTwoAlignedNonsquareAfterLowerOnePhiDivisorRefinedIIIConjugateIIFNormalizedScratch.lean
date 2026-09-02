import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateIIFMultiplicityScratch

/-! # Polynomial normalization of the corrected third F jet -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

section RefinedIIIConjugateIIFNormalizedAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

def terminalRefinedIIIConjugateIIFNormalizedPacket68
    (H A B D : k[X]) (c : k) : Prop :=
  ∃ B2 F3 : k[X],
    B = (X - C c) ^ 2 * B2 ∧
    A * B - C 3 * D = (X - C c) ^ 3 * F3 ∧
    3 * H.derivative.eval c * F3.eval c =
      (2 * A.eval c * H.derivative.derivative.eval c +
        3 * H.derivative.eval c * A.derivative.eval c) * B2.eval c

theorem second_jet_of_linear_sq_factor_68
    (B B2 : k[X]) (c : k)
    (hB : B = (X - C c) ^ 2 * B2) :
    B.derivative.derivative.eval c = 2 * B2.eval c := by
  have hj := congrArg (fun P : k[X] => P.derivative.derivative.eval c) hB
  simp [pow_two, derivative_mul] at hj
  linear_combination hj

theorem third_jet_of_linear_cube_factor_68
    (F F3 : k[X]) (c : k)
    (hF : F = (X - C c) ^ 3 * F3) :
    F.derivative.derivative.derivative.eval c = 6 * F3.eval c := by
  have hj := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval c) hF
  simp [pow_succ, derivative_mul] at hj
  linear_combination hj

/-- The corrected scalar `L₃` is precisely the leading coefficient relation
between the local double quotient of `B` and triple quotient of `F=AB-3D`. -/
theorem terminalRefinedIII_conjugateII_L3_normalized_68
    (H A B D : k[X]) (c : k)
    (hB0 : B.eval c = 0) (hB1 : B.derivative.eval c = 0)
    (hD0 : D.eval c = 0)
    (hF1 : A.eval c * B.derivative.eval c - 3 * D.derivative.eval c = 0)
    (hF2 : A.eval c * B.derivative.derivative.eval c -
      3 * D.derivative.derivative.eval c = 0)
    (hL3 : terminalRefinedIIIConjugateIIFThirdCorrected68
      (A.eval c) (H.derivative.eval c) (H.derivative.derivative.eval c)
      (B.derivative.derivative.eval c)
      (B.derivative.derivative.derivative.eval c)
      (D.derivative.derivative.derivative.eval c) = 0) :
    terminalRefinedIIIConjugateIIFNormalizedPacket68 H A B D c := by
  let F := A * B - C 3 * D
  have hD1 : D.derivative.eval c = 0 := by
    rw [hB1, mul_zero, zero_sub] at hF1
    have hthree : (3 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by linear_combination -hF1)).resolve_left hthree
  have hF0eval : F.eval c = 0 := by
    dsimp only [F]
    simp [eval_sub, eval_mul, hB0, hD0]
  have hF1eval : F.derivative.eval c = 0 := by
    dsimp only [F]
    simp only [derivative_sub, derivative_mul, derivative_C, zero_mul,
      derivative_ofNat, eval_sub, eval_add, eval_mul, eval_C, eval_zero,
      hB0, hB1, hD1, zero_mul, mul_zero, zero_add, add_zero]
    ring
  have hF2eval : F.derivative.derivative.eval c = 0 := by
    dsimp only [F]
    simp only [derivative_sub, derivative_add, derivative_mul, derivative_C,
      zero_mul, derivative_zero, derivative_ofNat, eval_sub, eval_add,
      eval_mul, eval_C, eval_zero, hB0, hB1, zero_mul, mul_zero, zero_add,
      add_zero]
    linear_combination hF2
  obtain ⟨B2, hB2⟩ := X_sub_C_sq_dvd_of_eval_derivative_zero_68
    B c hB0 hB1
  obtain ⟨F3, hF3⟩ := X_sub_C_cube_dvd_of_three_jets_68
    F c hF0eval hF1eval hF2eval
  have hBjet := second_jet_of_linear_sq_factor_68 B B2 c hB2
  have hFjet := third_jet_of_linear_cube_factor_68 F F3 c hF3
  have hFexpand : F.derivative.derivative.derivative.eval c =
      A.eval c * B.derivative.derivative.derivative.eval c +
        3 * A.derivative.eval c * B.derivative.derivative.eval c -
        3 * D.derivative.derivative.derivative.eval c := by
    dsimp only [F]
    simp only [derivative_sub, derivative_add, derivative_mul, derivative_C,
      zero_mul, derivative_zero, derivative_ofNat, eval_sub, eval_add,
      eval_mul, eval_C, eval_zero, hB0, hB1, zero_mul, mul_zero, zero_add,
      add_zero]
    ring
  have hFjet' :
      A.eval c * B.derivative.derivative.derivative.eval c +
          3 * A.derivative.eval c * B.derivative.derivative.eval c -
          3 * D.derivative.derivative.derivative.eval c =
        6 * F3.eval c := hFexpand.symm.trans hFjet
  refine ⟨B2, F3, hB2, hF3, ?_⟩
  dsimp only [terminalRefinedIIIConjugateIIFThirdCorrected68] at hL3
  linear_combination (-1 / 2 : k) * hL3 -
    (1 / 2 * H.derivative.eval c : k) * hFjet' +
    (1 / 2 * (2 * A.eval c * H.derivative.derivative.eval c +
      3 * H.derivative.eval c * A.derivative.eval c) : k) * hBjet

/-- The verified `G ∨ L₃` split is therefore a common face or an exact
normalized polynomial coefficient packet, not an open-ended row ladder. -/
theorem terminalRefinedIII_conjugateII_Fnormalized_split_68
    (H A B D w phi : k[X]) (c : k)
    (hB0 : B.eval c = 0) (hB1 : B.derivative.eval c = 0)
    (hD0 : D.eval c = 0)
    (hF1 : A.eval c * B.derivative.eval c - 3 * D.derivative.eval c = 0)
    (hF2 : A.eval c * B.derivative.derivative.eval c -
      3 * D.derivative.derivative.eval c = 0)
    (hsplit : phi.eval c + 2 * A.eval c * w.eval c = 0 ∨
      terminalRefinedIIIConjugateIIFThirdCorrected68
        (A.eval c) (H.derivative.eval c) (H.derivative.derivative.eval c)
        (B.derivative.derivative.eval c)
        (B.derivative.derivative.derivative.eval c)
        (D.derivative.derivative.derivative.eval c) = 0) :
    phi.eval c + 2 * A.eval c * w.eval c = 0 ∨
      terminalRefinedIIIConjugateIIFNormalizedPacket68 H A B D c := by
  rcases hsplit with hG | hL3
  · exact Or.inl hG
  · exact Or.inr (terminalRefinedIII_conjugateII_L3_normalized_68
      H A B D c hB0 hB1 hD0 hF1 hF2 hL3)

end RefinedIIIConjugateIIFNormalizedAlgebra68

section RefinedIIIConjugateIIFNormalizedSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source wrapper preserving the loaded `H²` quotient and common branch. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateIIFNormalizedPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (A B D w phi E0 K D1 BW : k[X]) (c : k)
    (hB0 : B.eval c = 0) (hB1 : B.derivative.eval c = 0)
    (hD0 : D.eval c = 0)
    (hF1 : A.eval c * B.derivative.eval c - 3 * D.derivative.eval c = 0)
    (hF2 : A.eval c * B.derivative.derivative.eval c -
      3 * D.derivative.derivative.eval c = 0)
    (hsplit : phi.eval c + 2 * A.eval c * w.eval c = 0 ∨
      terminalRefinedIIIConjugateIIFThirdCorrected68
        (A.eval c) (H.derivative.eval c) (H.derivative.derivative.eval c)
        (B.derivative.derivative.eval c)
        (B.derivative.derivative.derivative.eval c)
        (D.derivative.derivative.derivative.eval c) = 0)
    (hrowq : BW * terminalEDerivativeNumerator68 H E0 - D1 * K =
      C j * H ^ 2) :
    (phi.eval c + 2 * A.eval c * w.eval c = 0 ∨
      terminalRefinedIIIConjugateIIFNormalizedPacket68 H A B D c) ∧
      BW * terminalEDerivativeNumerator68 H E0 - D1 * K = C j * H ^ 2 := by
  exact ⟨terminalRefinedIII_conjugateII_Fnormalized_split_68
    H A B D w phi c hB0 hB1 hD0 hF1 hF2 hsplit, hrowq⟩

end RefinedIIIConjugateIIFNormalizedSource68

end Max11DegreeRoutes
