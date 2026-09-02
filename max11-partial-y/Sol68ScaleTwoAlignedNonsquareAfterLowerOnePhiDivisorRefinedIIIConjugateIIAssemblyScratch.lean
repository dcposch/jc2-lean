import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateIIFB2I4CommonScratch

/-! # Complete source-facing reduction of conjugate component II -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateIIAssemblyPolynomial68

variable {k : Type*} [Field k] [CharZero k]

/-- Away from the higher-multiplicity child, the twice-cancelled divided-I4
identity routes the remaining loaded factor to the common `G` face. -/
theorem terminalRefinedIII_normalized_loaded_factor_I4_common_68
    (H A B D w phi e K D1 B2 F3 M D2 : k[X]) (c : k)
    (hHM : H = (X - C c) * M)
    (hMc : M.eval c = H.derivative.eval c)
    (hB : B = (X - C c) ^ 2 * B2)
    (hD2 : D1 = (X - C c) * D2)
    (hDcore : C 3 * M * D2 = A * B2 - (X - C c) * F3)
    (hI4 : B * phi + C 6 * H * w * D1 = 0)
    (hB2ne : B2.eval c ≠ 0)
    (hfactor : terminalRefinedIIIConjugateCommonLoadedFactor68
      H A B D w K c) :
    terminalPhiDivisorDegeneracy68 (A.eval c) (B.eval c) (D.eval c)
      (w.eval c) (phi.eval c) (e.eval c) (K.eval c)
      (H.derivative.eval c) := by
  let L : k[X] := X - C c
  have hL : L ≠ 0 := X_sub_C_ne_zero c
  change H = L * M at hHM
  change B = L ^ 2 * B2 at hB
  change D1 = L * D2 at hD2
  have hI4q : B2 * phi + C 6 * M * w * D2 = 0 := by
    rw [hB, hHM, hD2] at hI4
    have hz : L ^ 2 * (B2 * phi + C 6 * M * w * D2) = 0 := by
      linear_combination hI4
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hL)
  have hDroot : 3 * H.derivative.eval c * D2.eval c =
      A.eval c * B2.eval c := by
    have hd := congrArg (fun P : k[X] => P.eval c) hDcore
    simp only [eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul,
      eval_C] at hd
    simpa only [hMc, sub_zero] using hd
  have hI4root : B2.eval c * phi.eval c +
      6 * H.derivative.eval c * w.eval c * D2.eval c = 0 := by
    have hi := congrArg (fun P : k[X] => P.eval c) hI4q
    simp only [eval_add, eval_mul, eval_C, eval_ofNat, eval_zero] at hi
    simpa only [hMc] using hi
  have hprod : B2.eval c *
      (phi.eval c + 2 * A.eval c * w.eval c) = 0 := by
    linear_combination hI4root - 2 * w.eval c * hDroot
  have hG := (mul_eq_zero.mp hprod).resolve_left hB2ne
  have hB0 : B.eval c = 0 := by
    have hb := congrArg (fun P : k[X] => P.eval c) hB
    dsimp only [L] at hb
    simp [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hb
    exact hb
  exact Or.inl ⟨hfactor.1, hG, Or.inr (Or.inl hB0)⟩

end RefinedIIIConjugateIIAssemblyPolynomial68

section RefinedIIIConjugateIIAssemblySource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

def terminalRefinedIIIConjugateIICompleteReduction68
    (H A B D w phi e K D1 BW B2 F3 r : k[X]) (j c : k) : Prop :=
  terminalRefinedIIIConjugateIIFNormalizedPacket68 H A B D c ∧
    ∃ M D2 BW1 : k[X],
      H = (X - C c) * M ∧ M.eval c = H.derivative.eval c ∧
      D1 = (X - C c) * D2 ∧ BW = (X - C c) * BW1 ∧
      C 3 * M * D2 = A * B2 - (X - C c) * F3 ∧
      M * BW1 = B2 * w ∧
      BW1 * e - D2 * K = C j * (X - C c) * M ^ 2 ∧
      (r.eval c = 0 ∨
        terminalPhiDivisorDegeneracy68 (A.eval c) (B.eval c) (D.eval c)
          (w.eval c) (phi.eval c) (e.eval c) (K.eval c)
          (H.derivative.eval c))

/-- Complete local source assembly for conjugate component II.  The old
three-way normalized split is reduced to exactly two reusable residuals:
the existing coordinate locus `r(c)=0`, or the common degeneracy component.
There is no remaining `B2` multiplicity or partial loaded-factor child. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateIICompleteReduction
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 : k[X]) (c : k)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H (cubicANumerator68 t r) C0 S.gamma =
      H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) b1 C0 E0
      S.gamma S.epsilon = H ^ 2 * phi)
    (hX : C 3 * t - r ^ 2 = H * X0)
    (hc : H.eval c = 0) (hh : H.derivative.eval c ≠ 0) (hj : j ≠ 0)
    (hB : B = (X - C c) ^ 2 * B2)
    (hF : cubicANumerator68 t r * B - C 3 * D =
      (X - C c) ^ 3 * F3)
    (hDshape : D = H * D1)
    (hBWshape : B * w = H * BW)
    (hI4 : B * phi + C 6 * H * w * D1 = 0)
    (hrow : BW * terminalEDerivativeNumerator68 H E0 - D1 * K =
      C j * H ^ 2)
    (hnormalized :
      3 * H.derivative.eval c * F3.eval c =
        (2 * (cubicANumerator68 t r).eval c *
            H.derivative.derivative.eval c +
          3 * H.derivative.eval c *
            (cubicANumerator68 t r).derivative.eval c) * B2.eval c) :
    terminalRefinedIIIConjugateIICompleteReduction68 H
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 r j c := by
  obtain ⟨hnorm, M, D2, BW1, hHM, hMc, hD2, hBW1, hDcore,
      hBWcore, hrow1, hsplit⟩ :=
    S.terminalRefinedIIIConjugateIIFLoadedRoutingPacket (H := H)
      t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW hPhi hX
      hc hh hB hF hDshape hBWshape hrow hnormalized
  refine ⟨hnorm, M, D2, BW1, hHM, hMc, hD2, hBW1, hDcore,
    hBWcore, hrow1, ?_⟩
  rcases hsplit with hB2 | hrOrFactor
  · right
    exact (S.terminalRefinedIIIConjugateIIFB2I4CommonPacket (H := H)
      t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW hPhi hX
      hc hh hj hB hF hDshape hBWshape hI4 hrow hnormalized hB2).2
  rcases hrOrFactor with hr | hfactor
  · exact Or.inl hr
  · by_cases hB2zero : B2.eval c = 0
    · right
      exact (S.terminalRefinedIIIConjugateIIFB2I4CommonPacket (H := H)
        t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW hPhi hX
        hc hh hj hB hF hDshape hBWshape hI4 hrow hnormalized hB2zero).2
    · right
      have hcommon := terminalRefinedIII_normalized_loaded_factor_I4_common_68
        H (cubicANumerator68 t r) B D w phi
          (terminalEDerivativeNumerator68 H E0) K D1 B2 F3 M D2 c
        hHM hMc hB hD2 hDcore hI4 hB2zero hfactor
      simpa only using hcommon

end RefinedIIIConjugateIIAssemblySource68

end Max11DegreeRoutes
