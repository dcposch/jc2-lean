import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateIIFNormalizedScratch

/-! # The H² loaded quotient on the normalized conjugate F packet -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateIIFNormalizedLoadedAlgebra68

variable {k : Type*} [Field k] [CharZero k]

theorem terminalRefinedIII_normalized_loaded_scalar_split_68
    (h A b2 w bw d2 e K : k) (hh : h ≠ 0)
    (hBW : h * bw = b2 * w)
    (hD : 3 * h * d2 = A * b2)
    (hload : bw * e - d2 * K = 0)
    (he : e = -(1 / 9 : k) * h * A ^ 3) :
    b2 = 0 ∨ A = 0 ∨ h * A ^ 2 * w + 3 * K = 0 := by
  have heq : e + (1 / 9 : k) * h * A ^ 3 = 0 := by linear_combination he
  have hfac : b2 * A * (h * A ^ 2 * w + 3 * K) = 0 := by
    linear_combination -9 * h * hload + 9 * e * hBW - 3 * K * hD +
      9 * b2 * w * heq
  rcases mul_eq_zero.mp hfac with hbA | hloadFace
  · rcases mul_eq_zero.mp hbA with hb | hA
    · exact Or.inl hb
    · exact Or.inr (Or.inl hA)
  · exact Or.inr (Or.inr hloadFace)

end RefinedIIIConjugateIIFNormalizedLoadedAlgebra68

section RefinedIIIConjugateIIFNormalizedLoadedPolynomial68

variable {k : Type*} [Field k] [CharZero k]

/-- The local linear factor of `H` at its specified simple root. -/
theorem simpleRoot_linear_factor_packet_68
    (H : k[X]) (c : k) (hc : H.eval c = 0)
    (hh : H.derivative.eval c ≠ 0) :
    ∃ M : k[X], H = (X - C c) * M ∧ M.eval c = H.derivative.eval c := by
  have hlin : X - C c ∣ H := by
    rw [dvd_iff_isRoot]
    exact hc
  obtain ⟨M, hM⟩ := hlin
  refine ⟨M, hM, ?_⟩
  have hd := congrArg (fun P : k[X] => P.derivative.eval c) hM
  simp [derivative_mul] at hd
  exact hd.symm

/-- Substitution of the actual local quotients into the preserved `H²`
loaded identity.  Both quotient factors acquire one linear factor, and their
root values yield the exact three-way scalar split. -/
theorem terminalRefinedIII_normalized_loaded_packet_68
    (H A B D w e K D1 BW B2 F3 : k[X]) (j c : k)
    (hc : H.eval c = 0) (hh : H.derivative.eval c ≠ 0)
    (hB : B = (X - C c) ^ 2 * B2)
    (hF : A * B - C 3 * D = (X - C c) ^ 3 * F3)
    (hDshape : D = H * D1)
    (hBWshape : B * w = H * BW)
    (hrow : BW * e - D1 * K = C j * H ^ 2)
    (he : e.eval c = -(1 / 9 : k) * H.derivative.eval c * A.eval c ^ 3) :
    ∃ M D2 BW1 : k[X],
      H = (X - C c) * M ∧ M.eval c = H.derivative.eval c ∧
      D1 = (X - C c) * D2 ∧ BW = (X - C c) * BW1 ∧
      C 3 * M * D2 = A * B2 - (X - C c) * F3 ∧
      M * BW1 = B2 * w ∧
      BW1 * e - D2 * K = C j * (X - C c) * M ^ 2 ∧
      (B2.eval c = 0 ∨ A.eval c = 0 ∨
        H.derivative.eval c * A.eval c ^ 2 * w.eval c +
          3 * K.eval c = 0) := by
  let L : k[X] := X - C c
  have hL : L ≠ 0 := X_sub_C_ne_zero c
  obtain ⟨M, hHM, hMc⟩ := simpleRoot_linear_factor_packet_68 H c hc hh
  change B = L ^ 2 * B2 at hB
  change A * B - C 3 * D = L ^ 3 * F3 at hF
  change H = L * M at hHM
  have hDcore : C 3 * M * D1 = L * (A * B2 - L * F3) := by
    have hf := hF
    rw [hB, hDshape, hHM] at hf
    have hz : L * (C 3 * M * D1 - L * (A * B2 - L * F3)) = 0 := by
      linear_combination -hf
    have hcanc := (mul_eq_zero.mp hz).resolve_left hL
    linear_combination hcanc
  have hD1c : D1.eval c = 0 := by
    have hd := congrArg (fun P : k[X] => P.eval c) hDcore
    dsimp only [L] at hd
    simp only [eval_mul, eval_sub, eval_X, eval_C, eval_C, sub_self,
      zero_mul, mul_zero] at hd
    have hcoef : (3 : k) * M.eval c ≠ 0 := mul_ne_zero (by norm_num) (by simpa [hMc])
    exact (mul_eq_zero.mp hd).resolve_left hcoef
  have hLD1 : L ∣ D1 := by
    rw [dvd_iff_isRoot]
    exact hD1c
  obtain ⟨D2, hD2⟩ := hLD1
  have hDcore2 : C 3 * M * D2 = A * B2 - L * F3 := by
    rw [hD2] at hDcore
    have hz : L * (C 3 * M * D2 - (A * B2 - L * F3)) = 0 := by
      linear_combination hDcore
    have hcanc := (mul_eq_zero.mp hz).resolve_left hL
    linear_combination hcanc
  have hBWcore : L * B2 * w = M * BW := by
    have hb := hBWshape
    rw [hB, hHM] at hb
    have hz : L * (L * B2 * w - M * BW) = 0 := by
      linear_combination hb
    have hcanc := (mul_eq_zero.mp hz).resolve_left hL
    linear_combination hcanc
  have hBWc : BW.eval c = 0 := by
    have hb := congrArg (fun P : k[X] => P.eval c) hBWcore
    dsimp only [L] at hb
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at hb
    exact (mul_eq_zero.mp hb.symm).resolve_left (by simpa [hMc] using hh)
  have hLBW : L ∣ BW := by
    rw [dvd_iff_isRoot]
    exact hBWc
  obtain ⟨BW1, hBW1⟩ := hLBW
  have hBWcore2 : M * BW1 = B2 * w := by
    rw [hBW1] at hBWcore
    have heq : L * (B2 * w) = L * (M * BW1) := by
      calc
        L * (B2 * w) = L * B2 * w := by ring
        _ = M * (L * BW1) := hBWcore
        _ = L * (M * BW1) := by ring
    exact (mul_left_cancel₀ hL heq).symm
  have hrow1 : BW1 * e - D2 * K = C j * L * M ^ 2 := by
    rw [hBW1, hD2, hHM] at hrow
    have hz : L * (BW1 * e - D2 * K - C j * L * M ^ 2) = 0 := by
      linear_combination hrow
    have hcanc := (mul_eq_zero.mp hz).resolve_left hL
    linear_combination hcanc
  have hDroot : 3 * H.derivative.eval c * D2.eval c =
      A.eval c * B2.eval c := by
    have hd := congrArg (fun P : k[X] => P.eval c) hDcore2
    dsimp only [L] at hd
    simp only [eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul,
      eval_C] at hd
    simpa [hMc] using hd
  have hBWroot : H.derivative.eval c * BW1.eval c =
      B2.eval c * w.eval c := by
    have hb := congrArg (fun P : k[X] => P.eval c) hBWcore2
    simpa [hMc] using hb
  have hloadroot : BW1.eval c * e.eval c - D2.eval c * K.eval c = 0 := by
    have hr := congrArg (fun P : k[X] => P.eval c) hrow1
    dsimp only [L] at hr
    simp only [eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul,
      eval_C] at hr
    simpa using hr
  have hsplit := terminalRefinedIII_normalized_loaded_scalar_split_68
    (H.derivative.eval c) (A.eval c) (B2.eval c) (w.eval c)
      (BW1.eval c) (D2.eval c) (e.eval c) (K.eval c) hh
      hBWroot hDroot hloadroot he
  exact ⟨M, D2, BW1, hHM, hMc, hD2, hBW1, hDcore2,
    hBWcore2, hrow1, hsplit⟩

end RefinedIIIConjugateIIFNormalizedLoadedPolynomial68

section RefinedIIIConjugateIIFNormalizedLoadedSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Actual-source specialization, including the canonical root value of the
`E` derivative numerator.  The normalized coefficient relation is retained
alongside the new loaded factor split. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateIIFNormalizedLoadedPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (A C0 E0 b1 B D w phi K D1 BW B2 F3 : k[X]) (c : k)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H A C0 S.gamma = H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H A b1 C0 E0 S.gamma S.epsilon =
      H ^ 2 * phi)
    (hc : H.eval c = 0) (hh : H.derivative.eval c ≠ 0)
    (hB : B = (X - C c) ^ 2 * B2)
    (hF : A * B - C 3 * D = (X - C c) ^ 3 * F3)
    (hDshape : D = H * D1)
    (hBWshape : B * w = H * BW)
    (hrow : BW * terminalEDerivativeNumerator68 H E0 - D1 * K =
      C j * H ^ 2)
    (hnormalized :
      3 * H.derivative.eval c * F3.eval c =
        (2 * A.eval c * H.derivative.derivative.eval c +
          3 * H.derivative.eval c * A.derivative.eval c) * B2.eval c) :
    terminalRefinedIIIConjugateIIFNormalizedPacket68 H A B D c ∧
      (∃ M D2 BW1 : k[X],
        H = (X - C c) * M ∧ M.eval c = H.derivative.eval c ∧
        D1 = (X - C c) * D2 ∧ BW = (X - C c) * BW1 ∧
        C 3 * M * D2 = A * B2 - (X - C c) * F3 ∧
        M * BW1 = B2 * w ∧
        BW1 * terminalEDerivativeNumerator68 H E0 - D2 * K =
          C j * (X - C c) * M ^ 2 ∧
        (B2.eval c = 0 ∨ A.eval c = 0 ∨
          H.derivative.eval c * A.eval c ^ 2 * w.eval c +
            3 * K.eval c = 0)) := by
  have hEshape := S.terminalActualEShape68 (H := H)
    A C0 E0 b1 B w phi hb hW hPhi
  have hEroot : E0.eval c = A.eval c ^ 3 / 27 := by
    have he := congrArg (fun P : k[X] => P.eval c) hEshape
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat,
      hc, zero_pow, zero_mul, mul_zero, zero_add, add_zero] at he
    simpa [div_eq_mul_inv, mul_comm] using he
  have heDot := terminalEDerivativeNumerator_eval_root_68 H A E0 c hc hEroot
  refine ⟨⟨B2, F3, hB, hF, hnormalized⟩, ?_⟩
  exact terminalRefinedIII_normalized_loaded_packet_68 H A B D w
    (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 j c hc hh
      hB hF hDshape hBWshape hrow heDot

end RefinedIIIConjugateIIFNormalizedLoadedSource68

end Max11DegreeRoutes
