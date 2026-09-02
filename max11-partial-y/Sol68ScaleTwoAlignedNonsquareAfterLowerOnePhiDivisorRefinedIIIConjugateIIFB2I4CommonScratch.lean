import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateIIFB2MultiplicityScratch

/-! # The divided-I4 closure of the B2-multiplicity child -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateIIFB2I4CommonPolynomial68

variable {k : Type*} [Field k] [CharZero k]

/-- The next independent face after the finite `B2` multiplicity packet is
the divided I4 identity.  Cancelling the cubic local factor gives
`B3(c) * (phi(c)+2*A(c)*w(c))=0`; the loaded unit product makes `B3(c)` a
unit, so this child rejoins the common `G` face. -/
theorem terminalRefinedIII_B2_multiplicity_I4_common_68
    (H A B D w phi e K D1 BW B2 F3 : k[X]) (j c : k)
    (hh : H.derivative.eval c ≠ 0) (hj : j ≠ 0)
    (hI4 : B * phi + C 6 * H * w * D1 = 0)
    (hpacket : terminalRefinedIIIConjugateIIFB2MultiplicityPacket68
      H A B D w e K D1 BW B2 F3 j c) :
    phi.eval c + 2 * A.eval c * w.eval c = 0 := by
  obtain ⟨M, D2, BW1, B3, F4, D3, BW2, hHM, hMc, hB3, hF4,
      hD3, hBW2, hBfull, hFfull, hDfull, hBWfull, hDcore,
      hBWcore, hrow, hunit⟩ := hpacket
  let L : k[X] := X - C c
  have hL : L ≠ 0 := X_sub_C_ne_zero c
  change B = L ^ 3 * B3 at hBfull
  change H = L * M at hHM
  change D1 = L ^ 2 * D3 at hDfull
  have hI4q : B3 * phi + C 6 * M * w * D3 = 0 := by
    rw [hBfull, hHM, hDfull] at hI4
    have hz : L ^ 3 * (B3 * phi + C 6 * M * w * D3) = 0 := by
      linear_combination hI4
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 3 hL)
  have hI4root : B3.eval c * phi.eval c +
      6 * H.derivative.eval c * w.eval c * D3.eval c = 0 := by
    have hi := congrArg (fun P : k[X] => P.eval c) hI4q
    simp only [eval_add, eval_mul, eval_C, eval_ofNat, eval_zero] at hi
    simpa only [hMc] using hi
  have hDroot : 3 * H.derivative.eval c * D3.eval c =
      A.eval c * B3.eval c := by
    have hd := congrArg (fun P : k[X] => P.eval c) hDcore
    simp only [eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul,
      eval_C, sub_zero] at hd
    simpa only [hMc] using hd
  have hrhs : (-9 : k) * j * H.derivative.eval c ^ 3 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hj) (pow_ne_zero 3 hh)
  have hunitne : A.eval c * B3.eval c *
      (H.derivative.eval c * A.eval c ^ 2 * w.eval c +
        3 * K.eval c) ≠ 0 := by
    rw [hunit]
    exact hrhs
  have hB3ne : B3.eval c ≠ 0 := by
    intro hzero
    apply hunitne
    rw [hzero]
    ring
  have hproduct : B3.eval c *
      (phi.eval c + 2 * A.eval c * w.eval c) = 0 := by
    linear_combination hI4root - 2 * w.eval c * hDroot
  exact (mul_eq_zero.mp hproduct).resolve_left hB3ne

/-- The same result stated as the exact common branch of the original
degeneracy packet.  Its third disjunction is witnessed by `B(c)=0`. -/
theorem terminalRefinedIII_B2_multiplicity_common_degeneracy_68
    (H A B D w phi e K D1 BW B2 F3 : k[X]) (j c : k)
    (hh : H.derivative.eval c ≠ 0) (hj : j ≠ 0)
    (hI4 : B * phi + C 6 * H * w * D1 = 0)
    (hpacket : terminalRefinedIIIConjugateIIFB2MultiplicityPacket68
      H A B D w e K D1 BW B2 F3 j c) :
    terminalPhiDivisorDegeneracy68 (A.eval c) (B.eval c) (D.eval c)
      (w.eval c) (phi.eval c) (e.eval c) (K.eval c)
      (H.derivative.eval c) := by
  have hG := terminalRefinedIII_B2_multiplicity_I4_common_68
    H A B D w phi e K D1 BW B2 F3 j c hh hj hI4 hpacket
  obtain ⟨M, D2, BW1, B3, F4, D3, BW2, hHM, hMc, hB3, hF4,
      hD3, hBW2, hBfull, hFfull, hDfull, hBWfull, hDcore,
      hBWcore, hrow, hunit⟩ := hpacket
  have hB0 : B.eval c = 0 := by
    have hb := congrArg (fun P : k[X] => P.eval c) hBfull
    simp [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hb
    exact hb
  have hF0 : A.eval c * B.eval c - 3 * D.eval c = 0 := by
    have hf := congrArg (fun P : k[X] => P.eval c) hFfull
    simp [eval_sub, eval_mul, eval_C, eval_ofNat, eval_pow, eval_X] at hf
    exact hf
  exact Or.inl ⟨hF0, hG, Or.inr (Or.inl hB0)⟩

end RefinedIIIConjugateIIFB2I4CommonPolynomial68

section RefinedIIIConjugateIIFB2I4CommonSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing closure of the sole higher-multiplicity child.  The packet
is preserved, and its independent divided-I4 face routes it to the common
degeneracy component. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateIIFB2I4CommonPacket
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
            (cubicANumerator68 t r).derivative.eval c) * B2.eval c)
    (hB2c : B2.eval c = 0) :
    terminalRefinedIIIConjugateIIFB2MultiplicityPacket68 H
        (cubicANumerator68 t r) B D w
        (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 j c ∧
      terminalPhiDivisorDegeneracy68
        ((cubicANumerator68 t r).eval c) (B.eval c) (D.eval c)
        (w.eval c) (phi.eval c)
        ((terminalEDerivativeNumerator68 H E0).eval c) (K.eval c)
        (H.derivative.eval c) := by
  have hpacket := S.terminalRefinedIIIConjugateIIFB2MultiplicityPacket
    (H := H) t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW hPhi
      hX hc hh hB hF hDshape hBWshape hrow hnormalized hB2c
  refine ⟨hpacket, ?_⟩
  exact terminalRefinedIII_B2_multiplicity_common_degeneracy_68 H
    (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 j c
      hh hj hI4 hpacket

end RefinedIIIConjugateIIFB2I4CommonSource68

end Max11DegreeRoutes
