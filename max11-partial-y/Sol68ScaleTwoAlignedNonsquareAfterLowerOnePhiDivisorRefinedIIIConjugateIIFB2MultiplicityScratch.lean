import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateIIFLoadedRoutingScratch

/-! # The finite B2-multiplicity packet on conjugate component II -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateIIFB2MultiplicityAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- After the extra local factor is removed, the loaded row has nonzero
right-hand side.  Its three quotient relations give this exact unit product. -/
theorem terminalRefinedIII_B2_loaded_unit_product_68
    (h A b w bw d e K j : k)
    (hBW : h * bw = b * w)
    (hD : 3 * h * d = A * b)
    (hload : bw * e - d * K = j * h ^ 2)
    (he : e = -(1 / 9 : k) * h * A ^ 3) :
    A * b * (h * A ^ 2 * w + 3 * K) = -9 * j * h ^ 3 := by
  linear_combination -9 * h * hload + 9 * h * bw * he -
    h * A ^ 3 * hBW - 3 * K * hD

end RefinedIIIConjugateIIFB2MultiplicityAlgebra68

section RefinedIIIConjugateIIFB2MultiplicityPolynomial68

variable {k : Type*} [Field k] [CharZero k]

def terminalRefinedIIIConjugateIIFB2MultiplicityPacket68
    (H A B D w e K D1 BW B2 F3 : k[X]) (j c : k) : Prop :=
  ∃ M D2 BW1 B3 F4 D3 BW2 : k[X],
    H = (X - C c) * M ∧ M.eval c = H.derivative.eval c ∧
    B2 = (X - C c) * B3 ∧ F3 = (X - C c) * F4 ∧
    D2 = (X - C c) * D3 ∧ BW1 = (X - C c) * BW2 ∧
    B = (X - C c) ^ 3 * B3 ∧
    A * B - C 3 * D = (X - C c) ^ 4 * F4 ∧
    D1 = (X - C c) ^ 2 * D3 ∧ BW = (X - C c) ^ 2 * BW2 ∧
    C 3 * M * D3 = A * B3 - (X - C c) * F4 ∧
    M * BW2 = B3 * w ∧
    BW2 * e - D3 * K = C j * M ^ 2 ∧
    A.eval c * B3.eval c *
        (H.derivative.eval c * A.eval c ^ 2 * w.eval c +
          3 * K.eval c) =
      -9 * j * H.derivative.eval c ^ 3

/-- The child `B2(c)=0` is a finite multiplicity packet.  It adds one factor
to `B`, `AB-3D`, `D1`, and `BW`; after cancellation the loaded row has the
nonzero constant right-hand side `j M^2`. -/
theorem terminalRefinedIII_normalized_loaded_B2_multiplicity_68
    (H A B D w e K D1 BW B2 F3 M D2 BW1 : k[X]) (j c : k)
    (hh : H.derivative.eval c ≠ 0)
    (hHM : H = (X - C c) * M)
    (hMc : M.eval c = H.derivative.eval c)
    (hB : B = (X - C c) ^ 2 * B2)
    (hF : A * B - C 3 * D = (X - C c) ^ 3 * F3)
    (hD2 : D1 = (X - C c) * D2)
    (hBW1 : BW = (X - C c) * BW1)
    (hDcore : C 3 * M * D2 = A * B2 - (X - C c) * F3)
    (hBWcore : M * BW1 = B2 * w)
    (hrow1 : BW1 * e - D2 * K = C j * (X - C c) * M ^ 2)
    (hnormalized :
      3 * H.derivative.eval c * F3.eval c =
        (2 * A.eval c * H.derivative.derivative.eval c +
          3 * H.derivative.eval c * A.derivative.eval c) * B2.eval c)
    (he : e.eval c =
      -(1 / 9 : k) * H.derivative.eval c * A.eval c ^ 3)
    (hB2c : B2.eval c = 0) :
    terminalRefinedIIIConjugateIIFB2MultiplicityPacket68
      H A B D w e K D1 BW B2 F3 j c := by
  let L : k[X] := X - C c
  have hL : L ≠ 0 := X_sub_C_ne_zero c
  have hF3c : F3.eval c = 0 := by
    have hn := hnormalized
    rw [hB2c, mul_zero] at hn
    have hcoef : (3 : k) * H.derivative.eval c ≠ 0 :=
      mul_ne_zero (by norm_num) hh
    exact (mul_eq_zero.mp hn).resolve_left hcoef
  have hLB2 : L ∣ B2 := by
    rw [dvd_iff_isRoot]
    exact hB2c
  have hLF3 : L ∣ F3 := by
    rw [dvd_iff_isRoot]
    exact hF3c
  obtain ⟨B3, hB3⟩ := hLB2
  obtain ⟨F4, hF4⟩ := hLF3
  have hD2c : D2.eval c = 0 := by
    have hd := congrArg (fun P : k[X] => P.eval c) hDcore
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
      eval_C, hB2c, hF3c, mul_zero, sub_zero] at hd
    have hcoef : (3 : k) * M.eval c ≠ 0 :=
      mul_ne_zero (by norm_num) (by simpa only [hMc] using hh)
    exact (mul_eq_zero.mp hd).resolve_left hcoef
  have hBW1c : BW1.eval c = 0 := by
    have hb := congrArg (fun P : k[X] => P.eval c) hBWcore
    simp only [eval_mul, hB2c, zero_mul] at hb
    exact (mul_eq_zero.mp hb).resolve_left (by simpa only [hMc] using hh)
  have hLD2 : L ∣ D2 := by
    rw [dvd_iff_isRoot]
    exact hD2c
  have hLBW1 : L ∣ BW1 := by
    rw [dvd_iff_isRoot]
    exact hBW1c
  obtain ⟨D3, hD3⟩ := hLD2
  obtain ⟨BW2, hBW2⟩ := hLBW1
  change B2 = L * B3 at hB3
  change F3 = L * F4 at hF4
  change D2 = L * D3 at hD3
  change BW1 = L * BW2 at hBW2
  have hDcore3 : C 3 * M * D3 = A * B3 - L * F4 := by
    rw [hD3, hB3, hF4] at hDcore
    have hz : L * (C 3 * M * D3 - (A * B3 - L * F4)) = 0 := by
      linear_combination hDcore
    have hcanc := (mul_eq_zero.mp hz).resolve_left hL
    linear_combination hcanc
  have hBWcore2 : M * BW2 = B3 * w := by
    rw [hBW2, hB3] at hBWcore
    have hz : L * (M * BW2 - B3 * w) = 0 := by
      linear_combination hBWcore
    have hcanc := (mul_eq_zero.mp hz).resolve_left hL
    linear_combination hcanc
  have hrow2 : BW2 * e - D3 * K = C j * M ^ 2 := by
    rw [hBW2, hD3] at hrow1
    have hz : L * (BW2 * e - D3 * K - C j * M ^ 2) = 0 := by
      linear_combination hrow1
    have hcanc := (mul_eq_zero.mp hz).resolve_left hL
    linear_combination hcanc
  have hB3full : B = L ^ 3 * B3 := by
    change B = L ^ 2 * B2 at hB
    rw [hB, hB3]
    ring
  have hF4full : A * B - C 3 * D = L ^ 4 * F4 := by
    change A * B - C 3 * D = L ^ 3 * F3 at hF
    rw [hF, hF4]
    ring
  have hD3full : D1 = L ^ 2 * D3 := by
    change D1 = L * D2 at hD2
    rw [hD2, hD3]
    ring
  have hBW2full : BW = L ^ 2 * BW2 := by
    change BW = L * BW1 at hBW1
    rw [hBW1, hBW2]
    ring
  have hDroot : 3 * H.derivative.eval c * D3.eval c =
      A.eval c * B3.eval c := by
    have hd := congrArg (fun P : k[X] => P.eval c) hDcore3
    dsimp only [L] at hd
    simp only [eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul,
      eval_C, sub_zero] at hd
    simpa only [hMc] using hd
  have hBWroot : H.derivative.eval c * BW2.eval c =
      B3.eval c * w.eval c := by
    have hb := congrArg (fun P : k[X] => P.eval c) hBWcore2
    simp only [eval_mul] at hb
    simpa only [hMc] using hb
  have hloadroot : BW2.eval c * e.eval c - D3.eval c * K.eval c =
      j * H.derivative.eval c ^ 2 := by
    have hr := congrArg (fun P : k[X] => P.eval c) hrow2
    simp only [eval_sub, eval_mul, eval_C, eval_pow] at hr
    simpa only [hMc] using hr
  have hunit := terminalRefinedIII_B2_loaded_unit_product_68
    (H.derivative.eval c) (A.eval c) (B3.eval c) (w.eval c)
      (BW2.eval c) (D3.eval c) (e.eval c) (K.eval c) j
      hBWroot hDroot hloadroot he
  exact ⟨M, D2, BW1, B3, F4, D3, BW2, hHM, hMc, hB3, hF4,
    hD3, hBW2, hB3full, hF4full, hD3full, hBW2full, hDcore3,
    hBWcore2, hrow2, hunit⟩

end RefinedIIIConjugateIIFB2MultiplicityPolynomial68

section RefinedIIIConjugateIIFB2MultiplicitySource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source specialization of the sole `B2(c)=0` child from the routed packet. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateIIFB2MultiplicityPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 : k[X]) (c : k)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H (cubicANumerator68 t r) C0 S.gamma =
      H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) b1 C0 E0
      S.gamma S.epsilon = H ^ 2 * phi)
    (hX : C 3 * t - r ^ 2 = H * X0)
    (hc : H.eval c = 0) (hh : H.derivative.eval c ≠ 0)
    (hB : B = (X - C c) ^ 2 * B2)
    (hF : cubicANumerator68 t r * B - C 3 * D =
      (X - C c) ^ 3 * F3)
    (hDshape : D = H * D1)
    (hBWshape : B * w = H * BW)
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
      (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 j c := by
  obtain ⟨_, M, D2, BW1, hHM, hMc, hD2, hBW1, hDcore,
      hBWcore, hrow1, _⟩ :=
    S.terminalRefinedIIIConjugateIIFLoadedRoutingPacket (H := H)
      t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW hPhi hX
      hc hh hB hF hDshape hBWshape hrow hnormalized
  have hEshape := S.terminalActualEShape68 (H := H)
    (cubicANumerator68 t r) C0 E0 b1 B w phi hb hW hPhi
  have hEroot : E0.eval c = (cubicANumerator68 t r).eval c ^ 3 / 27 := by
    have he := congrArg (fun P : k[X] => P.eval c) hEshape
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat,
      hc, zero_pow, zero_mul, mul_zero, zero_add, add_zero] at he
    simpa [div_eq_mul_inv, mul_comm] using he
  have heDot := terminalEDerivativeNumerator_eval_root_68 H
    (cubicANumerator68 t r) E0 c hc hEroot
  exact terminalRefinedIII_normalized_loaded_B2_multiplicity_68 H
    (cubicANumerator68 t r) B D w (terminalEDerivativeNumerator68 H E0)
      K D1 BW B2 F3 M D2 BW1 j c hh hHM hMc hB hF hD2 hBW1
      hDcore hBWcore hrow1 hnormalized heDot hB2c

end RefinedIIIConjugateIIFB2MultiplicitySource68

end Max11DegreeRoutes
