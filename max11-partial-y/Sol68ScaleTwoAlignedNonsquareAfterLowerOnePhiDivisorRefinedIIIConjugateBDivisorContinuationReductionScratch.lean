import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateStableReductionAssemblyScratch

/-! # Reduction of the stable B-divisor continuation

The stable local shape `B=(X-c)^2 B2` and `H=(X-c)M` lets the global
quotient `B=H B1` cancel at the conjugate root.  The cubic face then gives
the same local factor for `D1`, while `B1*w=BW` gives it for `BW`.  The
result is a fully cancelled local packet.  Its sole split is whether the new
quotient vanishes at `c`: that branch enters the verified `B2` multiplicity
consumer; the unit branch gives the two common scalar faces.  No new source
coefficient is opened.
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

section BDivisorContinuationReductionAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Exact local reduction of the global `H | B` packet. -/
def terminalRefinedIIIConjugateBDivisorContinuationReduction68
    (H A B D w phi e K D1 BW B2 F3 : k[X]) (j c : k) : Prop :=
  terminalRefinedIIIConjugateBDivisorContinuation68
      H B D w phi e K D1 BW j ∧
    ∃ B1 M Bq Dq Wq : k[X],
      H = (X - C c) * M ∧ M.eval c = H.derivative.eval c ∧
      B = H * B1 ∧ B1 = (X - C c) * Bq ∧
      D1 = (X - C c) * Dq ∧ BW = (X - C c) * Wq ∧
      B2 = M * Bq ∧ Wq = Bq * w ∧
      Bq * phi + 6 * w * Dq = 0 ∧
      Wq * e - Dq * K = C j * (X - C c) * M ^ 2 ∧
      A * B2 - C 3 * M * Dq = (X - C c) * F3 ∧
      ((Bq.eval c = 0 ∧
          terminalRefinedIIIConjugateIIFB2MultiplicityPacket68
            H A B D w e K D1 BW B2 F3 j c) ∨
       (Bq.eval c ≠ 0 ∧
          phi.eval c + 2 * A.eval c * w.eval c = 0 ∧
          3 * w.eval c * e.eval c = A.eval c * K.eval c))

/-- Cancellation of the stable source shapes, with the already verified
`B2(c)=0` consumer supplied as the only external branch theorem. -/
theorem terminalRefinedIII_conjugateB_divisor_continuation_reduction_68
    (H A B D w phi e K D1 BW B2 F3 : k[X]) (j c : k)
    (hc : H.eval c = 0) (hh : H.derivative.eval c ≠ 0)
    (hBshape : B = (X - C c) ^ 2 * B2)
    (hFshape : A * B - C 3 * D = (X - C c) ^ 3 * F3)
    (hDshape : D = H * D1)
    (hcontinuation : terminalRefinedIIIConjugateBDivisorContinuation68
      H B D w phi e K D1 BW j)
    (hB2consumer : B2.eval c = 0 →
      terminalRefinedIIIConjugateIIFB2MultiplicityPacket68
        H A B D w e K D1 BW B2 F3 j c) :
    terminalRefinedIIIConjugateBDivisorContinuationReduction68
      H A B D w phi e K D1 BW B2 F3 j c := by
  let L : k[X] := X - C c
  have hL : L ≠ 0 := X_sub_C_ne_zero c
  have hcontinuation0 := hcontinuation
  obtain ⟨B1, hB1, hB1w, hI4, hrow⟩ := hcontinuation
  obtain ⟨M, hHM, hMc⟩ := simpleRoot_linear_factor_packet_68 H c hc hh
  change H = L * M at hHM
  change B = L ^ 2 * B2 at hBshape
  change A * B - C 3 * D = L ^ 3 * F3 at hFshape
  have hBcore : L * B2 = M * B1 := by
    have heq : L ^ 2 * B2 = (L * M) * B1 := by
      calc
        L ^ 2 * B2 = B := hBshape.symm
        _ = H * B1 := hB1
        _ = (L * M) * B1 := by rw [hHM]
    have hz : L * (L * B2 - M * B1) = 0 := by
      linear_combination heq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hL)
  have hB1c : B1.eval c = 0 := by
    have hb := congrArg (fun P : k[X] => P.eval c) hBcore
    dsimp only [L] at hb
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at hb
    exact (mul_eq_zero.mp hb.symm).resolve_left (by simpa only [hMc] using hh)
  have hLB1 : L ∣ B1 := by rw [dvd_iff_isRoot]; exact hB1c
  obtain ⟨Bq, hBq⟩ := hLB1
  have hB2core : B2 = M * Bq := by
    rw [hBq] at hBcore
    have hz : L * (B2 - M * Bq) = 0 := by
      linear_combination hBcore
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hL)
  have hDcore : L * A * B2 - C 3 * M * D1 = L ^ 2 * F3 := by
    rw [hBshape, hDshape, hHM] at hFshape
    have hz : L *
        (L * A * B2 - C 3 * M * D1 - L ^ 2 * F3) = 0 := by
      linear_combination hFshape
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hL)
  have hD1c : D1.eval c = 0 := by
    have hd := congrArg (fun P : k[X] => P.eval c) hDcore
    have hLc : L.eval c = 0 := by simp [L]
    simp only [eval_sub, eval_mul, eval_pow, eval_C, hLc, zero_mul,
      mul_zero, sub_zero] at hd
    have hcoef : (3 : k) * M.eval c ≠ 0 :=
      mul_ne_zero (by norm_num) (by simpa only [hMc] using hh)
    have hz : ((3 : k) * M.eval c) * D1.eval c = 0 := by
      linear_combination -hd
    exact (mul_eq_zero.mp hz).resolve_left hcoef
  have hLD1 : L ∣ D1 := by rw [dvd_iff_isRoot]; exact hD1c
  obtain ⟨Dq, hDq⟩ := hLD1
  let Wq : k[X] := Bq * w
  have hBWq : BW = L * Wq := by
    dsimp only [Wq]
    rw [hBq] at hB1w
    calc
      BW = (L * Bq) * w := hB1w.symm
      _ = L * (Bq * w) := by ring
  have hI4q : Bq * phi + 6 * w * Dq = 0 := by
    rw [hBq, hDq] at hI4
    have hz : L * (Bq * phi + 6 * w * Dq) = 0 := by
      linear_combination hI4
    exact (mul_eq_zero.mp hz).resolve_left hL
  have hrowq : Wq * e - Dq * K = C j * L * M ^ 2 := by
    rw [hBWq, hDq, hHM] at hrow
    have hz : L * (Wq * e - Dq * K - C j * L * M ^ 2) = 0 := by
      linear_combination hrow
    have hcancel := (mul_eq_zero.mp hz).resolve_left hL
    linear_combination hcancel
  have hfaceq : A * B2 - C 3 * M * Dq = L * F3 := by
    rw [hDq] at hDcore
    have hz : L * (A * B2 - C 3 * M * Dq - L * F3) = 0 := by
      linear_combination hDcore
    have hcancel := (mul_eq_zero.mp hz).resolve_left hL
    linear_combination hcancel
  refine ⟨hcontinuation0, B1, M, Bq, Dq, Wq, hHM, hMc, hB1, hBq,
    hDq, hBWq, hB2core, rfl, hI4q, hrowq, hfaceq, ?_⟩
  rcases eq_or_ne (Bq.eval c) 0 with hBqc | hBqc
  · left
    have hB2c : B2.eval c = 0 := by rw [hB2core, eval_mul, hBqc, mul_zero]
    exact ⟨hBqc, hB2consumer hB2c⟩
  · right
    have hfaceRoot : A.eval c * Bq.eval c = 3 * Dq.eval c := by
      have hf := congrArg (fun P : k[X] => P.eval c) hfaceq
      dsimp only [L] at hf
      simp only [eval_sub, eval_mul, eval_C, eval_X, sub_self, zero_mul] at hf
      have hB2eval := congrArg (fun P : k[X] => P.eval c) hB2core
      simp only [eval_mul] at hB2eval
      rw [hB2eval] at hf
      have hMne : M.eval c ≠ 0 := by simpa only [hMc] using hh
      have hprod : M.eval c * (A.eval c * Bq.eval c - 3 * Dq.eval c) = 0 := by
        linear_combination hf
      exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hMne)
    have hI4root : Bq.eval c * phi.eval c +
        6 * w.eval c * Dq.eval c = 0 := by
      simpa only [eval_add, eval_mul, eval_ofNat, eval_zero] using
        congrArg (fun P : k[X] => P.eval c) hI4q
    have hrowRoot : Bq.eval c * w.eval c * e.eval c -
        Dq.eval c * K.eval c = 0 := by
      have hr := congrArg (fun P : k[X] => P.eval c) hrowq
      dsimp only [Wq, L] at hr
      simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_X, sub_self,
        zero_mul, mul_zero] at hr
      exact hr
    refine ⟨hBqc, ?_, ?_⟩
    · have hprod : Bq.eval c *
          (phi.eval c + 2 * A.eval c * w.eval c) = 0 := by
        linear_combination hI4root + 2 * w.eval c * hfaceRoot
      exact (mul_eq_zero.mp hprod).resolve_left hBqc
    · have hprod : Bq.eval c *
          (3 * w.eval c * e.eval c - A.eval c * K.eval c) = 0 := by
        linear_combination 3 * hrowRoot - K.eval c * hfaceRoot
      exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hBqc)

end BDivisorContinuationReductionAlgebra68

section BDivisorContinuationReductionSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing wrapper; the vanishing quotient branch is handed directly
to the verified normalized `B2` multiplicity consumer. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIConjugateBDivisorContinuationReduction
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 : k[X]) (c : k)
    (hdeg : H.natDegree = 2)
    (hb : b1 = H * B)
    (hW : terminalScaledW68 H (cubicANumerator68 t r) C0 S.gamma =
      H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H (cubicANumerator68 t r) b1 C0 E0
      S.gamma S.epsilon = H ^ 2 * phi)
    (hX : C 3 * t - r ^ 2 = H * X0)
    (hc : H.eval c = 0)
    (hBshape : B = (X - C c) ^ 2 * B2)
    (hFshape : cubicANumerator68 t r * B - C 3 * D =
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
    (hcontinuation : terminalRefinedIIIConjugateBDivisorContinuation68 H B D
      w phi (terminalEDerivativeNumerator68 H E0) K D1 BW j) :
    terminalRefinedIIIConjugateBDivisorContinuationReduction68 H
      (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 j c := by
  have hh : H.derivative.eval c ≠ 0 :=
    nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hc
  apply terminalRefinedIII_conjugateB_divisor_continuation_reduction_68
    H (cubicANumerator68 t r) B D w phi
      (terminalEDerivativeNumerator68 H E0) K D1 BW B2 F3 j c hc hh
      hBshape hFshape hDshape hcontinuation
  intro hB2c
  exact S.terminalRefinedIIIConjugateIIFB2MultiplicityPacket (H := H)
    t r X0 C0 E0 b1 B D w phi K D1 BW B2 F3 c hb hW hPhi hX hc hh
    hBshape hFshape hDshape hBWshape hrow hnormalized hB2c

end BDivisorContinuationReductionSource68

end Max11DegreeRoutes
