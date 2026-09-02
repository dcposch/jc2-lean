import Fable68ScaleTwoAlignedNonsquareMixedNextScratch

/-! # Fifth row of the preserved transverse two-root allocation

The fourth-row packet leaves a three-way split at the `Φ₁`-root `b` of
the transverse allocation: the `k₁ = H k₂` limb with the once-reduced
terminal row, the `b₂ = H b₃`, `d₂ = H e₁` limb with both once-reduced
rows, and the transverse residual `d₂ = H² e₂` with `Φ₁'`, `w₂`, `d₂'`
pins.  Each limb owns exactly one unconsumed low-order Taylor
coefficient of its reduced rows, and this file consumes precisely that
coefficient in each limb.

In the `k₁` limb the zeroth coefficient of `b₂ w₂ Ė - d₂ k₂ = j H³` at
`b` is the retained terminal derivative face divided by the unit
`H'(b)`, and all coefficients through order one at the `r`-root are
vacuous on the retained double zeros; the first genuinely new face is
the first coefficient at `b`,
`b₂' w₂ Ė + b₂ w₂' Ė + b₂ w₂ Ė' = d₂' k₂ + d₂ k₂'` there.  In the `b₂`
limb the retained `r`-root derivative faces backwire both new scalars,
`b₃(a) = 0` and `e₁(a) = 0`, and the zeroth coefficient of
`e₁ k₁ = H b₃ w₂ Ė - j H³` at `b` is the exact product split
`e₁(b) k₁(b) = 0`: either `e₁` gains both core roots and the double
transfer `d₂ = H² e₂` lands with both rows reduced once more, or `k₁`
gains both core roots and the terminal row reduces to
`e₁ k₂ = b₃ w₂ Ė - j H²`.  In the residual limb the second coefficient
of the reduced `I₄` row `b₂ Φ₁ + 6 H³ w₂ e₂ = 0` at `b` is the first
face loading `Φ₁''`: cancelling the square of the local linear factor
forces `Φ₁''(b) = 0`, so `b` is at least a triple root and
`Φ₁ = (X - b)³ ψ₃` exactly.  No honest contradiction is available in
any limb: all three children are returned refined, and the `H ∣ r`,
`H ∣ Φ₁` siblings pass through untouched. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section MixedFifthRowAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Source backwire for a once-divided scalar: at a simple core root the
quotient inherits the zero of the numerator's derivative. -/
theorem quotientEvalZero_of_derivativeZero_68
    (H P Q : k[X]) (a : k) (ha : H.eval a = 0)
    (hda : H.derivative.eval a ≠ 0) (hPQ : P = H * Q)
    (hPda : P.derivative.eval a = 0) :
    Q.eval a = 0 := by
  have hder := congrArg (fun R : k[X] => R.derivative.eval a) hPQ
  simp only [derivative_mul, eval_add, eval_mul, ha, zero_mul, add_zero]
    at hder
  rw [hPda] at hder
  exact (mul_eq_zero.mp hder.symm).resolve_left hda

/-- First Taylor coefficient at a core root of the once-reduced terminal
row carried by the `k₁ = H k₂` limb. -/
theorem mixedReducedTerminalFirstCoefficient_68
    (H b2 w2 eDot d2 k2 : k[X]) (j b : k) (hb : H.eval b = 0)
    (hrow : b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) :
    b2.derivative.eval b * w2.eval b * eDot.eval b +
        b2.eval b * w2.derivative.eval b * eDot.eval b +
        b2.eval b * w2.eval b * eDot.derivative.eval b -
      (d2.derivative.eval b * k2.eval b +
        d2.eval b * k2.derivative.eval b) = 0 := by
  have hder := congrArg (fun P : k[X] => P.derivative.eval b) hrow
  simp only [derivative_sub, derivative_mul, derivative_pow, derivative_C,
    eval_sub, eval_add, eval_mul, eval_pow, eval_C, hb, zero_mul, mul_zero,
    zero_pow, sub_zero, zero_add, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true] at hder
  linear_combination hder

/-- Zeroth Taylor coefficient at a core root of the twice-reduced
terminal row carried by the `b₂ = H b₃` limb: the exact product split. -/
theorem mixedReducedTerminalZeroCoefficient_68
    (H b3 w2 eDot e1 k1 : k[X]) (j b : k) (hb : H.eval b = 0)
    (hrow : e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3) :
    e1.eval b * k1.eval b = 0 := by
  have h0 := congrArg (fun P : k[X] => P.eval b) hrow
  simp only [eval_sub, eval_mul, eval_pow, eval_C, hb, zero_mul, mul_zero,
    zero_pow, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    at h0
  linear_combination h0

/-- Second Taylor coefficient of the reduced `I₄` row at a core root that
is a double zero of `Φ₁` but a unit for `b₂`: cancelling the square of
the local linear factor forces the root to third order on `Φ₁`, killing
`Φ₁''` there and extracting a full linear cube. -/
theorem mixedReducedIFourCube_68
    (H b2 phi1 w2 e2 : k[X]) (b : k) (hb : H.eval b = 0)
    (hpb : phi1.eval b = 0) (hphi1db : phi1.derivative.eval b = 0)
    (hb2b : b2.eval b ≠ 0)
    (hI4red : b2 * phi1 + (6 : k[X]) * H ^ 3 * w2 * e2 = 0) :
    phi1.derivative.derivative.eval b = 0 ∧
      ∃ psi3 : k[X], phi1 = (X - C b) ^ 3 * psi3 := by
  have hLne : (X - C b : k[X]) ≠ 0 := X_sub_C_ne_zero b
  have hLH : (X - C b : k[X]) ∣ H := by
    rw [dvd_iff_isRoot]
    exact hb
  obtain ⟨M, hHM⟩ := hLH
  have hLphi : (X - C b : k[X]) ∣ phi1 := by
    rw [dvd_iff_isRoot]
    exact hpb
  obtain ⟨p2, hp2⟩ := hLphi
  have hp2b : p2.eval b = 0 := by
    have hder := congrArg (fun P : k[X] => P.derivative.eval b) hp2
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, eval_add, eval_sub, eval_mul, eval_one, eval_X,
      eval_C, sub_self, zero_mul, add_zero] at hder
    linear_combination hphi1db - hder
  have hLp2 : (X - C b : k[X]) ∣ p2 := by
    rw [dvd_iff_isRoot]
    exact hp2b
  obtain ⟨p3, hp3⟩ := hLp2
  -- One core-square cancellation exposes the third-order coefficient.
  have hquot : b2 * p3 +
      (6 : k[X]) * (X - C b) * M ^ 3 * w2 * e2 = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hLne)
    have hc := hI4red
    rw [hp2, hp3, hHM] at hc
    linear_combination hc
  have hp3b : p3.eval b = 0 := by
    have h0 := congrArg (fun P : k[X] => P.eval b) hquot
    simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
      eval_ofNat, eval_zero, sub_self, zero_mul, mul_zero, add_zero]
      at h0
    have hz : b2.eval b * p3.eval b = 0 := by linear_combination h0
    exact (mul_eq_zero.mp hz).resolve_left hb2b
  have hLp3 : (X - C b : k[X]) ∣ p3 := by
    rw [dvd_iff_isRoot]
    exact hp3b
  obtain ⟨psi3, hpsi3⟩ := hLp3
  have hcube : phi1 = (X - C b) ^ 3 * psi3 := by
    rw [hp2, hp3, hpsi3]
    ring
  refine ⟨?_, psi3, hcube⟩
  have hdd := congrArg
    (fun P : k[X] => P.derivative.derivative.eval b) hcube
  simp only [derivative_add, derivative_mul, derivative_pow,
    derivative_sub, derivative_X, derivative_C, derivative_one, sub_zero,
    one_mul, mul_one, eval_add, eval_sub, eval_mul, eval_pow, eval_one,
    eval_X, eval_C, sub_self, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at hdd
  linear_combination hdd

end MixedFifthRowAlgebra68

section MixedFifthRowSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Fifth-row refinement of the preserved transverse two-root allocation.
Each fourth-row limb consumes exactly its next unused Taylor coefficient:
the `k₁ = H k₂` limb gains the first coefficient of its reduced terminal
row at `b`; the `b₂ = H b₃` limb gains the backwired zeros
`b₃(a) = e₁(a) = 0` and splits on the zeroth coefficient
`e₁(b) k₁(b) = 0` into the double transfer `d₂ = H² e₂` with both rows
reduced once more, or `k₁ = H k₂` with the terminal row reduced; the
transverse residual gains `Φ₁''(b) = 0` and the exact cube
`Φ₁ = (X - b)³ ψ₃` from the second coefficient of its reduced `I₄` row.
The `H ∣ r` and `H ∣ Φ₁` siblings pass through untouched. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneMixedFifthRowPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t X Yd phi1 k1 b2 d2 w2 : k[X]),
      p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4) ∧
      (H ∣ r ∨ H ∣ phi1 ∨
        (let A0 := cubicANumerator68 t r
         let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
         let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
           (p.coeff 3) t r
         let eDot := terminalEDerivativeNumerator68 H E0
         ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
           r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
           r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
           b2.eval a = 0 ∧ k1.eval a = 0 ∧ d2.eval a = 0 ∧
           b2.derivative.eval a = 0 ∧ d2.derivative.eval a = 0 ∧
           b2.eval b * phi1.derivative.eval b +
             6 * H.derivative.eval b * w2.eval b * d2.eval b = 0 ∧
           H.derivative.eval b * b2.eval b * w2.eval b * eDot.eval b -
             (d2.derivative.eval b * k1.eval b +
               d2.eval b * k1.derivative.eval b) = 0 ∧
           (r.eval b ^ 2 * b2.eval b + 36 * d2.eval b) *
             (6 * phi1.derivative.eval b -
               r.eval b ^ 2 * w2.eval b * H.derivative.eval b) = 0 ∧
           15552 * eDot.eval b = H.derivative.eval b * r.eval b ^ 6 ∧
           ((k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
               b2 * w2 * eDot - d2 * k2 = C j * H ^ 3 ∧
               b2.derivative.eval b * w2.eval b * eDot.eval b +
                   b2.eval b * w2.derivative.eval b * eDot.eval b +
                   b2.eval b * w2.eval b * eDot.derivative.eval b -
                 (d2.derivative.eval b * k2.eval b +
                   d2.eval b * k2.derivative.eval b) = 0) ∨
            (d2.eval b = 0 ∧ b2.eval b = 0 ∧ ∃ b3 e1 : k[X],
               b2 = H * b3 ∧ d2 = H * e1 ∧
               b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0 ∧
               e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3 ∧
               b3.eval a = 0 ∧ e1.eval a = 0 ∧
               ((e1.eval b = 0 ∧ ∃ e2 : k[X], e1 = H * e2 ∧
                   d2 = H ^ 2 * e2 ∧
                   b3 * phi1 + (6 : k[X]) * H ^ 2 * w2 * e2 = 0 ∧
                   e2 * k1 = b3 * w2 * eDot - C j * H ^ 2) ∨
                (k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
                   e1 * k2 = b3 * w2 * eDot - C j * H ^ 2))) ∨
            (d2.eval b = 0 ∧ k1.eval b ≠ 0 ∧ b2.eval b ≠ 0 ∧
               phi1.derivative.eval b = 0 ∧ w2.eval b = 0 ∧
               d2.derivative.eval b = 0 ∧
               phi1.derivative.derivative.eval b = 0 ∧
               ∃ e2 psi3 : k[X], d2 = H ^ 2 * e2 ∧
                 phi1 = (Polynomial.X - C b) ^ 3 * psi3 ∧
                 b2 * phi1 + (6 : k[X]) * H ^ 3 * w2 * e2 = 0 ∧
                 b2 * w2 * eDot - H * e2 * k1 = C j * H ^ 3 ∧
                 b2.eval b * w2.derivative.eval b * eDot.eval b =
                   H.derivative.eval b * e2.eval b * k1.eval b)))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, hsplit⟩ :=
    S.terminalAfterLowerOneMixedFourthRowPacket (H := H) hdeg hp hq hp6
      hq8 haligned hjac hj
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  rcases hsplit with hr | hphi | hmix
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inl hr⟩
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inr (Or.inl hphi)⟩
  · obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hb2a, hk1a, hd2a,
      hb2da, hd2da, hI4faceB, hrowFaceB, hfaceB, hpinB, htri⟩ := hmix
    refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow,
      Or.inr (Or.inr ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hb2a, hk1a,
        hd2a, hb2da, hd2da, hI4faceB, hrowFaceB, hfaceB, hpinB, ?_⟩)⟩
    rcases htri with ⟨hk1b, k2, hk2, hk2row⟩ |
      ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red, he1row⟩ |
      ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db, e2, hd2sq, hI4red,
        hrowRed, hface⟩
    · -- `k₁` limb: first coefficient of the reduced terminal row at `b`.
      exact Or.inl ⟨hk1b, k2, hk2, hk2row,
        mixedReducedTerminalFirstCoefficient_68 H b2 w2 _ d2 k2 j b hb
          hk2row⟩
    · -- `b₂` limb: backwired scalars and the zeroth-coefficient split.
      have hb3a : b3.eval a = 0 :=
        quotientEvalZero_of_derivativeZero_68 H b2 b3 a ha
          (hsimple a ha) hb2b3 hb2da
      have he1a : e1.eval a = 0 :=
        quotientEvalZero_of_derivativeZero_68 H d2 e1 a ha
          (hsimple a ha) hd2e1 hd2da
      have hsplit0 := mixedReducedTerminalZeroCoefficient_68 H b3 w2 _
        e1 k1 j b hb he1row
      refine Or.inr (Or.inl ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red,
        he1row, hb3a, he1a, ?_⟩)
      rcases mul_eq_zero.mp hsplit0 with he1b | hk1b
      · obtain ⟨e2, he2⟩ := dvd_of_two_simple_root_evals_68 H e1 hdeg
          hsimple a b hab ha hb he1a he1b
        refine Or.inl ⟨he1b, e2, he2, ?_, ?_, ?_⟩
        · rw [hd2e1, he2]
          ring
        · have hc := hI4red
          rw [he2] at hc
          linear_combination hc
        · apply mul_left_cancel₀ hH
          have hc := he1row
          rw [he2] at hc
          linear_combination hc
      · obtain ⟨k2, hk2⟩ := dvd_of_two_simple_root_evals_68 H k1 hdeg
          hsimple a b hab ha hb hk1a hk1b
        refine Or.inr ⟨hk1b, k2, hk2, ?_⟩
        apply mul_left_cancel₀ hH
        have hc := he1row
        rw [hk2] at hc
        linear_combination hc
    · -- Transverse residual: second coefficient of the reduced `I₄` row.
      obtain ⟨hphi1ddb, psi3, hcube⟩ := mixedReducedIFourCube_68 H b2
        phi1 w2 e2 b hb hpb hphi1db hb2b hI4red
      exact Or.inr (Or.inr ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db,
        hphi1ddb, e2, psi3, hd2sq, hcube, hI4red, hrowRed, hface⟩)

end MixedFifthRowSource68

end Max11DegreeRoutes
