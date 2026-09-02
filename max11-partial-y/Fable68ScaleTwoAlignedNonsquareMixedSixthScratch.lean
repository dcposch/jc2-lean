import Fable68ScaleTwoAlignedNonsquareMixedFollowingScratch

/-! # Sixth row of the preserved transverse two-root allocation

The fifth-row packet leaves three refined children at the `Φ₁`-root `b`
of the transverse allocation, and each of them (together with the shared
`r`-root data) owns exactly one unconsumed low-order Taylor coefficient.
This file consumes precisely that coefficient in each place.

At the shared level the second coefficient of the retained `I₄` row
`b₂ Φ₁ + 6 H w₂ d₂ = 0` at the `r`-root is the first face loading
`b₂''(a)`: every other term carries one of the retained zeros `b₂(a)`,
`b₂'(a)`, `d₂(a)`, `d₂'(a)` or the core value `H(a)`, so the row forces
`b₂''(a) Φ₁(a) = 0` and hence `b₂''(a) = 0` outright, since `Φ₁` is a
unit at the `r`-root.  In the `k₁ = H k₂` limb the second coefficient of
the reduced terminal row `b₂ w₂ Ė - d₂ k₂ = j H³` at `a` then collapses
to the exact product face `d₂''(a) k₂(a) = 0`, the first face loading
`d₂''(a)` and the value `k₂(a)`.  In the `b₂ = H b₃` limb the shared jet
backwires through the divisibility at the simple core root,
`b₂''(a) = 2 H'(a) b₃'(a)`, so `b₃'(a) = 0` exactly, and both
divisibility sub-limbs inherit it unchanged.  In the transverse residual
the third coefficient of the reduced `I₄` row `b₂ Φ₁ + 6 H³ w₂ e₂ = 0`
at `b` is exact: with `Φ₁ = (X - b)³ ψ₃` and `H = (X - b) M` the cube of
the local linear factor cancels term-wise, the cofactor row evaluates to
`b₂(b) ψ₃(b) = 0` because `w₂(b) = 0`, and `b₂(b) ≠ 0` forces
`ψ₃(b) = 0`; the triple root deepens to a quadruple root,
`Φ₁'''(b) = 0` and `Φ₁ = (X - b)⁴ ψ₄` exactly.  No honest contradiction
is available in any limb — the witnesses carry no degree bounds in the
retained interface — so all three children are returned refined and the
`H ∣ r`, `H ∣ Φ₁` siblings pass through untouched. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section MixedSixthRowAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Second Taylor coefficient of the retained `I₄` row at the `r`-root:
on the retained double zeros of `b₂` and `d₂` it reduces to
`b₂''(a) Φ₁(a) = 0`, killing `b₂''(a)` where `Φ₁` is a unit. -/
theorem mixedIFourSecondCoefficient_68
    (H b2 phi1 w2 d2 : k[X]) (a : k) (ha : H.eval a = 0)
    (hpa : phi1.eval a ≠ 0)
    (hb2a : b2.eval a = 0) (hb2da : b2.derivative.eval a = 0)
    (hd2a : d2.eval a = 0) (hd2da : d2.derivative.eval a = 0)
    (hI4 : b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0) :
    b2.derivative.derivative.eval a = 0 := by
  have hdd := congrArg
    (fun P : k[X] => P.derivative.derivative.eval a) hI4
  simp only [derivative_add, derivative_mul, derivative_ofNat,
    derivative_zero, eval_add, eval_mul, eval_ofNat, eval_zero, ha, hb2a,
    hb2da, hd2a, hd2da, zero_mul, mul_zero, zero_add, add_zero] at hdd
  have hz : b2.derivative.derivative.eval a * phi1.eval a = 0 := by
    linear_combination hdd
  exact (mul_eq_zero.mp hz).resolve_right hpa

/-- Second Taylor coefficient at the `r`-root of the once-reduced
terminal row carried by the `k₁ = H k₂` limb: with the shared
second-order kill of `b₂` it is the exact product face
`d₂''(a) k₂(a) = 0`. -/
theorem mixedReducedTerminalSecondCoefficient_68
    (H b2 w2 eDot d2 k2 : k[X]) (j a : k) (ha : H.eval a = 0)
    (hb2a : b2.eval a = 0) (hb2da : b2.derivative.eval a = 0)
    (hb2dda : b2.derivative.derivative.eval a = 0)
    (hd2a : d2.eval a = 0) (hd2da : d2.derivative.eval a = 0)
    (hrow : b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) :
    d2.derivative.derivative.eval a * k2.eval a = 0 := by
  have hdd := congrArg
    (fun P : k[X] => P.derivative.derivative.eval a) hrow
  simp only [derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, eval_sub, eval_add, eval_mul, eval_pow,
    eval_C, ha, hb2a, hb2da, hb2dda, hd2a, hd2da, pow_one, zero_mul,
    mul_zero, zero_add, add_zero, sub_zero, zero_sub, neg_eq_zero,
    zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at hdd
  linear_combination -hdd

/-- Source backwire for the derivative of a once-divided scalar: at a
simple core root a second-order zero of the numerator passes to a
first-order zero of the quotient. -/
theorem quotientDerivEvalZero_of_secondDerivativeZero_68
    (H P Q : k[X]) (a : k) (ha : H.eval a = 0)
    (hda : H.derivative.eval a ≠ 0) (hPQ : P = H * Q)
    (hQa : Q.eval a = 0)
    (hPdda : P.derivative.derivative.eval a = 0) :
    Q.derivative.eval a = 0 := by
  have hdd := congrArg
    (fun R : k[X] => R.derivative.derivative.eval a) hPQ
  simp only [derivative_add, derivative_mul, eval_add, eval_mul, ha, hQa,
    zero_mul, mul_zero, add_zero, zero_add] at hdd
  rw [hPdda] at hdd
  have hz : H.derivative.eval a * Q.derivative.eval a = 0 := by
    linear_combination (-1 / 2 : k) * hdd
  exact (mul_eq_zero.mp hz).resolve_left hda

/-- Third Taylor coefficient of the reduced `I₄` row at a core root that
is a triple zero of `Φ₁`, a zero of `w₂`, and a unit for `b₂`: the cube
of the local linear factor cancels term-wise, the cofactor row evaluates
to `b₂(b) ψ₃(b) = 0`, and the triple root deepens to a quadruple root. -/
theorem mixedReducedIFourQuartic_68
    (H b2 phi1 w2 e2 psi3 : k[X]) (b : k) (hb : H.eval b = 0)
    (hb2b : b2.eval b ≠ 0) (hw2b : w2.eval b = 0)
    (hcube : phi1 = (X - C b) ^ 3 * psi3)
    (hI4red : b2 * phi1 + (6 : k[X]) * H ^ 3 * w2 * e2 = 0) :
    psi3.eval b = 0 ∧
      phi1.derivative.derivative.derivative.eval b = 0 ∧
      ∃ psi4 : k[X], phi1 = (X - C b) ^ 4 * psi4 := by
  have hLne : (X - C b : k[X]) ≠ 0 := X_sub_C_ne_zero b
  have hLH : (X - C b : k[X]) ∣ H := by
    rw [dvd_iff_isRoot]
    exact hb
  obtain ⟨M, hHM⟩ := hLH
  -- The cube of the local linear factor cancels from the reduced row.
  have hquot : b2 * psi3 + (6 : k[X]) * M ^ 3 * w2 * e2 = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hLne)
    have hc := hI4red
    rw [hcube, hHM] at hc
    linear_combination hc
  have hpsi3b : psi3.eval b = 0 := by
    have h0 := congrArg (fun P : k[X] => P.eval b) hquot
    simp only [eval_add, eval_mul, eval_pow, eval_ofNat, eval_zero, hw2b,
      mul_zero, zero_mul, add_zero] at h0
    have hz : b2.eval b * psi3.eval b = 0 := by
      linear_combination h0
    exact (mul_eq_zero.mp hz).resolve_left hb2b
  have hLpsi : (X - C b : k[X]) ∣ psi3 := by
    rw [dvd_iff_isRoot]
    exact hpsi3b
  obtain ⟨psi4, hpsi4⟩ := hLpsi
  have hquart : phi1 = (X - C b) ^ 4 * psi4 := by
    rw [hcube, hpsi4]
    ring
  refine ⟨hpsi3b, ?_, psi4, hquart⟩
  have hddd := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval b) hquart
  simp only [derivative_add, derivative_mul, derivative_pow,
    derivative_sub, derivative_X, derivative_C, derivative_one, sub_zero,
    one_mul, mul_one, pow_one, eval_add, eval_sub, eval_mul, eval_pow,
    eval_one, eval_X, eval_C, sub_self, zero_mul, mul_zero, zero_add,
    add_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    at hddd
  linear_combination hddd

end MixedSixthRowAlgebra68

section MixedSixthRowSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Sixth-row refinement of the preserved transverse two-root allocation.
The shared level gains the second-order kill `b₂''(a) = 0` from the
retained `I₄` row.  The `k₁ = H k₂` limb consumes the second coefficient
of its reduced terminal row at the `r`-root, which then collapses to the
exact product face `d₂''(a) k₂(a) = 0`.  The `b₂ = H b₃` limb backwires
the shared jet to `b₃'(a) = 0`, inherited by both divisibility
sub-limbs.  The transverse residual consumes the third coefficient of
its reduced `I₄` row at `b`: the cube of the local linear factor cancels
exactly and `b₂(b) ≠ 0` forces `ψ₃(b) = 0`, so `Φ₁'''(b) = 0` and the
exact cube deepens to the exact fourth power `Φ₁ = (X - b)⁴ ψ₄`.  The
`H ∣ r` and `H ∣ Φ₁` siblings pass through untouched. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneMixedSixthRowPacket
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
           b2.derivative.derivative.eval a = 0 ∧
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
                   d2.eval b * k2.derivative.eval b) = 0 ∧
               d2.derivative.derivative.eval a * k2.eval a = 0) ∨
            (d2.eval b = 0 ∧ b2.eval b = 0 ∧ ∃ b3 e1 : k[X],
               b2 = H * b3 ∧ d2 = H * e1 ∧
               b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0 ∧
               e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3 ∧
               b3.eval a = 0 ∧ e1.eval a = 0 ∧
               b3.derivative.eval a = 0 ∧
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
               phi1.derivative.derivative.derivative.eval b = 0 ∧
               ∃ e2 psi4 : k[X], d2 = H ^ 2 * e2 ∧
                 phi1 = (Polynomial.X - C b) ^ 4 * psi4 ∧
                 b2 * phi1 + (6 : k[X]) * H ^ 3 * w2 * e2 = 0 ∧
                 b2 * w2 * eDot - H * e2 * k1 = C j * H ^ 3 ∧
                 b2.eval b * w2.derivative.eval b * eDot.eval b =
                   H.derivative.eval b * e2.eval b * k1.eval b)))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, hsplit⟩ :=
    S.terminalAfterLowerOneMixedFifthRowPacket (H := H) hdeg hp hq hp6
      hq8 haligned hjac hj
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  rcases hsplit with hr | hphi | hmix
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inl hr⟩
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inr (Or.inl hphi)⟩
  · obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hb2a, hk1a, hd2a,
      hb2da, hd2da, hI4faceB, hrowFaceB, hfaceB, hpinB, htri⟩ := hmix
    -- Shared sixth-row jet: the second coefficient of the retained `I₄`
    -- row at the `r`-root kills `b₂''(a)` outright.
    have hb2dda : b2.derivative.derivative.eval a = 0 :=
      mixedIFourSecondCoefficient_68 H b2 phi1 w2 d2 a ha hpa hb2a hb2da
        hd2a hd2da hI4
    refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow,
      Or.inr (Or.inr ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hb2a, hk1a,
        hd2a, hb2da, hd2da, hb2dda, hI4faceB, hrowFaceB, hfaceB, hpinB,
        ?_⟩)⟩
    rcases htri with ⟨hk1b, k2, hk2, hk2row, hk2face⟩ |
      ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red, he1row, hb3a, he1a,
        hsub⟩ |
      ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db, hphi1ddb, e2, psi3,
        hd2sq, hcube, hI4red, hrowRed, hface⟩
    · -- `k₁` limb: second coefficient of the reduced terminal row at `a`.
      exact Or.inl ⟨hk1b, k2, hk2, hk2row, hk2face,
        mixedReducedTerminalSecondCoefficient_68 H b2 w2 _ d2 k2 j a ha
          hb2a hb2da hb2dda hd2a hd2da hk2row⟩
    · -- `b₂` limb: the shared jet backwires to `b₃'(a) = 0`.
      have hb3da : b3.derivative.eval a = 0 :=
        quotientDerivEvalZero_of_secondDerivativeZero_68 H b2 b3 a ha
          (hsimple a ha) hb2b3 hb3a hb2dda
      exact Or.inr (Or.inl ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red,
        he1row, hb3a, he1a, hb3da, hsub⟩)
    · -- Transverse residual: third coefficient of the reduced `I₄` row.
      obtain ⟨hpsi3b, hphi1dddb, psi4, hquart⟩ :=
        mixedReducedIFourQuartic_68 H b2 phi1 w2 e2 psi3 b hb hb2b hw2b
          hcube hI4red
      exact Or.inr (Or.inr ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db,
        hphi1ddb, hphi1dddb, e2, psi4, hd2sq, hquart, hI4red, hrowRed,
        hface⟩)

end MixedSixthRowSource68

end Max11DegreeRoutes
