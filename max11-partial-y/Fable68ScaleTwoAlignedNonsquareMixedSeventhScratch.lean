import Fable68ScaleTwoAlignedNonsquareMixedSixthScratch

/-! # Seventh row of the preserved transverse two-root allocation

The sixth-row packet leaves three refined children at the `Φ₁`-root `b`
of the transverse allocation, and each of them again owns exactly one
unconsumed low-order Taylor coefficient.  This file consumes precisely
that coefficient in each limb.

In the `k₁ = H k₂` limb the third coefficient of the reduced terminal
row `b₂ w₂ Ė - d₂ k₂ = j H³` at the `r`-root is the first `j`-loaded
face of the limb: the retained triple zero of `b₂` and double zero of
`d₂` collapse it to the exact face
`b₂'''(a) w₂(a) Ė(a) - d₂'''(a) k₂(a) - 3 d₂''(a) k₂'(a) = 6 j H'(a)³`,
whose right-hand side is a unit because `j ≠ 0` and the core root is
simple.  In the `b₂ = H b₃` limb the second coefficient of the retained
`e₁`-row `e₁ k₁ = H b₃ w₂ Ė - j H³` at the `r`-root is exact: the
sixth-row gain `b₃'(a) = 0` promotes the `H b₃` block to a triple zero
at `a`, every load on the right dies, and the row collapses to the
product face `e₁'(a) k₁'(a) = 0`, inherited by both divisibility
sub-limbs.  In the transverse residual the second coefficient of the
reduced terminal row `b₂ w₂ Ė - H e₂ k₁ = j H³` at `b` is the first
face loading `w₂''(b)`, `e₂'(b)` and `k₁'(b)`:
`2 b₂' w₂' Ė + b₂ w₂'' Ė + 2 b₂ w₂' Ė'` ties to
`H'' e₂ k₁ + 2 H' e₂' k₁ + 2 H' e₂ k₁'` at `b`.  No honest
contradiction is available in any limb — the `j`-loaded face admits the
witness `d₂'''(a) k₂(a) = -6 j H'(a)³`, and the witnesses carry no
degree bounds in the retained interface — so all three children are
returned refined and the `H ∣ r`, `H ∣ Φ₁` siblings pass through
untouched. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section MixedSeventhRowAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Third Taylor coefficient of the reduced terminal row at the
`r`-root carried by the `k₁ = H k₂` limb: on the retained triple zero
of `b₂` and double zero of `d₂` it is the first `j`-loaded face of the
limb, `b₂'''(a) w₂(a) Ė(a) - d₂'''(a) k₂(a) - 3 d₂''(a) k₂'(a)
= 6 j H'(a)³`. -/
theorem mixedReducedTerminalThirdCoefficient_68
    (H b2 w2 eDot d2 k2 : k[X]) (j a : k) (ha : H.eval a = 0)
    (hb2a : b2.eval a = 0) (hb2da : b2.derivative.eval a = 0)
    (hb2dda : b2.derivative.derivative.eval a = 0)
    (hd2a : d2.eval a = 0) (hd2da : d2.derivative.eval a = 0)
    (hrow : b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) :
    b2.derivative.derivative.derivative.eval a * w2.eval a *
        eDot.eval a -
        (d2.derivative.derivative.derivative.eval a * k2.eval a +
          3 * d2.derivative.derivative.eval a * k2.derivative.eval a) =
      6 * j * H.derivative.eval a ^ 3 := by
  have hddd := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval a) hrow
  simp only [derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, ha, hb2a, hb2da, hb2dda, hd2a, hd2da, pow_one,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub,
    zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at hddd
  first
    | linear_combination hddd
    | linear_combination -hddd

/-- Second Taylor coefficient at the `r`-root of the `e₁`-row carried
by the `b₂ = H b₃` limb: through the sixth-row gain `b₃'(a) = 0` the
`H b₃` block carries a triple zero at `a`, every right-hand load dies,
and the row is the exact product face `e₁'(a) k₁'(a) = 0`. -/
theorem mixedEOneRowSecondCoefficient_68
    (H b3 w2 eDot e1 k1 : k[X]) (j a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (he1a : e1.eval a = 0) (hk1a : k1.eval a = 0)
    (hrow : e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3) :
    e1.derivative.eval a * k1.derivative.eval a = 0 := by
  have hdd := congrArg
    (fun P : k[X] => P.derivative.derivative.eval a) hrow
  simp only [derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, ha, hb3a, hb3da, he1a, hk1a, pow_one, zero_mul,
    mul_zero, zero_add, add_zero, sub_zero, zero_sub, neg_zero,
    zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at hdd
  first
    | linear_combination (1 / 2 : k) * hdd
    | linear_combination (-1 / 2 : k) * hdd
    | linear_combination hdd
    | linear_combination -hdd

/-- Second Taylor coefficient at the `Φ₁`-root of the reduced terminal
row carried by the transverse residual: with `w₂(b) = 0` and the simple
core zero it ties the second-order data
`2 b₂'(b) w₂'(b) Ė(b) + b₂(b) w₂''(b) Ė(b) + 2 b₂(b) w₂'(b) Ė'(b)` to
`H''(b) e₂(b) k₁(b) + 2 H'(b) e₂'(b) k₁(b) + 2 H'(b) e₂(b) k₁'(b)`,
the first face loading `w₂''(b)`, `e₂'(b)` and `k₁'(b)`. -/
theorem mixedResidualTerminalSecondCoefficient_68
    (H b2 w2 eDot e2 k1 : k[X]) (j b : k) (hb : H.eval b = 0)
    (hw2b : w2.eval b = 0)
    (hrow : b2 * w2 * eDot - H * e2 * k1 = C j * H ^ 3) :
    2 * b2.derivative.eval b * w2.derivative.eval b * eDot.eval b +
        b2.eval b * w2.derivative.derivative.eval b * eDot.eval b +
        2 * b2.eval b * w2.derivative.eval b *
          eDot.derivative.eval b =
      H.derivative.derivative.eval b * e2.eval b * k1.eval b +
        2 * H.derivative.eval b * e2.derivative.eval b * k1.eval b +
        2 * H.derivative.eval b * e2.eval b *
          k1.derivative.eval b := by
  have hdd := congrArg
    (fun P : k[X] => P.derivative.derivative.eval b) hrow
  simp only [derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, hb, hw2b, pow_one, zero_mul, mul_zero, zero_add,
    add_zero, sub_zero, zero_sub, neg_zero, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true] at hdd
  first
    | linear_combination hdd
    | linear_combination -hdd

end MixedSeventhRowAlgebra68

section MixedSeventhRowSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Seventh-row refinement of the preserved transverse two-root
allocation.  The `k₁ = H k₂` limb consumes the third coefficient of its
reduced terminal row at the `r`-root, the first `j`-loaded face of the
limb: `b₂'''(a) w₂(a) Ė(a) - d₂'''(a) k₂(a) - 3 d₂''(a) k₂'(a)
= 6 j H'(a)³` with unit right-hand side.  The `b₂ = H b₃` limb consumes
the second coefficient of its retained `e₁`-row at the `r`-root, the
exact product face `e₁'(a) k₁'(a) = 0`, inherited by both divisibility
sub-limbs.  The transverse residual consumes the second coefficient of
its reduced terminal row at `b`, the first face loading `w₂''(b)`,
`e₂'(b)` and `k₁'(b)`.  No limb closes — the `j`-loaded face is
satisfiable and the witnesses carry no degree bounds — so all three
children are returned refined and the `H ∣ r`, `H ∣ Φ₁` siblings pass
through untouched. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneMixedSeventhRowPacket
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
               d2.derivative.derivative.eval a * k2.eval a = 0 ∧
               b2.derivative.derivative.derivative.eval a * w2.eval a *
                   eDot.eval a -
                   (d2.derivative.derivative.derivative.eval a *
                       k2.eval a +
                     3 * d2.derivative.derivative.eval a *
                       k2.derivative.eval a) =
                 6 * j * H.derivative.eval a ^ 3) ∨
            (d2.eval b = 0 ∧ b2.eval b = 0 ∧ ∃ b3 e1 : k[X],
               b2 = H * b3 ∧ d2 = H * e1 ∧
               b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0 ∧
               e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3 ∧
               b3.eval a = 0 ∧ e1.eval a = 0 ∧
               b3.derivative.eval a = 0 ∧
               e1.derivative.eval a * k1.derivative.eval a = 0 ∧
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
                   H.derivative.eval b * e2.eval b * k1.eval b ∧
                 2 * b2.derivative.eval b * w2.derivative.eval b *
                       eDot.eval b +
                     b2.eval b * w2.derivative.derivative.eval b *
                       eDot.eval b +
                     2 * b2.eval b * w2.derivative.eval b *
                       eDot.derivative.eval b =
                   H.derivative.derivative.eval b * e2.eval b *
                       k1.eval b +
                     2 * H.derivative.eval b * e2.derivative.eval b *
                       k1.eval b +
                     2 * H.derivative.eval b * e2.eval b *
                       k1.derivative.eval b)))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, hsplit⟩ :=
    S.terminalAfterLowerOneMixedSixthRowPacket (H := H) hdeg hp hq hp6
      hq8 haligned hjac hj
  rcases hsplit with hr | hphi | hmix
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inl hr⟩
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inr (Or.inl hphi)⟩
  · obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hb2a, hk1a, hd2a,
      hb2da, hd2da, hb2dda, hI4faceB, hrowFaceB, hfaceB, hpinB,
      htri⟩ := hmix
    refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow,
      Or.inr (Or.inr ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hb2a,
        hk1a, hd2a, hb2da, hd2da, hb2dda, hI4faceB, hrowFaceB, hfaceB,
        hpinB, ?_⟩)⟩
    rcases htri with ⟨hk1b, k2, hk2, hk2row, hk2faceB, hk2facea⟩ |
      ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red, he1row, hb3a, he1a,
        hb3da, hsub⟩ |
      ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db, hphi1ddb, hphi1dddb,
        e2, psi4, hd2sq, hquart, hI4red, hrowRed, htie⟩
    · -- `k₁` limb: third coefficient of the reduced terminal row
      -- at `a`, the first `j`-loaded face of the limb.
      exact Or.inl ⟨hk1b, k2, hk2, hk2row, hk2faceB, hk2facea,
        mixedReducedTerminalThirdCoefficient_68 H b2 w2 _ d2 k2 j a ha
          hb2a hb2da hb2dda hd2a hd2da hk2row⟩
    · -- `b₂` limb: second coefficient of the `e₁`-row at `a`, the
      -- exact product face `e₁'(a) k₁'(a) = 0`.
      exact Or.inr (Or.inl ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red,
        he1row, hb3a, he1a, hb3da,
        mixedEOneRowSecondCoefficient_68 H b3 w2 _ e1 k1 j a ha hb3a
          hb3da he1a hk1a he1row,
        hsub⟩)
    · -- Residual: second coefficient of the reduced terminal row
      -- at `b`.
      exact Or.inr (Or.inr ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db,
        hphi1ddb, hphi1dddb, e2, psi4, hd2sq, hquart, hI4red, hrowRed,
        htie,
        mixedResidualTerminalSecondCoefficient_68 H b2 w2 _ e2 k1 j b
          hb hw2b hrowRed⟩)

end MixedSeventhRowSource68

end Max11DegreeRoutes
