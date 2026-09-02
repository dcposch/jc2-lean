import Fable68ScaleTwoAlignedNonsquareMixedSeventhScratch

/-! # Eighth row of the preserved transverse two-root allocation

The seventh-row packet leaves three refined children at the `Φ₁`-root
`b` of the transverse allocation.  This file consumes the next unused
Taylor coefficient in each limb and, in the `b₂ = H b₃` limb, resolves
the retained product face `e₁'(a) k₁'(a) = 0` into an exclusive
allocation dichotomy.

In the `b₂ = H b₃` limb two fresh rows are consumed at the `r`-root:
the second coefficient of the reduced `I₄` row
`b₃ Φ₁ + 6 H w₂ e₁ = 0`, which is the exact tie
`b₃''(a) Φ₁(a) + 12 H'(a) w₂(a) e₁'(a) = 0`, and the third coefficient
of the retained `e₁`-row `e₁ k₁ = H b₃ w₂ Ė - j H³`, the second
`j`-loaded face of the lane,
`e₁''(a) k₁'(a) + e₁'(a) k₁''(a)
  = H'(a) b₃''(a) w₂(a) Ė(a) - 2 j H'(a)³`.
Fed into the retained allocation `e₁'(a) k₁'(a) = 0` they force an
exclusive dichotomy.  If `e₁'(a) = 0` the `I₄` tie collapses to
`b₃''(a) Φ₁(a) = 0` and the unit `Φ₁(a)` kills `b₃''(a)` outright, the
divisibilities deepen the retained jets to `d₂''(a) = 0` and
`b₂'''(a) = 0`, and the `j`-loaded row collapses to the unit pin
`e₁''(a) k₁'(a) + 2 j H'(a)³ = 0`, so `k₁'(a) ≠ 0` and `e₁''(a) ≠ 0`
definitely.  If instead `k₁'(a) = 0`, eliminating `b₃''(a)` between the
two rows through the unit `Φ₁(a)` leaves
`e₁'(a) (k₁''(a) Φ₁(a) + 12 H'(a)² w₂(a)² Ė(a))
  + 2 j H'(a)³ Φ₁(a) = 0`
with unit load, so `e₁'(a) ≠ 0` definitely and the two branches are
mutually exclusive.  In the `k₁ = H k₂` limb the second coefficient of
the reduced terminal row `b₂ w₂ Ė - d₂ k₂ = j H³` at `b` is consumed:
the cube of the core kills the right-hand side and the row is the full
second-order tie, the first face loading `b₂''(b)`, `w₂''(b)`,
`Ė''(b)`, `d₂''(b)` and `k₂''(b)`.  In the transverse residual the
third coefficient of the reduced terminal row `b₂ w₂ Ė - H e₂ k₁ = j H³`
at `b` is the first `j`-loaded face of the residual limb, tying the
third-order data at `b` to the unit `6 j H'(b)³` and first loading
`w₂'''(b)`, `e₂''(b)` and `k₁''(b)`.  No honest contradiction is
available in any limb — the unit pins are satisfiable and the witnesses
carry no degree bounds in the retained interface — so all three
children are returned refined and the `H ∣ r`, `H ∣ Φ₁` siblings pass
through untouched. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

section MixedEighthRowAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Second Taylor coefficient of the reduced `I₄` row at the `r`-root
carried by the `b₂ = H b₃` limb: on the retained double zero of `b₃`
and simple zero of `e₁` it is the exact tie
`b₃''(a) Φ₁(a) + 12 H'(a) w₂(a) e₁'(a) = 0`. -/
theorem mixedReducedIFourSecondCoefficient_68
    (H b3 phi1 w2 e1 : k[X]) (a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (he1a : e1.eval a = 0)
    (hI4red : b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0) :
    b3.derivative.derivative.eval a * phi1.eval a +
      12 * H.derivative.eval a * w2.eval a * e1.derivative.eval a
        = 0 := by
  have hdd := congrArg
    (fun P : k[X] => P.derivative.derivative.eval a) hI4red
  simp only [derivative_add, derivative_mul, derivative_ofNat,
    derivative_zero, eval_add, eval_mul, eval_ofNat, eval_zero, ha,
    hb3a, hb3da, he1a, zero_mul, mul_zero, zero_add, add_zero] at hdd
  first
    | linear_combination hdd
    | linear_combination -hdd

/-- Third Taylor coefficient at the `r`-root of the `e₁`-row carried by
the `b₂ = H b₃` limb: through the retained double zero of `b₃` the
`H b₃` block carries a triple zero at `a` and the row is the second
`j`-loaded face of the lane, `e₁''(a) k₁'(a) + e₁'(a) k₁''(a)
= H'(a) b₃''(a) w₂(a) Ė(a) - 2 j H'(a)³`. -/
theorem mixedEOneRowThirdCoefficient_68
    (H b3 w2 eDot e1 k1 : k[X]) (j a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (he1a : e1.eval a = 0) (hk1a : k1.eval a = 0)
    (hrow : e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3) :
    e1.derivative.derivative.eval a * k1.derivative.eval a +
        e1.derivative.eval a * k1.derivative.derivative.eval a =
      H.derivative.eval a * b3.derivative.derivative.eval a *
          w2.eval a * eDot.eval a -
        2 * j * H.derivative.eval a ^ 3 := by
  have hddd := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval a) hrow
  simp only [derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, ha, hb3a, hb3da, he1a, hk1a, pow_one, zero_mul,
    mul_zero, zero_add, add_zero, sub_zero, zero_sub, neg_zero,
    zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at hddd
  first
    | linear_combination (1 / 3 : k) * hddd
    | linear_combination (-1 / 3 : k) * hddd
    | linear_combination hddd
    | linear_combination -hddd

/-- At a core root, a first-order zero of the quotient makes the
second derivative of the once-divided product vanish. -/
theorem productSecondDerivativeEvalZero_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hQa : Q.eval a = 0)
    (hQda : Q.derivative.eval a = 0) (hPQ : P = H * Q) :
    P.derivative.derivative.eval a = 0 := by
  have hdd := congrArg
    (fun R : k[X] => R.derivative.derivative.eval a) hPQ
  simp only [derivative_add, derivative_mul, eval_add, eval_mul, ha,
    hQa, hQda, zero_mul, mul_zero, add_zero, zero_add] at hdd
  first
    | exact hdd
    | linear_combination hdd

/-- At a core root, a second-order zero of the quotient makes the
third derivative of the once-divided product vanish. -/
theorem productThirdDerivativeEvalZero_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hQa : Q.eval a = 0)
    (hQda : Q.derivative.eval a = 0)
    (hQdda : Q.derivative.derivative.eval a = 0) (hPQ : P = H * Q) :
    P.derivative.derivative.derivative.eval a = 0 := by
  have hddd := congrArg
    (fun R : k[X] => R.derivative.derivative.derivative.eval a) hPQ
  simp only [derivative_add, derivative_mul, eval_add, eval_mul, ha,
    hQa, hQda, hQdda, zero_mul, mul_zero, add_zero, zero_add] at hddd
  first
    | exact hddd
    | linear_combination hddd

/-- Exclusive resolution of the retained allocation
`e₁'(a) k₁'(a) = 0` against the reduced-`I₄` order-two tie and the
`j`-loaded `e₁`-row order-three face.  On `e₁'(a) = 0` the unit
`Φ₁(a)` kills `b₃''(a)` and the `j`-loaded face becomes the unit pin
`e₁''(a) k₁'(a) + 2 j H'(a)³ = 0`, so `k₁'(a)` and `e₁''(a)` are
units.  On `k₁'(a) = 0` the elimination of `b₃''(a)` through `Φ₁(a)`
pins `e₁'(a)` against a unit, so `e₁'(a) ≠ 0`. -/
theorem mixedEOneRowAllocationSplit_68
    {phia Hda w2a eDa e1d e1dd k1d k1dd b3dd j : k}
    (hpa : phia ≠ 0) (hj : j ≠ 0) (hHda : Hda ≠ 0)
    (hA : b3dd * phia + 12 * Hda * w2a * e1d = 0)
    (hB : e1dd * k1d + e1d * k1dd =
      Hda * b3dd * w2a * eDa - 2 * j * Hda ^ 3)
    (hface : e1d * k1d = 0) :
    (e1d = 0 ∧ b3dd = 0 ∧ k1d ≠ 0 ∧ e1dd ≠ 0 ∧
      e1dd * k1d + 2 * j * Hda ^ 3 = 0) ∨
    (k1d = 0 ∧ e1d ≠ 0 ∧
      e1d * (k1dd * phia + 12 * Hda ^ 2 * w2a ^ 2 * eDa) +
        2 * j * Hda ^ 3 * phia = 0) := by
  have h2 : (2 : k) ≠ 0 := by norm_num
  have hunit : 2 * j * Hda ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2 hj) (pow_ne_zero 3 hHda)
  rcases mul_eq_zero.mp hface with he1d | hk1d
  · have hb3dd : b3dd = 0 := by
      have hz : b3dd * phia = 0 := by
        first
          | linear_combination hA - 12 * Hda * w2a * he1d
          | linear_combination hA + 12 * Hda * w2a * he1d
      exact (mul_eq_zero.mp hz).resolve_right hpa
    have hpin : e1dd * k1d + 2 * j * Hda ^ 3 = 0 := by
      first
        | linear_combination hB - k1dd * he1d + Hda * w2a * eDa * hb3dd
        | linear_combination hB + k1dd * he1d - Hda * w2a * eDa * hb3dd
        | linear_combination -hB - k1dd * he1d + Hda * w2a * eDa * hb3dd
    have hk1dne : k1d ≠ 0 := by
      intro h
      exact hunit (by linear_combination hpin - e1dd * h)
    have he1ddne : e1dd ≠ 0 := by
      intro h
      exact hunit (by linear_combination hpin - k1d * h)
    exact Or.inl ⟨he1d, hb3dd, hk1dne, he1ddne, hpin⟩
  · have hpin2 : e1d * (k1dd * phia + 12 * Hda ^ 2 * w2a ^ 2 * eDa) +
        2 * j * Hda ^ 3 * phia = 0 := by
      first
        | linear_combination phia * hB + Hda * w2a * eDa * hA -
            e1dd * phia * hk1d
        | linear_combination phia * hB - Hda * w2a * eDa * hA -
            e1dd * phia * hk1d
        | linear_combination -phia * hB + Hda * w2a * eDa * hA -
            e1dd * phia * hk1d
    have hunit2 : 2 * j * Hda ^ 3 * phia ≠ 0 :=
      mul_ne_zero hunit hpa
    have he1dne : e1d ≠ 0 := by
      intro h
      exact hunit2 (by linear_combination hpin2 -
        (k1dd * phia + 12 * Hda ^ 2 * w2a ^ 2 * eDa) * h)
    exact Or.inr ⟨hk1d, he1dne, hpin2⟩

/-- Second Taylor coefficient at the `Φ₁`-root of the reduced terminal
row carried by the `k₁ = H k₂` limb: the cube of the core kills the
right-hand side and the row is the full second-order tie, the first
face loading `b₂''(b)`, `w₂''(b)`, `Ė''(b)`, `d₂''(b)` and
`k₂''(b)`. -/
theorem mixedKTwoRowSecondCoefficient_68
    (H b2 w2 eDot d2 k2 : k[X]) (j b : k) (hb : H.eval b = 0)
    (hrow : b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) :
    b2.derivative.derivative.eval b * w2.eval b * eDot.eval b +
        2 * b2.derivative.eval b * w2.derivative.eval b *
          eDot.eval b +
        2 * b2.derivative.eval b * w2.eval b *
          eDot.derivative.eval b +
        b2.eval b * w2.derivative.derivative.eval b * eDot.eval b +
        2 * b2.eval b * w2.derivative.eval b *
          eDot.derivative.eval b +
        b2.eval b * w2.eval b * eDot.derivative.derivative.eval b -
        (d2.derivative.derivative.eval b * k2.eval b +
          2 * d2.derivative.eval b * k2.derivative.eval b +
          d2.eval b * k2.derivative.derivative.eval b) = 0 := by
  have hdd := congrArg
    (fun P : k[X] => P.derivative.derivative.eval b) hrow
  simp only [derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, hb, pow_one, zero_mul, mul_zero, zero_add,
    add_zero, sub_zero, zero_sub, neg_zero, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true] at hdd
  first
    | linear_combination hdd
    | linear_combination -hdd

/-- Third Taylor coefficient at the `Φ₁`-root of the reduced terminal
row carried by the transverse residual: with `w₂(b) = 0` it is the
first `j`-loaded face of the limb, tying the third-order data at `b`
to the unit `6 j H'(b)³` and first loading `w₂'''(b)`, `e₂''(b)` and
`k₁''(b)`. -/
theorem mixedResidualTerminalThirdCoefficient_68
    (H b2 w2 eDot e2 k1 : k[X]) (j b : k) (hb : H.eval b = 0)
    (hw2b : w2.eval b = 0)
    (hrow : b2 * w2 * eDot - H * e2 * k1 = C j * H ^ 3) :
    3 * b2.derivative.derivative.eval b * w2.derivative.eval b *
          eDot.eval b +
        3 * b2.derivative.eval b * w2.derivative.derivative.eval b *
          eDot.eval b +
        b2.eval b * w2.derivative.derivative.derivative.eval b *
          eDot.eval b +
        6 * b2.derivative.eval b * w2.derivative.eval b *
          eDot.derivative.eval b +
        3 * b2.eval b * w2.derivative.derivative.eval b *
          eDot.derivative.eval b +
        3 * b2.eval b * w2.derivative.eval b *
          eDot.derivative.derivative.eval b =
      H.derivative.derivative.derivative.eval b * e2.eval b *
          k1.eval b +
        3 * H.derivative.derivative.eval b * e2.derivative.eval b *
          k1.eval b +
        3 * H.derivative.derivative.eval b * e2.eval b *
          k1.derivative.eval b +
        3 * H.derivative.eval b * e2.derivative.derivative.eval b *
          k1.eval b +
        6 * H.derivative.eval b * e2.derivative.eval b *
          k1.derivative.eval b +
        3 * H.derivative.eval b * e2.eval b *
          k1.derivative.derivative.eval b +
        6 * j * H.derivative.eval b ^ 3 := by
  have hddd := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval b) hrow
  simp only [derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, hb, hw2b, pow_one, zero_mul, mul_zero, zero_add,
    add_zero, sub_zero, zero_sub, neg_zero, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true] at hddd
  first
    | linear_combination hddd
    | linear_combination -hddd

end MixedEighthRowAlgebra68

section MixedEighthRowSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Eighth-row refinement of the preserved transverse two-root
allocation.  The `b₂ = H b₃` limb consumes the second coefficient of
its reduced `I₄` row and the third, `j`-loaded coefficient of its
`e₁`-row at the `r`-root and resolves the retained allocation
`e₁'(a) k₁'(a) = 0` into an exclusive dichotomy: either `e₁'(a) = 0`
with `b₃''(a) = 0`, deepened jets `d₂''(a) = 0`, `b₂'''(a) = 0`, and
the unit pin `e₁''(a) k₁'(a) + 2 j H'(a)³ = 0` forcing `k₁'(a) ≠ 0`
and `e₁''(a) ≠ 0`, or `k₁'(a) = 0` with the retained `I₄` tie and the
`Φ₁`-eliminated unit pin forcing `e₁'(a) ≠ 0`.  The `k₁ = H k₂` limb
consumes the second coefficient of its reduced terminal row at `b`,
the full second-order tie.  The transverse residual consumes the third
coefficient of its reduced terminal row at `b`, the first `j`-loaded
face of the limb with unit right-hand side `6 j H'(b)³`.  No limb
closes — the unit pins are satisfiable and the witnesses carry no
degree bounds — so all three children are returned refined and the
`H ∣ r`, `H ∣ Φ₁` siblings pass through untouched. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneMixedEighthRowPacket
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
                 6 * j * H.derivative.eval a ^ 3 ∧
               b2.derivative.derivative.eval b * w2.eval b *
                     eDot.eval b +
                   2 * b2.derivative.eval b * w2.derivative.eval b *
                     eDot.eval b +
                   2 * b2.derivative.eval b * w2.eval b *
                     eDot.derivative.eval b +
                   b2.eval b * w2.derivative.derivative.eval b *
                     eDot.eval b +
                   2 * b2.eval b * w2.derivative.eval b *
                     eDot.derivative.eval b +
                   b2.eval b * w2.eval b *
                     eDot.derivative.derivative.eval b -
                   (d2.derivative.derivative.eval b * k2.eval b +
                     2 * d2.derivative.eval b *
                       k2.derivative.eval b +
                     d2.eval b * k2.derivative.derivative.eval b)
                     = 0) ∨
            (d2.eval b = 0 ∧ b2.eval b = 0 ∧ ∃ b3 e1 : k[X],
               b2 = H * b3 ∧ d2 = H * e1 ∧
               b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0 ∧
               e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3 ∧
               b3.eval a = 0 ∧ e1.eval a = 0 ∧
               b3.derivative.eval a = 0 ∧
               e1.derivative.eval a * k1.derivative.eval a = 0 ∧
               ((e1.derivative.eval a = 0 ∧
                   b3.derivative.derivative.eval a = 0 ∧
                   d2.derivative.derivative.eval a = 0 ∧
                   b2.derivative.derivative.derivative.eval a = 0 ∧
                   k1.derivative.eval a ≠ 0 ∧
                   e1.derivative.derivative.eval a ≠ 0 ∧
                   e1.derivative.derivative.eval a *
                       k1.derivative.eval a +
                     2 * j * H.derivative.eval a ^ 3 = 0) ∨
                 (k1.derivative.eval a = 0 ∧
                   e1.derivative.eval a ≠ 0 ∧
                   b3.derivative.derivative.eval a * phi1.eval a +
                     12 * H.derivative.eval a * w2.eval a *
                       e1.derivative.eval a = 0 ∧
                   e1.derivative.eval a *
                       (k1.derivative.derivative.eval a *
                           phi1.eval a +
                         12 * H.derivative.eval a ^ 2 *
                           w2.eval a ^ 2 * eDot.eval a) +
                     2 * j * H.derivative.eval a ^ 3 * phi1.eval a
                       = 0)) ∧
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
                       k1.derivative.eval b ∧
                 3 * b2.derivative.derivative.eval b *
                       w2.derivative.eval b * eDot.eval b +
                     3 * b2.derivative.eval b *
                       w2.derivative.derivative.eval b *
                       eDot.eval b +
                     b2.eval b *
                       w2.derivative.derivative.derivative.eval b *
                       eDot.eval b +
                     6 * b2.derivative.eval b * w2.derivative.eval b *
                       eDot.derivative.eval b +
                     3 * b2.eval b * w2.derivative.derivative.eval b *
                       eDot.derivative.eval b +
                     3 * b2.eval b * w2.derivative.eval b *
                       eDot.derivative.derivative.eval b =
                   H.derivative.derivative.derivative.eval b *
                       e2.eval b * k1.eval b +
                     3 * H.derivative.derivative.eval b *
                       e2.derivative.eval b * k1.eval b +
                     3 * H.derivative.derivative.eval b * e2.eval b *
                       k1.derivative.eval b +
                     3 * H.derivative.eval b *
                       e2.derivative.derivative.eval b * k1.eval b +
                     6 * H.derivative.eval b * e2.derivative.eval b *
                       k1.derivative.eval b +
                     3 * H.derivative.eval b * e2.eval b *
                       k1.derivative.derivative.eval b +
                     6 * j * H.derivative.eval b ^ 3)))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, hsplit⟩ :=
    S.terminalAfterLowerOneMixedSeventhRowPacket (H := H) hdeg hp hq
      hp6 hq8 haligned hjac hj
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
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
    rcases htri with ⟨hk1b, k2, hk2, hk2row, hk2faceB, hk2facea,
      hk2jet⟩ |
      ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red, he1row, hb3a, he1a,
        hb3da, hfaceProd, hsub⟩ |
      ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db, hphi1ddb, hphi1dddb,
        e2, psi4, hd2sq, hquart, hI4red, hrowRed, htie, htie2⟩
    · -- `k₁` limb: second coefficient of the reduced terminal row
      -- at `b`, the full second-order tie.
      exact Or.inl ⟨hk1b, k2, hk2, hk2row, hk2faceB, hk2facea, hk2jet,
        mixedKTwoRowSecondCoefficient_68 H b2 w2 _ d2 k2 j b hb
          hk2row⟩
    · -- `b₂` limb: reduced-`I₄` order two and the `j`-loaded
      -- `e₁`-row order three resolve the retained allocation into
      -- the exclusive dichotomy.
      have hHda : H.derivative.eval a ≠ 0 := hsimple a ha
      have hA := mixedReducedIFourSecondCoefficient_68 H b3 phi1 w2 e1
        a ha hb3a hb3da he1a hI4red
      have hB := mixedEOneRowThirdCoefficient_68 H b3 w2 _ e1 k1 j a
        ha hb3a hb3da he1a hk1a he1row
      refine Or.inr (Or.inl ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red,
        he1row, hb3a, he1a, hb3da, hfaceProd, ?_, hsub⟩)
      rcases mixedEOneRowAllocationSplit_68 hpa hj hHda hA hB
        hfaceProd with
        ⟨he1d, hb3dd, hk1dne, he1ddne, hpin⟩ | ⟨hk1d, he1dne, hpin2⟩
      · exact Or.inl ⟨he1d, hb3dd,
          productSecondDerivativeEvalZero_68 H e1 d2 a ha he1a he1d
            hd2e1,
          productThirdDerivativeEvalZero_68 H b3 b2 a ha hb3a hb3da
            hb3dd hb2b3,
          hk1dne, he1ddne, hpin⟩
      · exact Or.inr ⟨hk1d, he1dne, hA, hpin2⟩
    · -- Residual: third coefficient of the reduced terminal row at
      -- `b`, the first `j`-loaded face of the limb.
      exact Or.inr (Or.inr ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db,
        hphi1ddb, hphi1dddb, e2, psi4, hd2sq, hquart, hI4red, hrowRed,
        htie, htie2,
        mixedResidualTerminalThirdCoefficient_68 H b2 w2 _ e2 k1 j b
          hb hw2b hrowRed⟩)

end MixedEighthRowSource68

end Max11DegreeRoutes
