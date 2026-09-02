import Fable68ScaleTwoAlignedNonsquareMixedEighthScratch

/-! # Ninth row of the preserved transverse two-root allocation

The eighth-row packet leaves three refined children at the `Φ₁`-root
`b` of the transverse allocation, with the `b₂ = H b₃` limb resolved
into an exclusive `e₁'(a) = 0` / `k₁'(a) = 0` dichotomy carrying unit
pins.  This file advances each child by its next genuinely independent
Taylor coefficient and, in the dichotomy, exploits the fresh unit pins
and the deepened jets before any further rows are added.

In the `b₂ = H b₃` limb the third coefficient of the reduced `I₄` row
`b₃ Φ₁ + 6 H w₂ e₁ = 0` at the `r`-root is consumed in both branches.
On the `e₁'(a) = 0` branch the deepened jets `b₃''(a) = 0` and
`e₁'(a) = 0` collapse it to the exact tie
`b₃'''(a) Φ₁(a) + 18 H'(a) w₂(a) e₁''(a) = 0`; eliminating the unit
`e₁''(a)` through the retained pin
`e₁''(a) k₁'(a) + 2 j H'(a)³ = 0` transports it to the `j`-loaded face
`b₃'''(a) Φ₁(a) k₁'(a) = 36 j H'(a)⁴ w₂(a)`, whose four units force
the exact root dichotomy `b₃'''(a) = 0 ↔ w₂(a) = 0`.  On the
`k₁'(a) = 0` branch the same coefficient is the full tie
`b₃'''(a) Φ₁(a) + 3 b₃''(a) Φ₁'(a) + 36 H'(a) w₂'(a) e₁'(a)
  + 18 H'(a) w₂(a) e₁''(a) + 18 H''(a) w₂(a) e₁'(a) = 0`,
the first face loading `Φ₁'(a)`, `w₂'(a)` and `H''(a)` at the
`r`-root.  In the `k₁ = H k₂` limb the third coefficient of the
reduced terminal row `b₂ w₂ Ė - d₂ k₂ = j H³` at `b` is consumed: the
first `j`-loaded face of the limb at the `Φ₁`-root, tying the full
third-order data at `b` to the unit `6 j H'(b)³` and first loading
`b₂'''(b)`, `w₂'''(b)`, `Ė'''(b)`, `d₂'''(b)` and `k₂'''(b)`.  In the
transverse residual the fourth coefficient of the reduced terminal row
`b₂ w₂ Ė - H e₂ k₁ = j H³` at `b` is consumed: the second `j`-loaded
face of the limb, tying the fourth-order data at `b` to
`36 j H'(b)² H''(b)` and first loading `w₂''''(b)`, `e₂'''(b)` and
`k₁'''(b)`.  No honest contradiction is available in any limb — on
both dichotomy branches the transported pins are satisfiable, the new
full ties only introduce fresh higher-order loads, and the witnesses
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

section MixedNinthRowAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Third Taylor coefficient at the `Φ₁`-root of the reduced terminal
row carried by the `k₁ = H k₂` limb: the cube of the core survives
exactly once and the row is the first `j`-loaded face of the limb at
`b`, tying the full third-order data to the unit `6 j H'(b)³`. -/
theorem mixedKTwoRowThirdCoefficient_68
    (H b2 w2 eDot d2 k2 : k[X]) (j b : k) (hb : H.eval b = 0)
    (hrow : b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) :
    b2.derivative.derivative.derivative.eval b * w2.eval b *
          eDot.eval b +
        3 * b2.derivative.derivative.eval b * w2.derivative.eval b *
          eDot.eval b +
        3 * b2.derivative.derivative.eval b * w2.eval b *
          eDot.derivative.eval b +
        3 * b2.derivative.eval b * w2.derivative.derivative.eval b *
          eDot.eval b +
        6 * b2.derivative.eval b * w2.derivative.eval b *
          eDot.derivative.eval b +
        3 * b2.derivative.eval b * w2.eval b *
          eDot.derivative.derivative.eval b +
        b2.eval b * w2.derivative.derivative.derivative.eval b *
          eDot.eval b +
        3 * b2.eval b * w2.derivative.derivative.eval b *
          eDot.derivative.eval b +
        3 * b2.eval b * w2.derivative.eval b *
          eDot.derivative.derivative.eval b +
        b2.eval b * w2.eval b *
          eDot.derivative.derivative.derivative.eval b -
        (d2.derivative.derivative.derivative.eval b * k2.eval b +
          3 * d2.derivative.derivative.eval b * k2.derivative.eval b +
          3 * d2.derivative.eval b * k2.derivative.derivative.eval b +
          d2.eval b * k2.derivative.derivative.derivative.eval b) =
      6 * j * H.derivative.eval b ^ 3 := by
  have hddd := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval b) hrow
  simp only [derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, hb, pow_one, zero_mul, mul_zero, zero_add,
    add_zero, sub_zero, zero_sub, neg_zero, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true] at hddd
  first
    | linear_combination hddd
    | linear_combination -hddd

/-- Third Taylor coefficient of the reduced `I₄` row at the `r`-root
on the `e₁'(a) = 0` branch of the allocation dichotomy: through the
deepened jets `b₃''(a) = 0` and `e₁'(a) = 0` it is the exact tie
`b₃'''(a) Φ₁(a) + 18 H'(a) w₂(a) e₁''(a) = 0`. -/
theorem mixedReducedIFourThirdCoefficientDeepZero_68
    (H b3 phi1 w2 e1 : k[X]) (a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (hb3dda : b3.derivative.derivative.eval a = 0)
    (he1a : e1.eval a = 0) (he1da : e1.derivative.eval a = 0)
    (hI4red : b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0) :
    b3.derivative.derivative.derivative.eval a * phi1.eval a +
      18 * H.derivative.eval a * w2.eval a *
        e1.derivative.derivative.eval a = 0 := by
  have hddd := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval a) hI4red
  simp only [derivative_add, derivative_mul, derivative_ofNat,
    derivative_zero, eval_add, eval_mul, eval_ofNat, eval_zero, ha,
    hb3a, hb3da, hb3dda, he1a, he1da, zero_mul, mul_zero, zero_add,
    add_zero] at hddd
  first
    | linear_combination hddd
    | linear_combination -hddd

/-- Third Taylor coefficient of the reduced `I₄` row at the `r`-root
on the `k₁'(a) = 0` branch of the allocation dichotomy: only the
retained double zero of `b₃` and simple zero of `e₁` are available, so
the row is the full tie loading `Φ₁'(a)`, `w₂'(a)` and `H''(a)`. -/
theorem mixedReducedIFourThirdCoefficient_68
    (H b3 phi1 w2 e1 : k[X]) (a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (he1a : e1.eval a = 0)
    (hI4red : b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0) :
    b3.derivative.derivative.derivative.eval a * phi1.eval a +
        3 * b3.derivative.derivative.eval a *
          phi1.derivative.eval a +
        36 * H.derivative.eval a * w2.derivative.eval a *
          e1.derivative.eval a +
        18 * H.derivative.eval a * w2.eval a *
          e1.derivative.derivative.eval a +
        18 * H.derivative.derivative.eval a * w2.eval a *
          e1.derivative.eval a = 0 := by
  have hddd := congrArg
    (fun P : k[X] => P.derivative.derivative.derivative.eval a) hI4red
  simp only [derivative_add, derivative_mul, derivative_ofNat,
    derivative_zero, eval_add, eval_mul, eval_ofNat, eval_zero, ha,
    hb3a, hb3da, he1a, zero_mul, mul_zero, zero_add, add_zero] at hddd
  first
    | linear_combination hddd
    | linear_combination -hddd

/-- Transport of the deep-zero reduced-`I₄` tie through the retained
unit pin of the `e₁'(a) = 0` branch: eliminating the unit `e₁''(a)`
between `b₃'''(a) Φ₁(a) + 18 H'(a) w₂(a) e₁''(a) = 0` and
`e₁''(a) k₁'(a) + 2 j H'(a)³ = 0` yields the `j`-loaded face
`b₃'''(a) Φ₁(a) k₁'(a) = 36 j H'(a)⁴ w₂(a)`, and its four units force
the exact root dichotomy `b₃'''(a) = 0 ↔ w₂(a) = 0`. -/
theorem mixedEOneBranchPinElimination_68
    {phia Hda k1d e1dd b3ddd w2a j : k}
    (hpa : phia ≠ 0) (hj : j ≠ 0) (hHda : Hda ≠ 0) (hk1d : k1d ≠ 0)
    (hpin : e1dd * k1d + 2 * j * Hda ^ 3 = 0)
    (htie : b3ddd * phia + 18 * Hda * w2a * e1dd = 0) :
    b3ddd * phia * k1d = 36 * j * Hda ^ 4 * w2a ∧
      (b3ddd = 0 ↔ w2a = 0) := by
  have hjload : b3ddd * phia * k1d = 36 * j * Hda ^ 4 * w2a := by
    linear_combination k1d * htie - 18 * Hda * w2a * hpin
  have h36 : (36 : k) * j * Hda ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hj) (pow_ne_zero 4 hHda)
  refine ⟨hjload, ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
  · have hz : 36 * j * Hda ^ 4 * w2a = 0 := by
      linear_combination phia * k1d * h0 - hjload
    exact (mul_eq_zero.mp hz).resolve_left h36
  · have hz : b3ddd * phia * k1d = 0 := by
      linear_combination hjload + 36 * j * Hda ^ 4 * h0
    have hz2 : b3ddd * phia = 0 :=
      (mul_eq_zero.mp hz).resolve_right hk1d
    exact (mul_eq_zero.mp hz2).resolve_right hpa

/-- Fourth Taylor coefficient at the `Φ₁`-root of the reduced terminal
row carried by the transverse residual: with `w₂(b) = 0` it is the
second `j`-loaded face of the limb, tying the fourth-order data at `b`
to `36 j H'(b)² H''(b)` and first loading `w₂''''(b)`, `e₂'''(b)` and
`k₁'''(b)`. -/
theorem mixedResidualTerminalFourthCoefficient_68
    (H b2 w2 eDot e2 k1 : k[X]) (j b : k) (hb : H.eval b = 0)
    (hw2b : w2.eval b = 0)
    (hrow : b2 * w2 * eDot - H * e2 * k1 = C j * H ^ 3) :
    4 * b2.derivative.derivative.derivative.eval b *
          w2.derivative.eval b * eDot.eval b +
        6 * b2.derivative.derivative.eval b *
          w2.derivative.derivative.eval b * eDot.eval b +
        12 * b2.derivative.derivative.eval b * w2.derivative.eval b *
          eDot.derivative.eval b +
        4 * b2.derivative.eval b *
          w2.derivative.derivative.derivative.eval b * eDot.eval b +
        12 * b2.derivative.eval b * w2.derivative.derivative.eval b *
          eDot.derivative.eval b +
        12 * b2.derivative.eval b * w2.derivative.eval b *
          eDot.derivative.derivative.eval b +
        b2.eval b *
          w2.derivative.derivative.derivative.derivative.eval b *
          eDot.eval b +
        4 * b2.eval b * w2.derivative.derivative.derivative.eval b *
          eDot.derivative.eval b +
        6 * b2.eval b * w2.derivative.derivative.eval b *
          eDot.derivative.derivative.eval b +
        4 * b2.eval b * w2.derivative.eval b *
          eDot.derivative.derivative.derivative.eval b =
      H.derivative.derivative.derivative.derivative.eval b *
          e2.eval b * k1.eval b +
        4 * H.derivative.derivative.derivative.eval b *
          e2.derivative.eval b * k1.eval b +
        4 * H.derivative.derivative.derivative.eval b * e2.eval b *
          k1.derivative.eval b +
        6 * H.derivative.derivative.eval b *
          e2.derivative.derivative.eval b * k1.eval b +
        12 * H.derivative.derivative.eval b * e2.derivative.eval b *
          k1.derivative.eval b +
        6 * H.derivative.derivative.eval b * e2.eval b *
          k1.derivative.derivative.eval b +
        4 * H.derivative.eval b *
          e2.derivative.derivative.derivative.eval b * k1.eval b +
        12 * H.derivative.eval b * e2.derivative.derivative.eval b *
          k1.derivative.eval b +
        12 * H.derivative.eval b * e2.derivative.eval b *
          k1.derivative.derivative.eval b +
        4 * H.derivative.eval b * e2.eval b *
          k1.derivative.derivative.derivative.eval b +
        36 * j * H.derivative.eval b ^ 2 *
          H.derivative.derivative.eval b := by
  have hdddd := congrArg
    (fun P : k[X] =>
      P.derivative.derivative.derivative.derivative.eval b) hrow
  simp only [derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, hb, hw2b, pow_one, zero_mul, mul_zero, zero_add,
    add_zero, sub_zero, zero_sub, neg_zero, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true] at hdddd
  first
    | linear_combination hdddd
    | linear_combination -hdddd

end MixedNinthRowAlgebra68

section MixedNinthRowSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Ninth-row refinement of the preserved transverse two-root
allocation.  The `b₂ = H b₃` limb consumes the third coefficient of
its reduced `I₄` row at the `r`-root in both branches of the retained
allocation dichotomy.  On `e₁'(a) = 0` the deepened jets collapse it
to `b₃'''(a) Φ₁(a) + 18 H'(a) w₂(a) e₁''(a) = 0`; the retained unit
pin eliminates `e₁''(a)` into the `j`-loaded face
`b₃'''(a) Φ₁(a) k₁'(a) = 36 j H'(a)⁴ w₂(a)`, forcing the exact root
dichotomy `b₃'''(a) = 0 ↔ w₂(a) = 0`.  On `k₁'(a) = 0` it is the full
tie first loading `Φ₁'(a)`, `w₂'(a)` and `H''(a)`.  The `k₁ = H k₂`
limb consumes the third coefficient of its reduced terminal row at
`b`, the first `j`-loaded face of the limb at the `Φ₁`-root with unit
right-hand side `6 j H'(b)³`.  The transverse residual consumes the
fourth coefficient of its reduced terminal row at `b`, the second
`j`-loaded face of the limb with right-hand load
`36 j H'(b)² H''(b)`.  No limb closes — the transported pins are
satisfiable and the witnesses carry no degree bounds — so all three
children are returned refined and the `H ∣ r`, `H ∣ Φ₁` siblings pass
through untouched. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneMixedNinthRowPacket
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
                     = 0 ∧
               b2.derivative.derivative.derivative.eval b *
                     w2.eval b * eDot.eval b +
                   3 * b2.derivative.derivative.eval b *
                     w2.derivative.eval b * eDot.eval b +
                   3 * b2.derivative.derivative.eval b * w2.eval b *
                     eDot.derivative.eval b +
                   3 * b2.derivative.eval b *
                     w2.derivative.derivative.eval b * eDot.eval b +
                   6 * b2.derivative.eval b * w2.derivative.eval b *
                     eDot.derivative.eval b +
                   3 * b2.derivative.eval b * w2.eval b *
                     eDot.derivative.derivative.eval b +
                   b2.eval b *
                     w2.derivative.derivative.derivative.eval b *
                     eDot.eval b +
                   3 * b2.eval b * w2.derivative.derivative.eval b *
                     eDot.derivative.eval b +
                   3 * b2.eval b * w2.derivative.eval b *
                     eDot.derivative.derivative.eval b +
                   b2.eval b * w2.eval b *
                     eDot.derivative.derivative.derivative.eval b -
                   (d2.derivative.derivative.derivative.eval b *
                       k2.eval b +
                     3 * d2.derivative.derivative.eval b *
                       k2.derivative.eval b +
                     3 * d2.derivative.eval b *
                       k2.derivative.derivative.eval b +
                     d2.eval b *
                       k2.derivative.derivative.derivative.eval b) =
                 6 * j * H.derivative.eval b ^ 3) ∨
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
                     2 * j * H.derivative.eval a ^ 3 = 0 ∧
                   b3.derivative.derivative.derivative.eval a *
                       phi1.eval a +
                     18 * H.derivative.eval a * w2.eval a *
                       e1.derivative.derivative.eval a = 0 ∧
                   b3.derivative.derivative.derivative.eval a *
                       phi1.eval a * k1.derivative.eval a =
                     36 * j * H.derivative.eval a ^ 4 * w2.eval a ∧
                   (b3.derivative.derivative.derivative.eval a = 0 ↔
                     w2.eval a = 0)) ∨
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
                       = 0 ∧
                   b3.derivative.derivative.derivative.eval a *
                       phi1.eval a +
                     3 * b3.derivative.derivative.eval a *
                       phi1.derivative.eval a +
                     36 * H.derivative.eval a *
                       w2.derivative.eval a * e1.derivative.eval a +
                     18 * H.derivative.eval a * w2.eval a *
                       e1.derivative.derivative.eval a +
                     18 * H.derivative.derivative.eval a * w2.eval a *
                       e1.derivative.eval a = 0)) ∧
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
                     6 * j * H.derivative.eval b ^ 3 ∧
                 4 * b2.derivative.derivative.derivative.eval b *
                       w2.derivative.eval b * eDot.eval b +
                     6 * b2.derivative.derivative.eval b *
                       w2.derivative.derivative.eval b *
                       eDot.eval b +
                     12 * b2.derivative.derivative.eval b *
                       w2.derivative.eval b * eDot.derivative.eval b +
                     4 * b2.derivative.eval b *
                       w2.derivative.derivative.derivative.eval b *
                       eDot.eval b +
                     12 * b2.derivative.eval b *
                       w2.derivative.derivative.eval b *
                       eDot.derivative.eval b +
                     12 * b2.derivative.eval b *
                       w2.derivative.eval b *
                       eDot.derivative.derivative.eval b +
                     b2.eval b *
                       w2.derivative.derivative.derivative.derivative.eval
                         b * eDot.eval b +
                     4 * b2.eval b *
                       w2.derivative.derivative.derivative.eval b *
                       eDot.derivative.eval b +
                     6 * b2.eval b *
                       w2.derivative.derivative.eval b *
                       eDot.derivative.derivative.eval b +
                     4 * b2.eval b * w2.derivative.eval b *
                       eDot.derivative.derivative.derivative.eval b =
                   H.derivative.derivative.derivative.derivative.eval
                       b * e2.eval b * k1.eval b +
                     4 * H.derivative.derivative.derivative.eval b *
                       e2.derivative.eval b * k1.eval b +
                     4 * H.derivative.derivative.derivative.eval b *
                       e2.eval b * k1.derivative.eval b +
                     6 * H.derivative.derivative.eval b *
                       e2.derivative.derivative.eval b * k1.eval b +
                     12 * H.derivative.derivative.eval b *
                       e2.derivative.eval b * k1.derivative.eval b +
                     6 * H.derivative.derivative.eval b * e2.eval b *
                       k1.derivative.derivative.eval b +
                     4 * H.derivative.eval b *
                       e2.derivative.derivative.derivative.eval b *
                       k1.eval b +
                     12 * H.derivative.eval b *
                       e2.derivative.derivative.eval b *
                       k1.derivative.eval b +
                     12 * H.derivative.eval b * e2.derivative.eval b *
                       k1.derivative.derivative.eval b +
                     4 * H.derivative.eval b * e2.eval b *
                       k1.derivative.derivative.derivative.eval b +
                     36 * j * H.derivative.eval b ^ 2 *
                       H.derivative.derivative.eval b)))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, hsplit⟩ :=
    S.terminalAfterLowerOneMixedEighthRowPacket (H := H) hdeg hp hq
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
    rcases htri with
      ⟨hk1b, k2, hk2, hk2row, hk2faceB, hk2facea, hk2jet, hk2tie2⟩ |
      ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red, he1row, hb3a, he1a,
        hb3da, hfaceProd, hdichot, hsub⟩ |
      ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db, hphi1ddb, hphi1dddb,
        e2, psi4, hd2sq, hquart, hI4red, hrowRed, htie, htie2, htie3⟩
    · -- `k₁` limb: third coefficient of the reduced terminal row at
      -- `b`, the first `j`-loaded face of the limb at the `Φ₁`-root.
      exact Or.inl ⟨hk1b, k2, hk2, hk2row, hk2faceB, hk2facea, hk2jet,
        hk2tie2,
        mixedKTwoRowThirdCoefficient_68 H b2 w2 _ d2 k2 j b hb hk2row⟩
    · -- `b₂` limb: reduced-`I₄` order three in both dichotomy
      -- branches; on `e₁'(a) = 0` the retained unit pin transports it
      -- to the `j`-loaded root dichotomy `b₃'''(a) = 0 ↔ w₂(a) = 0`.
      have hHda : H.derivative.eval a ≠ 0 := hsimple a ha
      refine Or.inr (Or.inl ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red,
        he1row, hb3a, he1a, hb3da, hfaceProd, ?_, hsub⟩)
      rcases hdichot with
        ⟨he1d, hb3dd, hd2dd, hb2ddd, hk1dne, he1ddne, hpin⟩ |
        ⟨hk1d, he1dne, hI4tie, hpin2⟩
      · have htieA := mixedReducedIFourThirdCoefficientDeepZero_68 H
          b3 phi1 w2 e1 a ha hb3a hb3da hb3dd he1a he1d hI4red
        obtain ⟨hjface, hiff⟩ := mixedEOneBranchPinElimination_68 hpa
          hj hHda hk1dne hpin htieA
        exact Or.inl ⟨he1d, hb3dd, hd2dd, hb2ddd, hk1dne, he1ddne,
          hpin, htieA, hjface, hiff⟩
      · exact Or.inr ⟨hk1d, he1dne, hI4tie, hpin2,
          mixedReducedIFourThirdCoefficient_68 H b3 phi1 w2 e1 a ha
            hb3a hb3da he1a hI4red⟩
    · -- Residual: fourth coefficient of the reduced terminal row at
      -- `b`, the second `j`-loaded face of the limb.
      exact Or.inr (Or.inr ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db,
        hphi1ddb, hphi1dddb, e2, psi4, hd2sq, hquart, hI4red, hrowRed,
        htie, htie2, htie3,
        mixedResidualTerminalFourthCoefficient_68 H b2 w2 _ e2 k1 j b
          hb hw2b hrowRed⟩)

end MixedNinthRowSource68

end Max11DegreeRoutes
