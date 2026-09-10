import Grok68NonsquareQuadraticPacketInventoryScratch

/-! # Tenth Taylor row of the mixed square dichotomy

Untracked working note. No tracked file was edited.

The inventoried mixed-loaded cell already carries the ninth-row faces
and the MixedNinthAllocation transports.  MixedNinthAllocation takes
no further Taylor row.  This file consumes the named next unused row:
the tenth Taylor coefficient of the reduced `I₄` / `e₁`-row on the
mixed square dichotomy.

On the `e₁'(a) = 0` branch the fourth coefficient of
`b₃ Φ₁ + 6 H w e₁ = 0` is the semi-collapsed tie
`b₃⁽⁴⁾(a) Φ₁(a) + 4 b₃'''(a) Φ₁'(a) + 24 H'(a) w(a) e₁'''(a)
  + 72 H'(a) w'(a) e₁''(a) + 36 H''(a) w(a) e₁''(a) = 0`,
and the fourth coefficient of `e₁ k₁ = H b₃ w Ė - j H³` is
`4 e₁'''(a) k₁'(a) + 6 e₁''(a) k₁''(a)
  = 4 H'(a) b₃'''(a) w(a) Ė(a) - 36 j H''(a) H'(a)²`.
On the inventoried `w(a) = 0` child those identities collapse to
`b₃⁽⁴⁾(a) Φ₁(a) + 72 H'(a) w'(a) e₁''(a) = 0` and
`4 e₁'''(a) k₁'(a) + 6 e₁''(a) k₁''(a) + 36 j H''(a) H'(a)² = 0`;
the retained unit pin eliminates `e₁''(a)` to the `j`-loaded face
`b₃⁽⁴⁾(a) Φ₁(a) k₁'(a) = 144 j H'(a)⁴ w'(a)`, whose four units force
the exact root dichotomy `b₃⁽⁴⁾(a) = 0 ↔ w'(a) = 0` together with the
explicit allocation
`(w'(a) = 0 ∧ b₃⁽⁴⁾(a) = 0 ∧ B⁽⁵⁾(a) = 0) ∨ (all three ≠ 0)`.
Coordinate transport through `B = H B₃` and `D = H E₁` lifts the
collapsed tie to `B⁽⁵⁾(a) = 5 H'(a) b₃⁽⁴⁾(a)`,
`B⁽⁵⁾(a) Φ₁(a) + 120 H'(a) w'(a) D'''(a) = 0`,
`B⁽⁵⁾(a) Φ₁(a) k₁'(a) = 720 j H'(a)⁵ w'(a)`, and
`B⁽⁵⁾(a) = 0 ↔ w'(a) = 0`.  On the `k₁'(a) = 0` branch the same two
coefficients are the full fourth-order ties.  Cube and transverse
siblings gain only the next factor transports
`k₁''(a) = H''(a) K(a) + 2 H'(a) K'(a)` and
`D'''(b) = 6 H'(b) H''(b) E₂(b) + 6 H'(b)² E₂'(b)`.

No cell closes.  The R-loaded and early-geometric siblings pass
through untouched.  The named packet Prop
`PlaneKeller68AlignedNonsquareQuadraticPacketExclusion` is not claimed.

Exact gain: the mixed `B = H B₃` child of the inventoried residual
gains the tenth Taylor coefficients of the reduced `I₄` and `e₁`-rows
on both dichotomy branches; on the `e₁'(a) = 0`, `w(a) = 0` child it
gains the collapsed ties, the `j`-loaded face
`b₃⁽⁴⁾(a) Φ₁(a) k₁'(a) = 144 j H'(a)⁴ w'(a)`, the iff
`b₃⁽⁴⁾(a) = 0 ↔ w'(a) = 0`, the explicit `w'(a)` allocation, and the
coordinate lifts through `B⁽⁵⁾` and `D⁽⁴⁾`.  Cube and transverse
siblings gain only the corresponding next factor transports.

Next unused row: the eleventh Taylor coefficient of the reduced `I₄` /
`e₁`-row on the mixed square dichotomy (on the `w(a) = 0` child, the
fifth coefficient after the new `w'(a)` iff), or the still-opaque
component-III conjugate on the early-geometric leaf.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

section MixedTenthRowAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Fourth derivative evaluated at a point. -/
def fourthDerivEval68 (P : k[X]) (a : k) : k :=
  P.derivative.derivative.derivative.derivative.eval a

/-- Fifth derivative evaluated at a point. -/
def fifthDerivEval68 (P : k[X]) (a : k) : k :=
  P.derivative.derivative.derivative.derivative.derivative.eval a

/-- Second-order transport through a retained divisibility at a core
root, without a zero of the quotient. -/
theorem productSecondDerivativeEvalGeneral_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hPQ : P = H * Q) :
    P.derivative.derivative.eval a =
      H.derivative.derivative.eval a * Q.eval a +
        2 * H.derivative.eval a * Q.derivative.eval a := by
  have hdd := congrArg
    (fun R : k[X] => R.derivative.derivative.eval a) hPQ
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, ha,
    zero_mul, mul_zero, add_zero, zero_add] at hdd
  first
    | exact hdd
    | linear_combination hdd

/-- Third-order transport through a retained divisibility on a simple
zero of the quotient. -/
theorem productThirdDerivativeEvalSimpleZero_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hQa : Q.eval a = 0)
    (hPQ : P = H * Q) :
    P.derivative.derivative.derivative.eval a =
      3 * H.derivative.eval a * Q.derivative.derivative.eval a +
        3 * H.derivative.derivative.eval a * Q.derivative.eval a := by
  have hddd := congrArg
    (fun R : k[X] => R.derivative.derivative.derivative.eval a) hPQ
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, ha,
    hQa, zero_mul, mul_zero, add_zero, zero_add] at hddd
  first
    | exact hddd
    | linear_combination hddd

/-- Fourth-order transport through a retained divisibility on a simple
zero of the quotient. -/
theorem productFourthDerivativeEvalSimpleZero_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hQa : Q.eval a = 0)
    (hPQ : P = H * Q) :
    P.derivative.derivative.derivative.derivative.eval a =
      4 * H.derivative.eval a *
          Q.derivative.derivative.derivative.eval a +
        6 * H.derivative.derivative.eval a *
          Q.derivative.derivative.eval a +
        4 * H.derivative.derivative.derivative.eval a *
          Q.derivative.eval a := by
  have hdddd := congrArg
    (fun R : k[X] =>
      R.derivative.derivative.derivative.derivative.eval a) hPQ
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, ha,
    hQa, zero_mul, mul_zero, add_zero, zero_add] at hdddd
  first
    | exact hdddd
    | linear_combination hdddd

/-- Fourth-order transport through a retained divisibility on a double
zero of the quotient. -/
theorem productFourthDerivativeEvalDoubleZero_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hQa : Q.eval a = 0)
    (hQda : Q.derivative.eval a = 0) (hPQ : P = H * Q) :
    P.derivative.derivative.derivative.derivative.eval a =
      4 * H.derivative.eval a *
          Q.derivative.derivative.derivative.eval a +
        6 * H.derivative.derivative.eval a *
          Q.derivative.derivative.eval a := by
  rw [productFourthDerivativeEvalSimpleZero_68 H Q P a ha hQa hPQ,
    hQda, mul_zero, add_zero]

/-- Fifth-order transport through a retained divisibility on a
quadruple zero of the quotient. -/
theorem productFifthDerivativeEval_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hQa : Q.eval a = 0)
    (hQda : Q.derivative.eval a = 0)
    (hQdda : Q.derivative.derivative.eval a = 0)
    (hQddda : Q.derivative.derivative.derivative.eval a = 0)
    (hPQ : P = H * Q) :
    P.derivative.derivative.derivative.derivative.derivative.eval a =
      5 * H.derivative.eval a *
        Q.derivative.derivative.derivative.derivative.eval a := by
  have hddddd := congrArg
    (fun R : k[X] =>
      R.derivative.derivative.derivative.derivative.derivative.eval a)
    hPQ
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, ha,
    hQa, hQda, hQdda, hQddda, zero_mul, mul_zero, add_zero,
    zero_add] at hddddd
  first
    | exact hddddd
    | linear_combination hddddd

/-- Third-order transport through the retained square factorisation
`D = H² E₂` at a core root. -/
theorem squareFactorThirdDerivativeEval_68
    (H E2 D : k[X]) (b : k) (hb : H.eval b = 0)
    (hD : D = H ^ 2 * E2) :
    D.derivative.derivative.derivative.eval b =
      6 * H.derivative.eval b * H.derivative.derivative.eval b *
          E2.eval b +
        6 * H.derivative.eval b ^ 2 * E2.derivative.eval b := by
  have hmul : D = H * (H * E2) := by rw [hD]; ring
  have hQ0 : (H * E2).eval b = 0 := by rw [eval_mul, hb, zero_mul]
  have hQd := productDerivativeEval_68 H E2 (H * E2) b hb rfl
  have hQdd :=
    productSecondDerivativeEvalGeneral_68 H E2 (H * E2) b hb rfl
  have hD3 :=
    productThirdDerivativeEvalSimpleZero_68 H (H * E2) D b hb hQ0 hmul
  rw [hD3, hQd, hQdd]
  ring

/-- Scalar `6` passes through four derivatives. -/
theorem sixMulFourthEval_68 (T : k[X]) (a : k) :
    fourthDerivEval68 ((6 : k[X]) * T) a =
      (6 : k) * fourthDerivEval68 T a := by
  simp only [fourthDerivEval68]
  have hder : ∀ P : k[X],
      ((6 : k[X]) * P).derivative = (6 : k[X]) * P.derivative := by
    intro P
    simp [derivative_mul, derivative_ofNat, derivative_C]
  rw [hder, hder, hder, hder, eval_mul, eval_ofNat]

/-- Pair second derivative on a double zero of the left factor. -/
theorem leftDoubleZeroPairSecondEval_68
    (A B : k[X]) (a : k) (hA : A.eval a = 0)
    (hAda : A.derivative.eval a = 0) :
    (A * B).derivative.derivative.eval a =
      A.derivative.derivative.eval a * B.eval a := by
  simp [derivative_mul, derivative_add, eval_add, eval_mul, hA, hAda,
    zero_mul, mul_zero, add_zero, zero_add]

/-- Pair third derivative on a double zero of the left factor. -/
theorem leftDoubleZeroPairThirdEval_68
    (A B : k[X]) (a : k) (hA : A.eval a = 0)
    (hAda : A.derivative.eval a = 0) :
    (A * B).derivative.derivative.derivative.eval a =
      A.derivative.derivative.derivative.eval a * B.eval a +
        3 * A.derivative.derivative.eval a * B.derivative.eval a := by
  simp [derivative_mul, derivative_add, eval_add, eval_mul, hA, hAda,
    zero_mul, mul_zero, add_zero, zero_add]
  ring

/-- Pair fourth derivative on a double zero of the left factor. -/
theorem leftDoubleZeroPairFourthEval_68
    (A B : k[X]) (a : k) (hA : A.eval a = 0)
    (hAda : A.derivative.eval a = 0) :
    (A * B).derivative.derivative.derivative.derivative.eval a =
      A.derivative.derivative.derivative.derivative.eval a *
          B.eval a +
        4 * A.derivative.derivative.derivative.eval a *
          B.derivative.eval a +
        6 * A.derivative.derivative.eval a *
          B.derivative.derivative.eval a := by
  simp [derivative_mul, derivative_add, eval_add, eval_mul, hA, hAda,
    zero_mul, mul_zero, add_zero, zero_add]
  ring

/-- Pair fourth derivative on a triple zero of the left factor. -/
theorem leftTripleZeroPairFourthEval_68
    (A B : k[X]) (a : k) (hA : A.eval a = 0)
    (hAda : A.derivative.eval a = 0)
    (hAdda : A.derivative.derivative.eval a = 0) :
    (A * B).derivative.derivative.derivative.derivative.eval a =
      A.derivative.derivative.derivative.derivative.eval a *
          B.eval a +
        4 * A.derivative.derivative.derivative.eval a *
          B.derivative.eval a := by
  rw [leftDoubleZeroPairFourthEval_68 A B a hA hAda, hAdda]
  ring

/-- Pair fourth derivative on a simple zero of both factors and a
first-order zero of the left factor. -/
theorem pairFourthEvalLeftSimpleBothZero_68
    (A B : k[X]) (a : k) (hA : A.eval a = 0) (hB : B.eval a = 0)
    (hAda : A.derivative.eval a = 0) :
    (A * B).derivative.derivative.derivative.derivative.eval a =
      4 * A.derivative.derivative.derivative.eval a *
          B.derivative.eval a +
        6 * A.derivative.derivative.eval a *
          B.derivative.derivative.eval a := by
  rw [leftDoubleZeroPairFourthEval_68 A B a hA hAda, hB, mul_zero,
    zero_add]

/-- The cube `j H³` contributes `36 j H'(a)² H''(a)` at a core root. -/
theorem constMulCubeFourthDerivativeEval_68
    (H : k[X]) (j a : k) (ha : H.eval a = 0) :
    (C j * H ^ 3).derivative.derivative.derivative.derivative.eval a =
      36 * j * H.derivative.eval a ^ 2 *
        H.derivative.derivative.eval a := by
  have hcube : H ^ 3 = H * (H * H) := by ring
  have hQ0 : (H * H).eval a = 0 := by rw [eval_mul, ha, zero_mul]
  have hQd : (H * H).derivative.eval a = 0 := by
    rw [productDerivativeEval_68 H H (H * H) a ha rfl, ha, mul_zero]
  have hQdd : (H * H).derivative.derivative.eval a =
      2 * H.derivative.eval a ^ 2 := by
    rw [productSecondDerivativeEvalGeneral_68 H H (H * H) a ha rfl, ha,
      mul_zero, zero_add]
    ring
  have hQddd : (H * H).derivative.derivative.derivative.eval a =
      6 * H.derivative.eval a * H.derivative.derivative.eval a := by
    rw [productThirdDerivativeEvalSimpleZero_68 H H (H * H) a ha ha
      rfl]
    ring
  have hH3 :
      (H ^ 3).derivative.derivative.derivative.derivative.eval a =
        36 * H.derivative.eval a ^ 2 *
          H.derivative.derivative.eval a := by
    have hP := productFourthDerivativeEvalSimpleZero_68 H (H * H)
      (H ^ 3) a ha hQ0 hcube
    rw [hP, hQd, hQdd, hQddd]
    ring
  have hder : ∀ P : k[X],
      (C j * P).derivative = C j * P.derivative := by
    intro P
    simp [derivative_mul, derivative_C]
  rw [hder, hder, hder, hder, eval_mul, eval_C, hH3]
  ring

/-- Fourth Taylor coefficient of the reduced `I₄` row at the `r`-root
on the `e₁'(a) = 0` branch: through the deepened jets `b₃''(a) = 0`
and `e₁'(a) = 0` it is the semi-collapsed tie
`b₃⁽⁴⁾(a) Φ₁(a) + 4 b₃'''(a) Φ₁'(a) + 24 H'(a) w(a) e₁'''(a)
  + 72 H'(a) w'(a) e₁''(a) + 36 H''(a) w(a) e₁''(a) = 0`. -/
theorem mixedReducedIFourFourthCoefficientDeepZero_68
    (H b3 phi1 w2 e1 : k[X]) (a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (hb3dda : b3.derivative.derivative.eval a = 0)
    (he1a : e1.eval a = 0) (he1da : e1.derivative.eval a = 0)
    (hI4red : b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0) :
    b3.derivative.derivative.derivative.derivative.eval a *
          phi1.eval a +
        4 * b3.derivative.derivative.derivative.eval a *
          phi1.derivative.eval a +
        24 * H.derivative.eval a * w2.eval a *
          e1.derivative.derivative.derivative.eval a +
        72 * H.derivative.eval a * w2.derivative.eval a *
          e1.derivative.derivative.eval a +
        36 * H.derivative.derivative.eval a * w2.eval a *
          e1.derivative.derivative.eval a = 0 := by
  have h4 := congrArg
    (fun P : k[X] =>
      P.derivative.derivative.derivative.derivative.eval a) hI4red
  simp only [derivative_add, derivative_mul, derivative_ofNat,
    derivative_zero, eval_add, eval_mul, eval_ofNat, eval_zero, ha,
    hb3a, hb3da, hb3dda, he1a, he1da, zero_mul, mul_zero, zero_add,
    add_zero] at h4
  first
    | linear_combination h4
    | linear_combination -h4

/-- Fourth Taylor coefficient of the reduced `I₄` row on the
`e₁'(a) = 0`, `w(a) = 0` child: the deepened jets `b₃'''(a) = 0` and
`w(a) = 0` collapse it to
`b₃⁽⁴⁾(a) Φ₁(a) + 72 H'(a) w'(a) e₁''(a) = 0`. -/
theorem mixedReducedIFourFourthCoefficientDeepWZero_68
    (H b3 phi1 w2 e1 : k[X]) (a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (hb3dda : b3.derivative.derivative.eval a = 0)
    (hb3ddda : b3.derivative.derivative.derivative.eval a = 0)
    (he1a : e1.eval a = 0) (he1da : e1.derivative.eval a = 0)
    (hw2a : w2.eval a = 0)
    (hI4red : b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0) :
    b3.derivative.derivative.derivative.derivative.eval a *
          phi1.eval a +
        72 * H.derivative.eval a * w2.derivative.eval a *
          e1.derivative.derivative.eval a = 0 := by
  have hfull := mixedReducedIFourFourthCoefficientDeepZero_68 H b3
    phi1 w2 e1 a ha hb3a hb3da hb3dda he1a he1da hI4red
  simpa [hb3ddda, hw2a] using hfull

/-- Fourth Taylor coefficient of the reduced `I₄` row at the `r`-root
on the `k₁'(a) = 0` branch: only the retained double zero of `b₃` and
simple zero of `e₁` are available, so the row is the full fourth-order
tie. -/
theorem mixedReducedIFourFourthCoefficient_68
    (H b3 phi1 w2 e1 : k[X]) (a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (he1a : e1.eval a = 0)
    (hI4red : b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0) :
    b3.derivative.derivative.derivative.derivative.eval a *
          phi1.eval a +
        4 * b3.derivative.derivative.derivative.eval a *
          phi1.derivative.eval a +
        6 * b3.derivative.derivative.eval a *
          phi1.derivative.derivative.eval a +
        24 * H.derivative.eval a * w2.eval a *
          e1.derivative.derivative.derivative.eval a +
        72 * H.derivative.eval a * w2.derivative.eval a *
          e1.derivative.derivative.eval a +
        72 * H.derivative.eval a * w2.derivative.derivative.eval a *
          e1.derivative.eval a +
        36 * H.derivative.derivative.eval a * w2.eval a *
          e1.derivative.derivative.eval a +
        72 * H.derivative.derivative.eval a * w2.derivative.eval a *
          e1.derivative.eval a +
        24 * H.derivative.derivative.derivative.eval a * w2.eval a *
          e1.derivative.eval a = 0 := by
  have h4 := congrArg
    (fun P : k[X] =>
      P.derivative.derivative.derivative.derivative.eval a) hI4red
  simp only [derivative_add, derivative_mul, derivative_ofNat,
    derivative_zero, eval_add, eval_mul, eval_ofNat, eval_zero, ha,
    hb3a, hb3da, he1a, zero_mul, mul_zero, zero_add, add_zero] at h4
  first
    | linear_combination h4
    | linear_combination -h4

/-- Fourth Taylor coefficient of the `e₁`-row at the `r`-root on the
`e₁'(a) = 0` branch: through the triple zero of `H b₃` the row is
`4 e₁'''(a) k₁'(a) + 6 e₁''(a) k₁''(a)
  = 4 H'(a) b₃'''(a) w(a) Ė(a) - 36 j H''(a) H'(a)²`. -/
theorem mixedEOneRowFourthCoefficientDeepZero_68
    (H b3 w2 eDot e1 k1 : k[X]) (j a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (hb3dda : b3.derivative.derivative.eval a = 0)
    (he1a : e1.eval a = 0) (he1da : e1.derivative.eval a = 0)
    (hk1a : k1.eval a = 0)
    (hrow : e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3) :
    4 * e1.derivative.derivative.derivative.eval a *
          k1.derivative.eval a +
        6 * e1.derivative.derivative.eval a *
          k1.derivative.derivative.eval a =
      4 * H.derivative.eval a *
          b3.derivative.derivative.derivative.eval a * w2.eval a *
          eDot.eval a -
        36 * j * H.derivative.derivative.eval a *
          H.derivative.eval a ^ 2 := by
  have h4 := congrArg
    (fun P : k[X] =>
      P.derivative.derivative.derivative.derivative.eval a) hrow
  simp only [derivative_sub, derivative_add, derivative_mul,
    derivative_pow, derivative_C, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, ha, hb3a, hb3da, hb3dda, he1a, he1da, hk1a,
    pow_one, zero_mul, mul_zero, zero_add, add_zero, sub_zero,
    zero_sub, neg_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true] at h4
  first
    | linear_combination h4
    | linear_combination -h4

/-- Fourth Taylor coefficient of the `e₁`-row on the `e₁'(a) = 0`,
`w(a) = 0` child. -/
theorem mixedEOneRowFourthCoefficientDeepWZero_68
    (H b3 w2 eDot e1 k1 : k[X]) (j a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (hb3dda : b3.derivative.derivative.eval a = 0)
    (hb3ddda : b3.derivative.derivative.derivative.eval a = 0)
    (he1a : e1.eval a = 0) (he1da : e1.derivative.eval a = 0)
    (hk1a : k1.eval a = 0) (hw2a : w2.eval a = 0)
    (hrow : e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3) :
    4 * e1.derivative.derivative.derivative.eval a *
          k1.derivative.eval a +
        6 * e1.derivative.derivative.eval a *
          k1.derivative.derivative.eval a +
        36 * j * H.derivative.derivative.eval a *
          H.derivative.eval a ^ 2 = 0 := by
  have hfull := mixedEOneRowFourthCoefficientDeepZero_68 H b3 w2 eDot
    e1 k1 j a ha hb3a hb3da hb3dda he1a he1da hk1a hrow
  rw [hfull, hb3ddda]
  ring

/-- Fourth Taylor coefficient of the `e₁`-row at the `r`-root on the
`k₁'(a) = 0` branch. -/
theorem mixedEOneRowFourthCoefficient_68
    (H b3 w2 eDot e1 k1 : k[X]) (j a : k) (ha : H.eval a = 0)
    (hb3a : b3.eval a = 0) (hb3da : b3.derivative.eval a = 0)
    (he1a : e1.eval a = 0) (hk1a : k1.eval a = 0)
    (hk1da : k1.derivative.eval a = 0)
    (hrow : e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3) :
    6 * e1.derivative.derivative.eval a *
          k1.derivative.derivative.eval a +
        4 * e1.derivative.eval a *
          k1.derivative.derivative.derivative.eval a =
      4 * H.derivative.eval a *
          b3.derivative.derivative.derivative.eval a * w2.eval a *
          eDot.eval a +
        12 * H.derivative.eval a *
          b3.derivative.derivative.eval a * w2.derivative.eval a *
          eDot.eval a +
        12 * H.derivative.eval a *
          b3.derivative.derivative.eval a * w2.eval a *
          eDot.derivative.eval a +
        6 * H.derivative.derivative.eval a *
          b3.derivative.derivative.eval a * w2.eval a *
          eDot.eval a -
        36 * j * H.derivative.derivative.eval a *
          H.derivative.eval a ^ 2 := by
  have hprod : H * b3 * w2 * eDot = H * (b3 * (w2 * eDot)) := by ring
  have hrow' : e1 * k1 = H * (b3 * (w2 * eDot)) - C j * H ^ 3 := by
    rwa [← hprod]
  have h4 := congrArg
    (fun P : k[X] =>
      P.derivative.derivative.derivative.derivative.eval a) hrow'
  have hL : (e1 * k1).derivative.derivative.derivative.derivative.eval
      a =
      6 * e1.derivative.derivative.eval a *
          k1.derivative.derivative.eval a +
        4 * e1.derivative.eval a *
          k1.derivative.derivative.derivative.eval a := by
    simp [derivative_mul, derivative_add, eval_add, eval_mul, he1a,
      hk1a, hk1da, zero_mul, mul_zero, add_zero, zero_add]
    ring
  have hU0 : (b3 * (w2 * eDot)).eval a = 0 := by
    rw [eval_mul, hb3a, zero_mul]
  have hUd : (b3 * (w2 * eDot)).derivative.eval a = 0 := by
    simp [derivative_mul, eval_add, eval_mul, hb3a, hb3da, zero_mul,
      mul_zero, add_zero]
  have hUdd :=
    leftDoubleZeroPairSecondEval_68 b3 (w2 * eDot) a hb3a hb3da
  have hUddd :=
    leftDoubleZeroPairThirdEval_68 b3 (w2 * eDot) a hb3a hb3da
  have hV := productFourthDerivativeEvalDoubleZero_68 H
    (b3 * (w2 * eDot)) (H * (b3 * (w2 * eDot))) a ha hU0 hUd rfl
  have hWd : (w2 * eDot).derivative.eval a =
      w2.derivative.eval a * eDot.eval a +
        w2.eval a * eDot.derivative.eval a := by
    simp [derivative_mul, eval_add, eval_mul]
  have hcube := constMulCubeFourthDerivativeEval_68 H j a ha
  simp only [derivative_sub, eval_sub, hL, hV, hUdd, hUddd, hWd,
    eval_mul, hcube] at h4
  first
    | linear_combination h4
    | linear_combination -h4

/-- Transport of the deep-`w` reduced-`I₄` tie through the retained
unit pin of the `e₁'(a) = 0` branch: eliminating the unit `e₁''(a)`
between `b₃⁽⁴⁾(a) Φ₁(a) + 72 H'(a) w'(a) e₁''(a) = 0` and
`e₁''(a) k₁'(a) + 2 j H'(a)³ = 0` yields the `j`-loaded face
`b₃⁽⁴⁾(a) Φ₁(a) k₁'(a) = 144 j H'(a)⁴ w'(a)`, and its four units force
the exact root dichotomy `b₃⁽⁴⁾(a) = 0 ↔ w'(a) = 0`. -/
theorem mixedEOneBranchWZeroPinElimination_68
    {phia Hda k1d e1dd b3dddd w2da j : k}
    (hpa : phia ≠ 0) (hj : j ≠ 0) (hHda : Hda ≠ 0) (hk1d : k1d ≠ 0)
    (hpin : e1dd * k1d + 2 * j * Hda ^ 3 = 0)
    (htie : b3dddd * phia + 72 * Hda * w2da * e1dd = 0) :
    b3dddd * phia * k1d = 144 * j * Hda ^ 4 * w2da ∧
      (b3dddd = 0 ↔ w2da = 0) := by
  have hjload : b3dddd * phia * k1d = 144 * j * Hda ^ 4 * w2da := by
    linear_combination k1d * htie - 72 * Hda * w2da * hpin
  have h144 : (144 : k) * j * Hda ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hj) (pow_ne_zero 4 hHda)
  refine ⟨hjload, ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
  · have hz : 144 * j * Hda ^ 4 * w2da = 0 := by
      linear_combination phia * k1d * h0 - hjload
    exact (mul_eq_zero.mp hz).resolve_left h144
  · have hz : b3dddd * phia * k1d = 0 := by
      linear_combination hjload + 144 * j * Hda ^ 4 * h0
    have hz2 : b3dddd * phia = 0 :=
      (mul_eq_zero.mp hz).resolve_right hk1d
    exact (mul_eq_zero.mp hz2).resolve_right hpa

end MixedTenthRowAlgebra68

section MixedTenthRowSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- Next-order factor transports of the cube limb `k₁ = H K`. -/
def terminalFixedMixedCubeTenthFaces68
    (k1 : k[X]) : Prop :=
  ∀ (a b : k) (K : k[X]),
    H.eval a = 0 → H.eval b = 0 →
    k1 = H * K →
    k1.derivative.derivative.eval a =
        H.derivative.derivative.eval a * K.eval a +
          2 * H.derivative.eval a * K.derivative.eval a ∧
      k1.derivative.derivative.eval b =
        H.derivative.derivative.eval b * K.eval b +
          2 * H.derivative.eval b * K.derivative.eval b

theorem terminalFixedMixedCubeTenthFaces_68
    (k1 : k[X]) :
    terminalFixedMixedCubeTenthFaces68 H k1 := by
  intro a b K ha hb hk
  exact ⟨productSecondDerivativeEvalGeneral_68 H K k1 a ha hk,
    productSecondDerivativeEvalGeneral_68 H K k1 b hb hk⟩

/-- Next-order factor transport of the transverse limb `D = H² E₂`. -/
def terminalFixedMixedTransverseTenthFaces68
    (D : k[X]) : Prop :=
  ∀ (b : k) (E2 : k[X]),
    H.eval b = 0 → D = H ^ 2 * E2 →
    D.derivative.derivative.derivative.eval b =
      6 * H.derivative.eval b * H.derivative.derivative.eval b *
          E2.eval b +
        6 * H.derivative.eval b ^ 2 * E2.derivative.eval b

theorem terminalFixedMixedTransverseTenthFaces_68
    (D : k[X]) :
    terminalFixedMixedTransverseTenthFaces68 H D := by
  intro b E2 hb hD
  exact squareFactorThirdDerivativeEval_68 H E2 D b hb hD

set_option maxHeartbeats 16000000 in
/-- Tenth Taylor coefficients of the reduced `I₄` / `e₁`-row on the
mixed square dichotomy, universal in the fixed quotient witnesses. -/
def terminalFixedMixedSquareTenthFaces68
    (B D w phi1 eDot k1 : k[X]) (j : k) : Prop :=
  ∀ (a : k) (B3 E1 : k[X]),
    H.eval a = 0 → H.derivative.eval a ≠ 0 → j ≠ 0 →
    phi1.eval a ≠ 0 → k1.eval a = 0 →
    B = H * B3 → D = H * E1 →
    B3.eval a = 0 → B3.derivative.eval a = 0 → E1.eval a = 0 →
    B3 * phi1 + C 6 * H * w * E1 = 0 →
    E1 * k1 = H * B3 * w * eDot - C j * H ^ 3 →
    ((E1.derivative.eval a = 0 ∧
        B3.derivative.derivative.eval a = 0 ∧
        k1.derivative.eval a ≠ 0 ∧
        E1.derivative.derivative.eval a ≠ 0 ∧
        E1.derivative.derivative.eval a * k1.derivative.eval a +
          2 * j * H.derivative.eval a ^ 3 = 0) →
      (B3.derivative.derivative.derivative.derivative.eval a *
            phi1.eval a +
          4 * B3.derivative.derivative.derivative.eval a *
            phi1.derivative.eval a +
          24 * H.derivative.eval a * w.eval a *
            E1.derivative.derivative.derivative.eval a +
          72 * H.derivative.eval a * w.derivative.eval a *
            E1.derivative.derivative.eval a +
          36 * H.derivative.derivative.eval a * w.eval a *
            E1.derivative.derivative.eval a = 0) ∧
        (4 * E1.derivative.derivative.derivative.eval a *
              k1.derivative.eval a +
            6 * E1.derivative.derivative.eval a *
              k1.derivative.derivative.eval a =
          4 * H.derivative.eval a *
              B3.derivative.derivative.derivative.eval a *
              w.eval a * eDot.eval a -
            36 * j * H.derivative.derivative.eval a *
              H.derivative.eval a ^ 2) ∧
        ((w.eval a = 0 ∧
            B3.derivative.derivative.derivative.eval a = 0) →
          (B3.derivative.derivative.derivative.derivative.eval a *
                phi1.eval a +
              72 * H.derivative.eval a * w.derivative.eval a *
                E1.derivative.derivative.eval a = 0) ∧
            (4 * E1.derivative.derivative.derivative.eval a *
                  k1.derivative.eval a +
                6 * E1.derivative.derivative.eval a *
                  k1.derivative.derivative.eval a +
                36 * j * H.derivative.derivative.eval a *
                  H.derivative.eval a ^ 2 = 0) ∧
            B3.derivative.derivative.derivative.derivative.eval a *
                phi1.eval a * k1.derivative.eval a =
              144 * j * H.derivative.eval a ^ 4 *
                w.derivative.eval a ∧
            (B3.derivative.derivative.derivative.derivative.eval a
                = 0 ↔ w.derivative.eval a = 0) ∧
            fourthDerivEval68 B a = 0 ∧
            fifthDerivEval68 B a =
              5 * H.derivative.eval a * fourthDerivEval68 B3 a ∧
            fourthDerivEval68 D a =
              4 * H.derivative.eval a *
                  E1.derivative.derivative.derivative.eval a +
                6 * H.derivative.derivative.eval a *
                  E1.derivative.derivative.eval a ∧
            fifthDerivEval68 B a * phi1.eval a +
              120 * H.derivative.eval a * w.derivative.eval a *
                D.derivative.derivative.derivative.eval a = 0 ∧
            fifthDerivEval68 B a * phi1.eval a *
                k1.derivative.eval a =
              720 * j * H.derivative.eval a ^ 5 *
                w.derivative.eval a ∧
            (fifthDerivEval68 B a = 0 ↔ w.derivative.eval a = 0) ∧
            ((w.derivative.eval a = 0 ∧
                fourthDerivEval68 B3 a = 0 ∧
                fifthDerivEval68 B a = 0) ∨
              (w.derivative.eval a ≠ 0 ∧
                fourthDerivEval68 B3 a ≠ 0 ∧
                fifthDerivEval68 B a ≠ 0)))) ∧
    ((k1.derivative.eval a = 0 ∧ E1.derivative.eval a ≠ 0) →
      (B3.derivative.derivative.derivative.derivative.eval a *
            phi1.eval a +
          4 * B3.derivative.derivative.derivative.eval a *
            phi1.derivative.eval a +
          6 * B3.derivative.derivative.eval a *
            phi1.derivative.derivative.eval a +
          24 * H.derivative.eval a * w.eval a *
            E1.derivative.derivative.derivative.eval a +
          72 * H.derivative.eval a * w.derivative.eval a *
            E1.derivative.derivative.eval a +
          72 * H.derivative.eval a * w.derivative.derivative.eval a *
            E1.derivative.eval a +
          36 * H.derivative.derivative.eval a * w.eval a *
            E1.derivative.derivative.eval a +
          72 * H.derivative.derivative.eval a * w.derivative.eval a *
            E1.derivative.eval a +
          24 * H.derivative.derivative.derivative.eval a * w.eval a *
            E1.derivative.eval a = 0) ∧
        (6 * E1.derivative.derivative.eval a *
              k1.derivative.derivative.eval a +
            4 * E1.derivative.eval a *
              k1.derivative.derivative.derivative.eval a =
          4 * H.derivative.eval a *
              B3.derivative.derivative.derivative.eval a *
              w.eval a * eDot.eval a +
            12 * H.derivative.eval a *
              B3.derivative.derivative.eval a * w.derivative.eval a *
              eDot.eval a +
            12 * H.derivative.eval a *
              B3.derivative.derivative.eval a * w.eval a *
              eDot.derivative.eval a +
            6 * H.derivative.derivative.eval a *
              B3.derivative.derivative.eval a * w.eval a *
              eDot.eval a -
            36 * j * H.derivative.derivative.eval a *
              H.derivative.eval a ^ 2))

theorem terminalFixedMixedSquareTenthFaces_68
    (B D w phi1 eDot k1 : k[X]) (j : k) :
    terminalFixedMixedSquareTenthFaces68 H B D w phi1 eDot k1 j := by
  intro a B3 E1 ha hHa hj hphia hk1a hB hD hB3a hB3da hE1a
    hI4red hE1row
  constructor
  · rintro ⟨he1d, hb3dd, hk1dne, he1ddne, hpin⟩
    have hI4 := mixedReducedIFourFourthCoefficientDeepZero_68 H B3
      phi1 w E1 a ha hB3a hB3da hb3dd hE1a he1d hI4red
    have hE1 := mixedEOneRowFourthCoefficientDeepZero_68 H B3 w eDot
      E1 k1 j a ha hB3a hB3da hb3dd hE1a he1d hk1a hE1row
    refine ⟨hI4, hE1, ?_⟩
    rintro ⟨hw, hb3ddd⟩
    have hI4w := mixedReducedIFourFourthCoefficientDeepWZero_68 H B3
      phi1 w E1 a ha hB3a hB3da hb3dd hb3ddd hE1a he1d hw hI4red
    have hE1w := mixedEOneRowFourthCoefficientDeepWZero_68 H B3 w eDot
      E1 k1 j a ha hB3a hB3da hb3dd hb3ddd hE1a he1d hk1a hw hE1row
    have helim := mixedEOneBranchWZeroPinElimination_68 hphia hj hHa
      hk1dne hpin hI4w
    have hb4Eq := productFourthDerivativeEval_68 H B3 B a ha
      hB3a hB3da hb3dd hB
    have hb4zero : fourthDerivEval68 B a = 0 := by
      simp only [fourthDerivEval68]
      rw [hb4Eq, hb3ddd, mul_zero]
    have hb5Eq : fifthDerivEval68 B a =
        5 * H.derivative.eval a * fourthDerivEval68 B3 a := by
      simp only [fifthDerivEval68, fourthDerivEval68]
      exact productFifthDerivativeEval_68 H B3 B a ha
        hB3a hB3da hb3dd hb3ddd hB
    have hd3Eq :=
      productThirdDerivativeEval_68 H E1 D a ha hE1a he1d hD
    have hd4Eq : fourthDerivEval68 D a =
        4 * H.derivative.eval a *
            E1.derivative.derivative.derivative.eval a +
          6 * H.derivative.derivative.eval a *
            E1.derivative.derivative.eval a := by
      simp only [fourthDerivEval68]
      exact productFourthDerivativeEvalDoubleZero_68 H E1 D a
        ha hE1a he1d hD
    have hb5face :
        fifthDerivEval68 B a * phi1.eval a +
          120 * H.derivative.eval a * w.derivative.eval a *
            D.derivative.derivative.derivative.eval a = 0 := by
      simp only [fifthDerivEval68, fourthDerivEval68] at hb5Eq hI4w ⊢
      linear_combination phi1.eval a * hb5Eq +
        120 * H.derivative.eval a * w.derivative.eval a * hd3Eq +
        5 * H.derivative.eval a * hI4w
    have hb5jface :
        fifthDerivEval68 B a * phi1.eval a * k1.derivative.eval a =
          720 * j * H.derivative.eval a ^ 5 * w.derivative.eval a :=
      by
      simp only [fifthDerivEval68, fourthDerivEval68] at hb5Eq helim ⊢
      linear_combination
        phi1.eval a * k1.derivative.eval a * hb5Eq +
        5 * H.derivative.eval a * helim.1
    have hb5iff :
        fifthDerivEval68 B a = 0 ↔ w.derivative.eval a = 0 := by
      constructor
      · intro h0
        rw [hb5Eq] at h0
        apply helim.2.mp
        have hz := (mul_eq_zero.mp h0).resolve_left
          (mul_ne_zero (by norm_num) hHa)
        simpa [fourthDerivEval68] using hz
      · intro h0
        have hw0 := helim.2.mpr h0
        simp only [fifthDerivEval68, fourthDerivEval68] at hb5Eq hw0 ⊢
        simp [hb5Eq, hw0]
    have halloc :
        (w.derivative.eval a = 0 ∧
            fourthDerivEval68 B3 a = 0 ∧
            fifthDerivEval68 B a = 0) ∨
          (w.derivative.eval a ≠ 0 ∧
            fourthDerivEval68 B3 a ≠ 0 ∧
            fifthDerivEval68 B a ≠ 0) := by
      by_cases hw' : w.derivative.eval a = 0
      · exact Or.inl ⟨hw', helim.2.mpr hw', hb5iff.mpr hw'⟩
      · exact Or.inr ⟨hw', fun h0 => hw' (helim.2.mp h0),
          fun h0 => hw' (hb5iff.mp h0)⟩
    exact ⟨hI4w, hE1w, helim.1, helim.2, hb4zero, hb5Eq, hd4Eq,
      hb5face, hb5jface, hb5iff, halloc⟩
  · rintro ⟨hk1d, he1dne⟩
    exact ⟨mixedReducedIFourFourthCoefficient_68 H B3 phi1 w E1 a ha
        hB3a hB3da hE1a hI4red,
      mixedEOneRowFourthCoefficient_68 H B3 w eDot E1 k1 j a ha
        hB3a hB3da hE1a hk1a hk1d hE1row⟩

/-- Mixed square child after the tenth Taylor row. -/
def terminalFixedUnifiedMixedLoadedTenthInventory68
    (r t : k[X]) (B D w phi1 k1 : k[X]) : Prop :=
  let eDot := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  terminalFixedUnifiedMixedLoadedInventory68 (p := p) (j := j)
      H r t B D w phi1 k1 ∧
    terminalFixedMixedSquareTenthFaces68 H
      B D w phi1 eDot k1 j ∧
    terminalFixedMixedCubeTenthFaces68 H k1 ∧
    terminalFixedMixedTransverseTenthFaces68 H D

/-- Degree-two quadratic-packet residual after consuming the tenth
Taylor row on the mixed square dichotomy.  The R-loaded and
early-geometric siblings are preserved verbatim. -/
def NonsquareAlignedQuadraticPacketTenthResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRLoadedConsumed68 H S r t X0 Yd B D w phi1 k1 ∨
    terminalFixedUnifiedMixedLoadedTenthInventory68 (p := p) (j := j)
      H r t B D w phi1 k1 ∨
    terminalFixedUnifiedEarlyGeometryResidual68 H S
      r t X0 Yd B D w phi1 k1

theorem NonsquareAlignedQuadraticPacketTenthResidual_of_inventory68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (h : NonsquareAlignedQuadraticPacketInventoryResidual68 H S
      r t X0 Yd B D w phi1 k1) :
    NonsquareAlignedQuadraticPacketTenthResidual68 H S
      r t X0 Yd B D w phi1 k1 := by
  rcases h with hR | hM | hG
  · exact Or.inl hR
  · exact Or.inr (Or.inl ⟨hM,
      terminalFixedMixedSquareTenthFaces_68 H B D w phi1
        (terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r)) k1 j,
      terminalFixedMixedCubeTenthFaces_68 H k1,
      terminalFixedMixedTransverseTenthFaces_68 H D⟩)
  · exact Or.inr (Or.inr hG)

/-- Same-witness source packet for the tenth-row residual. -/
theorem NonsquareAlignedSourceCurveData68.quadraticPacketMixedTenthRowPacket
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ r t X0 Yd B D w phi1 k1 : k[X],
      p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
      C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
      B * phi1 + C 6 * H * w * D = 0 ∧
      H * B * w * terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
      H ∣ r * phi1 ∧
      terminalFixedMixedLowerTransport68 H S r t X0 Yd
        B D w phi1 k1 ∧
      NonsquareAlignedQuadraticPacketTenthResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower, hres⟩ :=
    S.quadraticPacketInventoryPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  exact ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower,
    NonsquareAlignedQuadraticPacketTenthResidual_of_inventory68
      H S r t X0 Yd B D w phi1 k1 hres⟩

end MixedTenthRowSource68

section MixedTenthRowInterface68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Remaining hypothesis after the tenth Taylor row: impossibility of
the three-way residual on a canonical same-witness tuple.  This is
strictly smaller than
`PlaneKeller68AlignedNonsquareQuadraticPacketExclusion`, which still
asks for the raw packet on every nonsquare core. -/
def PlaneKeller68AlignedNonsquareQuadraticPacketTenthExclusion
    : Prop :=
  ∀ (H : k[X]) [NonsquarePolynomial46 H] {p q : k[X][X]} {j : k}
      (S : NonsquareAlignedSourceCurveData68 H p q j)
      (r t X0 Yd B D w phi1 k1 : k[X]),
    j ≠ 0 →
    NonsquareAlignedQuadraticPacketTenthResidual68 H S
      r t X0 Yd B D w phi1 k1 → False

/-- The aligned-nonsquare parent reduces to the tenth-row residual.
The named packet Prop
`PlaneKeller68AlignedNonsquareQuadraticPacketExclusion` is not
claimed. -/
theorem planeKeller68AlignedNonsquareExclusion_of_quadraticPacketTenth
    (hinv : PlaneKeller68AlignedNonsquareQuadraticPacketTenthExclusion
      (k := k)) :
    PlaneKeller68AlignedNonsquareExclusion (k := k) := by
  intro P Q H hsource hnsq haligned
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  have haligned' : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0 := by
    simpa only [p, q] using haligned
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDsrc : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [p, q, bivariateJacobian, xderiv, GCD369SourceXDeriv]
      using hjac
  obtain ⟨S⟩ := nonsquareAlignedSourceCurveData68 (H := H) p q j
    hp hq hp6' hq8' haligned' hDsrc
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
      _hp4, _hX, _hY, _hI4, _hrow, _hdvd, _Tlower, hres⟩ :=
    S.quadraticPacketMixedTenthRowPacket (H := H)
      hHdegree hp hq hp6' hq8' haligned' hjac hj
  exact hinv H S r t X0 Yd B D w phi1 k1 hj hres

end MixedTenthRowInterface68

section NormalizedMixedTenthRow68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem normalized68ScaleTwo_alignedNonsquare_quadraticPacketTenth
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let _inst : NonsquarePolynomial46 H := ⟨hnsq⟩
    ∃ (j : k) (S : NonsquareAlignedSourceCurveData68 H p q j),
      j ≠ 0 ∧
      ∃ r t X0 Yd B D w phi1 k1 : k[X],
        p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
        C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
        B * phi1 + C 6 * H * w * D = 0 ∧
        H * B * w * terminalEDerivativeNumerator68 H
            (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
        H ∣ r * phi1 ∧
        terminalFixedMixedLowerTransport68 H S r t X0 Yd
          B D w phi1 k1 ∧
        NonsquareAlignedQuadraticPacketTenthResidual68 H S
          r t X0 Yd B D w phi1 k1 := by
  dsimp only
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  have haligned' : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0 := by
    simpa only [p, q] using haligned
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDsrc : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [p, q, bivariateJacobian, xderiv, GCD369SourceXDeriv]
      using hjac
  obtain ⟨S⟩ := nonsquareAlignedSourceCurveData68 (H := H) p q j
    hp hq hp6' hq8' haligned' hDsrc
  refine ⟨j, S, hj, ?_⟩
  exact S.quadraticPacketMixedTenthRowPacket (H := H)
    hHdegree hp hq hp6' hq8' haligned' hjac hj

end NormalizedMixedTenthRow68

#print axioms productSecondDerivativeEvalGeneral_68
#print axioms productThirdDerivativeEvalSimpleZero_68
#print axioms productFourthDerivativeEvalSimpleZero_68
#print axioms productFourthDerivativeEvalDoubleZero_68
#print axioms productFifthDerivativeEval_68
#print axioms squareFactorThirdDerivativeEval_68
#print axioms mixedReducedIFourFourthCoefficientDeepZero_68
#print axioms mixedReducedIFourFourthCoefficientDeepWZero_68
#print axioms mixedReducedIFourFourthCoefficient_68
#print axioms mixedEOneRowFourthCoefficientDeepZero_68
#print axioms mixedEOneRowFourthCoefficientDeepWZero_68
#print axioms mixedEOneRowFourthCoefficient_68
#print axioms mixedEOneBranchWZeroPinElimination_68
#print axioms terminalFixedMixedCubeTenthFaces_68
#print axioms terminalFixedMixedTransverseTenthFaces_68
#print axioms terminalFixedMixedSquareTenthFaces_68
#print axioms NonsquareAlignedQuadraticPacketTenthResidual_of_inventory68
#print axioms NonsquareAlignedSourceCurveData68.quadraticPacketMixedTenthRowPacket
#print axioms planeKeller68AlignedNonsquareExclusion_of_quadraticPacketTenth
#print axioms normalized68ScaleTwo_alignedNonsquare_quadraticPacketTenth

end Max11DegreeRoutes
