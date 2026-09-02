import Sol68ScaleTwoAlignedNonsquareTerminalMixedRootsNextScratch

/-! # Split source bridge for the next mixed-root terminal row -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section SplitThirdDerivative68

variable {k : Type*} [Field k] [CharZero k]

/-- The sparse third-product rule used after the four root zeroes have been
proved separately.  This keeps expansion of the large reduced coordinates
out of the differentiation step. -/
theorem eval_thirdDerivative_triple_sub_product_of_root_zeroes_68
    (b w e d z : k[X]) (a : k)
    (he0 : e.eval a = 0) (he1 : e.derivative.eval a = 0)
    (hd0 : d.eval a = 0) (hz0 : z.eval a = 0) :
    (((((b * w * e - d * z).derivative).derivative).derivative).eval a) =
      b.eval a * w.eval a * e.derivative.derivative.derivative.eval a +
      3 * b.derivative.eval a * w.eval a *
        e.derivative.derivative.eval a +
      3 * b.eval a * w.derivative.eval a *
        e.derivative.derivative.eval a -
      3 * d.derivative.derivative.eval a * z.derivative.eval a -
      3 * d.derivative.eval a * z.derivative.derivative.eval a := by
  simp only [derivative_add, derivative_sub, derivative_mul, eval_add,
    eval_sub, eval_mul, he0, he1, hd0, hz0, zero_mul, mul_zero, add_zero,
    zero_add, sub_zero]
  ring

end SplitThirdDerivative68

section TerminalRZeroLastBridge68

variable {k : Type*} [Field k] [CharZero k]

/-- The four low-order root zeroes needed by the sparse third-product rule.
They are deliberately checked without expanding any third derivative. -/
theorem terminalRZero_reduced_lastRow_rootZeroes_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0) :
    let d := terminalGReducedD68 H r X Yd p1 p2
    let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
    let k1 := terminalGReducedKOne68 H r X Yd p0 p1 p2
      alpha gamma epsilon eta
    eDot.eval a = 0 ∧ eDot.derivative.eval a = 0 ∧
      d.eval a = 0 ∧ k1.eval a = 0 := by
  dsimp only
  simp only [terminalGReducedKOne68, terminalGReducedEDot68,
    terminalGReducedA68, terminalGReducedB68, terminalGReducedC68,
    terminalGReducedD68, terminalGReducedE68, terminalGReducedW68,
    terminalGReducedPhi68, terminalKDotNext68,
    terminalCShiftNumerator68, terminalVNumerator68,
    terminalKDotLoadQuotient68, terminalEDerivativeNumerator68,
    derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly,
    eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat,
    eval_zero, ha, hr, zero_mul, mul_zero, zero_add, add_zero, zero_pow,
    true_and]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Root evaluation of the sparse five-term third-derivative expression.
This is budgeted separately from both the product rule and the source row. -/
theorem terminalRZero_reduced_lastRow_sparseEvaluation_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hu : p2.eval a ≠ 0)
    (hlin : -r.derivative.eval a * p2.eval a +
      3 * H.derivative.eval a * p1.eval a = 0)
    (hquad : (Yd.eval a) ^ 2 + 1458 * X.eval a * p2.eval a = 0) :
    let b := terminalGReducedB68 r X Yd
    let d := terminalGReducedD68 H r X Yd p1 p2
    let w := terminalGReducedW68 H r X Yd p2 gamma
    let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
    let k1 := terminalGReducedKOne68 H r X Yd p0 p1 p2
      alpha gamma epsilon eta
    b.eval a * w.eval a * eDot.derivative.derivative.derivative.eval a +
        3 * b.derivative.eval a * w.eval a *
          eDot.derivative.derivative.eval a +
        3 * b.eval a * w.derivative.eval a *
          eDot.derivative.derivative.eval a -
        3 * d.derivative.derivative.eval a * k1.derivative.eval a -
        3 * d.derivative.eval a * k1.derivative.derivative.eval a =
      (2 / 27 : k) * (H.derivative.eval a) ^ 2 *
        terminalRZeroLastNext68
          (H.derivative.eval a) (H.derivative.derivative.eval a)
          (Yd.eval a) (p2.eval a) (p2.derivative.eval a)
          (p1.eval a) (p1.derivative.eval a)
          (r.derivative.derivative.eval a) := by
  dsimp only
  have hv : p1.eval a =
      r.derivative.eval a * p2.eval a / (3 * H.derivative.eval a) := by
    field_simp [hh]
    linear_combination hlin
  have hx : X.eval a = -(Yd.eval a) ^ 2 / (1458 * p2.eval a) := by
    field_simp [hu]
    linear_combination hquad
  simp only [terminalGReducedKOne68, terminalGReducedEDot68,
    terminalGReducedA68, terminalGReducedB68, terminalGReducedC68,
    terminalGReducedD68, terminalGReducedE68, terminalGReducedW68,
    terminalGReducedPhi68, terminalKDotNext68,
    terminalCShiftNumerator68, terminalVNumerator68,
    terminalKDotLoadQuotient68, terminalEDerivativeNumerator68,
    terminalRZeroLastNext68, derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
    C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, hr, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  rw [hv, hx]
  field_simp [hh, hu]
  ring

/-- The formerly missing third-derivative factor, assembled from the sparse
product rule and separately checked root evaluation. -/
theorem terminalRZero_reduced_lastRow_thirdDerivative_factor_split_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hu : p2.eval a ≠ 0)
    (hlin : -r.derivative.eval a * p2.eval a +
      3 * H.derivative.eval a * p1.eval a = 0)
    (hquad : (Yd.eval a) ^ 2 + 1458 * X.eval a * p2.eval a = 0) :
    let b := terminalGReducedB68 r X Yd
    let d := terminalGReducedD68 H r X Yd p1 p2
    let w := terminalGReducedW68 H r X Yd p2 gamma
    let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
    let k1 := terminalGReducedKOne68 H r X Yd p0 p1 p2
      alpha gamma epsilon eta
    (((((b * w * eDot - d * k1).derivative).derivative).derivative).eval a) =
      (2 / 27 : k) * (H.derivative.eval a) ^ 2 *
        terminalRZeroLastNext68
          (H.derivative.eval a) (H.derivative.derivative.eval a)
          (Yd.eval a) (p2.eval a) (p2.derivative.eval a)
          (p1.eval a) (p1.derivative.eval a)
          (r.derivative.derivative.eval a) := by
  dsimp only
  obtain ⟨he0, he1, hd0, hk0⟩ :=
    terminalRZero_reduced_lastRow_rootZeroes_68
      H r X Yd p0 p1 p2 alpha gamma epsilon eta a ha hr
  rw [eval_thirdDerivative_triple_sub_product_of_root_zeroes_68
    _ _ _ _ _ a he0 he1 hd0 hk0]
  exact terminalRZero_reduced_lastRow_sparseEvaluation_68
    H r X Yd p0 p1 p2 alpha gamma epsilon eta a ha hr hh hu hlin hquad

/-- The source polynomial row supplies the scalar coefficient with no
remaining interface premise. -/
theorem terminalRZero_reduced_lastNext_of_sourceRow_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta j a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hu : p2.eval a ≠ 0)
    (hlin : -r.derivative.eval a * p2.eval a +
      3 * H.derivative.eval a * p1.eval a = 0)
    (hquad : (Yd.eval a) ^ 2 + 1458 * X.eval a * p2.eval a = 0)
    (hrow :
      let b := terminalGReducedB68 r X Yd
      let d := terminalGReducedD68 H r X Yd p1 p2
      let w := terminalGReducedW68 H r X Yd p2 gamma
      let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
      let k1 := terminalGReducedKOne68 H r X Yd p0 p1 p2
        alpha gamma epsilon eta
      b * w * eDot - d * k1 = C j * H ^ 5) :
    terminalRZeroLastNext68
      (H.derivative.eval a) (H.derivative.derivative.eval a)
      (Yd.eval a) (p2.eval a) (p2.derivative.eval a)
      (p1.eval a) (p1.derivative.eval a)
      (r.derivative.derivative.eval a) = 0 := by
  dsimp only at hrow
  have hsourceZero :
      (((((terminalGReducedB68 r X Yd *
          terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedEDot68 H r X Yd p0 p1 p2 -
        terminalGReducedD68 H r X Yd p1 p2 *
          terminalGReducedKOne68 H r X Yd p0 p1 p2
            alpha gamma epsilon eta).derivative).derivative).derivative).eval a) =
        0 := by
    rw [hrow]
    simp only [derivative_add, derivative_sub, derivative_mul,
      derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly,
      eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero,
      ha, zero_mul, mul_zero, zero_add, add_zero, zero_pow]
    ring
  have hfactor := terminalRZero_reduced_lastRow_thirdDerivative_factor_split_68
    H r X Yd p0 p1 p2 alpha gamma epsilon eta a ha hr hh hu hlin hquad
  dsimp only at hfactor
  rw [hsourceZero] at hfactor
  have hc : (2 / 27 : k) * (H.derivative.eval a) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hh)
  exact (mul_eq_zero.mp hfactor.symm).resolve_left hc

/-- The compatibility consequence is now unconditional on the actual reduced
source row. -/
theorem terminalRZero_reduced_nextCompatibility_of_sourceRows_68
    (H r X Yd p0 p1 p2 : k[X]) (alpha gamma epsilon eta j a : k)
    (ha : H.eval a = 0) (hr : r.eval a = 0)
    (hh : H.derivative.eval a ≠ 0) (hu : p2.eval a ≠ 0)
    (hlin : -r.derivative.eval a * p2.eval a +
      3 * H.derivative.eval a * p1.eval a = 0)
    (hquad : (Yd.eval a) ^ 2 + 1458 * X.eval a * p2.eval a = 0)
    (hI4 : terminalGReducedB68 r X Yd *
          terminalGReducedPhi68 H r X Yd p0 p1 p2 gamma epsilon +
        (6 : k[X]) * terminalGReducedW68 H r X Yd p2 gamma *
          terminalGReducedD68 H r X Yd p1 p2 = 0)
    (hrow :
      let b := terminalGReducedB68 r X Yd
      let d := terminalGReducedD68 H r X Yd p1 p2
      let w := terminalGReducedW68 H r X Yd p2 gamma
      let eDot := terminalGReducedEDot68 H r X Yd p0 p1 p2
      let k1 := terminalGReducedKOne68 H r X Yd p0 p1 p2
        alpha gamma epsilon eta
      b * w * eDot - d * k1 = C j * H ^ 5) :
    terminalRZeroNextCompatibility68
      (H.derivative.eval a) (r.derivative.eval a) (X.eval a)
      (X.derivative.eval a) (Yd.eval a) (Yd.derivative.eval a)
      (p2.eval a) (p2.derivative.eval a) (p1.eval a) (p0.eval a)
      gamma epsilon = 0 := by
  apply terminalRZero_reduced_nextCompatibility_of_lastNext_68
    H r X Yd p0 p1 p2 gamma epsilon a ha hr hh hu hlin hquad hI4
  exact terminalRZero_reduced_lastNext_of_sourceRow_68
    H r X Yd p0 p1 p2 alpha gamma epsilon eta j a ha hr hh hu hlin hquad hrow

end TerminalRZeroLastBridge68

end Max11DegreeRoutes
