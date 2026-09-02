import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIScratch

/-! # The fourth lower-zero face on refined component III -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

section RefinedIIIFourthAlgebra68

variable {k : Type*} [Field k] [CharZero k]

theorem terminalEDerivativeNumerator_derivative_eval_root_shape_68
    (H A B phi w E : k[X]) (gamma epsilon a : k)
    (ha : H.eval a = 0)
    (hE : E = C (1 / 27 : k) * A ^ 3 +
      H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
        C (1 / 2 * gamma : k) * A) - C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * H ^ 4 * B ^ 2) :
    (terminalEDerivativeNumerator68 H E).derivative.eval a =
      -(2 / 9 : k) * H.derivative.eval a * A.eval a ^ 2 *
          A.derivative.eval a -
        (1 / 9 : k) * H.derivative.derivative.eval a * A.eval a ^ 3 := by
  rw [hE]
  simp only [terminalEDerivativeNumerator68, derivative_add, derivative_sub,
    derivative_neg, derivative_mul, derivative_pow, derivative_C,
    derivative_ofNat, C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul,
    eval_pow, eval_C, eval_ofNat, eval_zero, ha, zero_mul, mul_zero,
    zero_add, add_zero, zero_pow]
  ring_nf

theorem terminalRefinedIII_loaded_of_E_shape_68
    (H A B D phi w E K : k[X]) (gamma epsilon j a : k)
    (ha : H.eval a = 0)
    (hE : E = C (1 / 27 : k) * A ^ 3 +
      H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
        C (1 / 2 * gamma : k) * A) - C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * H ^ 4 * B ^ 2)
    (hload :
      terminalThirdTripleMiddleDoubleZeroAt68 B w
          (terminalEDerivativeNumerator68 H E) a -
        terminalThirdPairLeftZeroAt68 D K a =
          6 * j * H.derivative.eval a ^ 3) :
    let eDot := terminalEDerivativeNumerator68 H E
    eDot.eval a = -(1 / 9 : k) * H.derivative.eval a * A.eval a ^ 3 ∧
    eDot.derivative.eval a =
      -(2 / 9 : k) * H.derivative.eval a * A.eval a ^ 2 *
          A.derivative.eval a -
        (1 / 9 : k) * H.derivative.derivative.eval a * A.eval a ^ 3 ∧
    -3 * H.derivative.eval a * A.eval a ^ 3 * B.derivative.eval a *
          w.derivative.derivative.eval a -
        H.derivative.eval a * A.eval a ^ 3 * B.eval a *
          w.derivative.derivative.derivative.eval a -
        6 * H.derivative.eval a * A.eval a ^ 2 * A.derivative.eval a *
          B.eval a * w.derivative.derivative.eval a -
        3 * H.derivative.derivative.eval a * A.eval a ^ 3 * B.eval a *
          w.derivative.derivative.eval a -
        9 * (D.derivative.derivative.derivative.eval a * K.eval a +
          3 * D.derivative.derivative.eval a * K.derivative.eval a +
          3 * D.derivative.eval a * K.derivative.derivative.eval a) =
        54 * j * H.derivative.eval a ^ 3 := by
  dsimp only
  have hEroot : E.eval a = A.eval a ^ 3 / 27 := by
    have hm := congrArg (fun P : k[X] => P.eval a) hE
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat,
      ha, zero_pow, zero_mul, mul_zero, zero_add, add_zero] at hm
    simpa [div_eq_mul_inv, mul_comm] using hm
  have he := terminalEDerivativeNumerator_eval_root_68 H A E a ha hEroot
  have he1 := terminalEDerivativeNumerator_derivative_eval_root_shape_68
    H A B phi w E gamma epsilon a ha hE
  refine ⟨he, he1, ?_⟩
  dsimp only [terminalThirdTripleMiddleDoubleZeroAt68,
    terminalThirdPairLeftZeroAt68] at hload
  rw [he, he1] at hload
  linear_combination 9 * hload

end RefinedIIIFourthAlgebra68

end Max11DegreeRoutes
