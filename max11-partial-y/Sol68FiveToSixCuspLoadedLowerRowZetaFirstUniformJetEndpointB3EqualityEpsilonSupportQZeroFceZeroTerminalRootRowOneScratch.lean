import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalRootPacketScratch

/-! # The second pinned row on a terminal root -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalRootRowOne68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Root evaluation of the pinned row one after the quotient normal form. -/
theorem fiveToSix_qZero_terminal_rowOne_root_algebra68
    (alpha gamma epsilon eta : k)
    (A B c d e v W : k[X]) (x : k)
    (hBx : B.eval x = 0) (hdx : d.eval x ≠ 0)
    (hv : (2 : k) • c + C (3 * gamma) = B * v)
    (he : e = (1 / 9 : k) • B ^ 2 - (1 / 2 : k) • (v * d) -
      C (3 / 4 * epsilon))
    (hW : W = (4 : k) • A + (3 : k) • v ^ 2)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    (derivative B).eval x * (A.eval x * W.eval x - 18 * gamma) +
      6 * (derivative A).eval x * d.eval x -
      9 * d.eval x * v.eval x * (derivative v).eval x -
      9 * (derivative d).eval x * v.eval x ^ 2 = 0 := by
  have hv0 := congrArg (fun R : k[X] => R.eval x) hv
  have hv1 := congrArg (fun R : k[X] => (derivative R).eval x) hv
  have he0 := congrArg (fun R : k[X] => R.eval x) he
  have he1 := congrArg (fun R : k[X] => (derivative R).eval x) he
  have hW0 := congrArg (fun R : k[X] => R.eval x) hW
  simp only [derivative_add, derivative_sub, derivative_smul, derivative_C,
    derivative_mul, derivative_pow, eval_add, eval_sub, eval_smul, eval_mul,
    eval_pow, eval_C, eval_zero] at hv0 hv1 he0 he1 hW0
  rw [hBx] at hv0 hv1 he0 he1
  norm_num at hv0 hv1 he0 he1 hW0
  have hcval : c.eval x = -(3 / 2 : k) * gamma := by
    linear_combination (1 / 2 : k) * hv0
  have hcpval : (derivative c).eval x =
      (1 / 2 : k) * (derivative B).eval x * v.eval x := by
    linear_combination (1 / 2 : k) * hv1
  have heval : e.eval x =
      -(1 / 2 : k) * v.eval x * d.eval x - (3 / 4 : k) * epsilon := by
    linear_combination he0
  have hepval : (derivative e).eval x =
      -(1 / 2 : k) * ((derivative v).eval x * d.eval x +
        v.eval x * (derivative d).eval x) := by
    linear_combination he1
  have hWval : W.eval x = 4 * A.eval x + 3 * v.eval x ^ 2 := by
    exact hW0
  have hr := congrArg (fun R : k[X] => R.eval x) hrow
  simp only [secondaryResidualRowOnePolynomial68,
    cubicLoadRowOnePolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    derivative_add, derivative_sub, derivative_smul, derivative_mul,
    derivative_pow, derivative_C, eval_add, eval_sub, eval_smul, eval_mul,
    eval_pow, eval_neg, eval_C, eval_zero] at hr
  rw [hBx, hcval, hcpval, heval, hepval] at hr
  norm_num at hr
  have hprod : d.eval x *
      ((derivative B).eval x * (A.eval x * W.eval x - 18 * gamma) +
        6 * (derivative A).eval x * d.eval x -
        9 * d.eval x * v.eval x * (derivative v).eval x -
        9 * (derivative d).eval x * v.eval x ^ 2) = 0 := by
    linear_combination (-27 / 2 : k) * hr +
      (d.eval x * (derivative B).eval x * A.eval x) * hWval
  exact (mul_eq_zero.mp hprod).resolve_left hdx

#print axioms fiveToSix_qZero_terminal_rowOne_root_algebra68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalRootRowOne68

end Max11DegreeRoutes
