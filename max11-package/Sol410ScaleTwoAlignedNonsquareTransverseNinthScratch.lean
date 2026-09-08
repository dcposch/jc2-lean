import Sol410ScaleTwoAlignedNonsquareTransverseSourcePacketScratch

/-! # Ninth-row kill of a transverse `(4,10)` root -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]
variable {H g f : K[X]} {p q : K[X][Y]}

set_option maxHeartbeats 8000000 in
/-- At any root of `H` where `g` vanishes, the exact ninth row forces the
complementary factor `g*f+8p₁` to vanish as well. -/
theorem AlignedNonsquareTransverseRaw410.gZero_forces_complementZero
    (R : AlignedNonsquareTransverseRaw410 H p q g f)
    (x : K) (hx : H.eval x = 0) (hgx : g.eval x = 0) :
    (g * f + (8 : K[X]) * p.coeff 1).eval x = 0 := by
  have hcore := alignedNonsquareNinth_core_410
    R.hH R.hp3 R.hM2 R.hM4 R.hM5 R.hM6 R.hM7 R.hM8 R.hM9
  have hblock := alignedNonsquareNinth_solved_410 R.hH hcore R.hgf
  have hgfEval := congrArg (fun w : K[X] => w.eval x) R.hgf
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hgfEval
  rw [hx, hgx] at hgfEval
  norm_num at hgfEval
  have hp2x : (p.coeff 2).eval x = 0 := by linear_combination hgfEval
  have hblockEval := congrArg (fun w : K[X] => w.eval x) hblock
  simp only [Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat] at hblockEval
  rw [hx, hgx, hp2x] at hblockEval
  norm_num at hblockEval
  have hp1x : (p.coeff 1).eval x = 0 := hblockEval
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, hgx, hp1x, zero_mul, mul_zero, add_zero]

#print axioms AlignedNonsquareTransverseRaw410.gZero_forces_complementZero

end Max11DegreeRoutes
