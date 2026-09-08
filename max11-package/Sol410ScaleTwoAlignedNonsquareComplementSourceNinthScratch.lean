import Sol410ScaleTwoAlignedNonsquareComplementSourcePacketScratch

/-! # Same-witness complementary ninth row for `(4,10)` -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]
variable {H g f l : K[X]} {p q : K[X][Y]}

set_option maxHeartbeats 8000000 in
/-- M9 on the exact raw packet. -/
theorem AlignedNonsquareComplementRaw410.ninthRow
    (R : AlignedNonsquareComplementRaw410 H p q g f l) :
    alignedNinthComplementRow410 H (p.coeff 0) (q.coeff 1) g f l
      R.kappa R.kappa3 R.kappa5 R.kappa7 = 0 := by
  have hcore := alignedNonsquareNinth_core_410
    R.hH R.hp3 R.hM2 R.hM4 R.hM5 R.hM6 R.hM7 R.hM8 R.hM9
  have hblock := alignedNonsquareNinth_solved_410 R.hH hcore R.hgf
  exact alignedNonsquareNinth_complementSolved_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 1) g f l
      R.kappa R.kappa3 R.kappa5 R.kappa7 R.hH R.hgf R.hL hblock

#print axioms AlignedNonsquareComplementRaw410.ninthRow

end Max11DegreeRoutes
