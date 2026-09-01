import Sol410ScaleTwoAlignedNonsquareComplementSourcePacketScratch

/-! # Same-witness complementary eleventh row for `(4,10)` -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]
variable {H g f l : K[X]} {p q : K[X][Y]}

set_option maxHeartbeats 8000000 in
/-- M11 on the exact raw packet. -/
theorem AlignedNonsquareComplementRaw410.eleventhRow
    (R : AlignedNonsquareComplementRaw410 H p q g f l) :
    (64 : K[X]) * l *
        alignedEleventhComplementWall410 (p.coeff 0) g f l
          R.kappa3 R.kappa7 +
      (10240 : K[X]) * H * f * l ^ 3 = 0 := by
  have hcore := alignedNonsquareEleventh_core_410
    R.hH R.hp3 R.hM2 R.hM4 R.hM5 R.hM7 R.hM8 R.hM9 R.hM11
  have hblock := alignedNonsquareEleventh_solved_410 R.hH hcore R.hgf
  exact alignedNonsquareEleventh_complementSolved_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) g f l R.kappa3 R.kappa7
      R.hH R.hgf R.hL hblock

#print axioms AlignedNonsquareComplementRaw410.eleventhRow

end Max11DegreeRoutes
