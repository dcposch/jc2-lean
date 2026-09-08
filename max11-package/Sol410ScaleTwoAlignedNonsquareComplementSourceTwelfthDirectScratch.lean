import Sol410ScaleTwoAlignedNonsquareComplementSourcePacketScratch

/-! # Direct same-witness complementary twelfth row for `(4,10)` -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]
variable {H g f l : K[X]} {p q : K[X][Y]}

set_option maxHeartbeats 8000000 in
/-- M12 on the exact raw packet.  The already-proved solved block is consumed
directly, avoiding a second enormous dependent theorem application. -/
theorem AlignedNonsquareComplementRaw410.twelfthRowDirect
    (R : AlignedNonsquareComplementRaw410 H p q g f l) :
    alignedTwelfthComplementV410 (p.coeff 0) f
        R.kappa3 R.kappa7 R.kappa11 +
      (320 : K[X]) * g * l *
        alignedEleventhComplementWall410 (p.coeff 0) g f l
          R.kappa3 R.kappa7 +
      H * alignedTwelfthComplementH4Coefficient410 (p.coeff 0) g f l
        R.kappa3 +
      H ^ 2 * alignedTwelfthComplementH5Coefficient410 l = 0 := by
  have hcore := alignedNonsquareTwelfth_core_410
    R.hH R.hp3 R.hM2 R.hM4 R.hM5 R.hM7 R.hM8 R.hM9 R.hM12
  have hblk := alignedNonsquareTwelfth_solved_410 R.hH hcore R.hgf
  let U : K[X] := (8 : K[X]) * p.coeff 1
  let V : K[X] := (4 : K[X]) * p.coeff 2
  have hscaled :
      (3200 : K[X]) * ((143 : K[X]) * g ^ 6 -
            (143 : K[X]) * V * g ^ 4 +
            (33 : K[X]) * V ^ 2 * g ^ 2 - V ^ 3) * f ^ 3 +
        (6400 : K[X]) * U * g *
          ((187 : K[X]) * g ^ 4 - (166 : K[X]) * V * g ^ 2 +
            (27 : K[X]) * V ^ 2) * f ^ 2 +
        (307200 : K[X]) * U ^ 2 * V ^ 2 * f +
        (102400 : K[X]) * U ^ 3 * V * g =
      H * (-(1305600 : K[X]) * U ^ 2 * V * f ^ 2 -
        (358400 : K[X]) * U ^ 3 * g * f +
        (4915200 : K[X]) * (p.coeff 0) * V ^ 2 * f ^ 2 +
        (9830400 : K[X]) * (p.coeff 0) * U * V * g * f -
        (25600 : K[X]) * U ^ 4 +
        (4915200 : K[X]) * (p.coeff 0) * U ^ 2 * V -
        Polynomial.C R.kappa3 * ((15360 : K[X]) * V ^ 2 * f ^ 2) -
        Polynomial.C R.kappa3 * ((30720 : K[X]) * U * V * g * f) -
        Polynomial.C R.kappa3 * ((15360 : K[X]) * U ^ 2 * V) +
      H * (-(1075200 : K[X]) * U ^ 2 * f ^ 3 +
          (17203200 : K[X]) * (p.coeff 0) * V * f ^ 3 +
          (22118400 : K[X]) * (p.coeff 0) * U * g * f ^ 2 +
          (9830400 : K[X]) * (p.coeff 0) * U ^ 2 * f -
          (78643200 : K[X]) * (p.coeff 0) ^ 2 * V * f -
          (78643200 : K[X]) * (p.coeff 0) ^ 2 * U * g +
          Polynomial.C R.kappa7 * ((320 : K[X]) * V * f) +
          Polynomial.C R.kappa7 * ((320 : K[X]) * U * g) -
          Polynomial.C R.kappa3 * ((53760 : K[X]) * V * f ^ 3) -
          Polynomial.C R.kappa3 * ((69120 : K[X]) * U * g * f ^ 2) -
          Polynomial.C R.kappa3 * ((30720 : K[X]) * U ^ 2 * f) +
          Polynomial.C R.kappa3 * ((491520 : K[X]) * (p.coeff 0) * V * f) +
          Polynomial.C R.kappa3 * ((491520 : K[X]) * (p.coeff 0) * U * g) +
        H * ((12902400 : K[X]) * (p.coeff 0) * f ^ 4 -
            (117964800 : K[X]) * (p.coeff 0) ^ 2 * f ^ 2 +
            (838860800 : K[X]) * (p.coeff 0) ^ 3 - Polynomial.C R.kappa11 +
            Polynomial.C R.kappa7 * ((480 : K[X]) * f ^ 2) -
            Polynomial.C R.kappa7 * ((10240 : K[X]) * (p.coeff 0)) -
            Polynomial.C R.kappa3 * ((40320 : K[X]) * f ^ 4) +
            Polynomial.C R.kappa3 * ((737280 : K[X]) * (p.coeff 0) * f ^ 2) -
            Polynomial.C R.kappa3 * ((7864320 : K[X]) * (p.coeff 0) ^ 2)))) := by
    dsimp only [U, V]
    linear_combination hblk
  have hU : U = H * l - g * f := by
    dsimp only [U]
    linear_combination R.hL
  have hV : V = g ^ 2 - H * f := by
    dsimp only [V]
    linear_combination -R.hgf
  rw [hU, hV] at hscaled
  have hfactored :
      H ^ 3 *
        (alignedTwelfthComplementV410 (p.coeff 0) f
            R.kappa3 R.kappa7 R.kappa11 +
          (320 : K[X]) * g * l *
            alignedEleventhComplementWall410 (p.coeff 0) g f l
              R.kappa3 R.kappa7 +
          H * alignedTwelfthComplementH4Coefficient410
            (p.coeff 0) g f l R.kappa3 +
          H ^ 2 * alignedTwelfthComplementH5Coefficient410 l) = 0 := by
    simp only [alignedTwelfthComplementV410,
      alignedEleventhComplementWall410,
      alignedTwelfthComplementH4Coefficient410,
      alignedTwelfthComplementH5Coefficient410]
    linear_combination hscaled
  exact (mul_eq_zero.mp hfactored).resolve_left (pow_ne_zero 3 R.hH)

#print axioms AlignedNonsquareComplementRaw410.twelfthRowDirect

end Max11DegreeRoutes
