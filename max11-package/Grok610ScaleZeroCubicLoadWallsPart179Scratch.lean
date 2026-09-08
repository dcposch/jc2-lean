import Grok610ScaleZeroCubicLoadWallsPart11Scratch
import Grok610ScaleZeroCubicLoadWallsPart15Scratch
import Grok610ScaleZeroCubicLoadWallsPart37Scratch
import Grok610ScaleZeroCubicLoadWallsPart78Scratch
import Grok610ScaleZeroCubicLoadWallsPart148Scratch
import Grok610ScaleZeroCubicLoadWallsPart149Scratch
import Grok610ScaleZeroCubicLoadWallsPart162Scratch
import Grok610ScaleZeroCubicLoadWallsPart163Scratch
import Grok610ScaleZeroCubicLoadWallsPart164Scratch
import Grok610ScaleZeroCubicLoadWallsPart174Scratch
import Grok610ScaleZeroCubicLoadWallsPart175Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000

section CubicLoadCDWallKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CD_thetaWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hl : l = 0)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hbetaTop := cubicLoadSigmaConeCD610_n1BetaTop_of_thetaWall hcone hwall
  have hbeta0 : beta = 0 :=
    cubicN1_beta_eq_zero 0 alpha beta delta epsilon zeta eta theta
      A B C D E hbetaTop rfl hmu hkap
  subst hbeta0
  have hdeltaTop := cubicLoadSigmaConeCD610_n1DeltaTop_of_thetaWall hcone hwall
  have hdelta0 : delta = 0 :=
    cubicN1_delta_eq_zero 0 alpha 0 delta epsilon zeta eta theta
      A B C D E hdeltaTop rfl rfl hmu hkap
  subst hdelta0
  have hzetaTop := cubicLoadSigmaConeCD610_n1ZetaTop_of_thetaWall hcone hwall
  have hzeta0 : zeta = 0 :=
    cubicN1_zeta_eq_zero 0 alpha 0 0 epsilon zeta eta theta
      A B C D E hzetaTop rfl rfl rfl hmu hkap
  subst hzeta0
  have hAne := CubicLoadSigmaConeCD610_A_ne hcone
  have hCne : C ≠ 0 := hcone.2.1
  have hDne : D ≠ 0 := hcone.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha 0 0 epsilon
      0 eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) 0
      alpha 0 0 epsilon 0 eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 2 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hT2 : 2 * A.natDegree < 3 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hdeg1 : 2 * A.natDegree = 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  have hdeg2 : 3 * A.natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 0 alpha 0 0 epsilon 0 eta
        theta A B C D E).coeff (2 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 0 alpha 0 0 epsilon 0 eta
        theta A B C D E).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicCDWallThetaRest610_natDegree_lt alpha epsilon eta theta
      A B C D E hcone hwall
  have hN2rest :=
    degreeZeroN2CubicCDWallThetaRest610_natDegree_lt alpha epsilon eta theta
      A B C D E hcone hwall
  rw [degreeZeroN1Cubic610_eq_CD_thetaWall, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicCDWallThetaRest610 alpha epsilon eta theta
          A B C D E).coeff (2 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg1 ▸ hN1rest)
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_CD_thetaWall, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicCDWallThetaRest610 alpha epsilon eta theta
          A B C D E).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg2 ▸ hN2rest)
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceCD610_coeff_top A B C D E hCne hDne
  have hN2face := n2CubicSigmaFaceCD610_coeff_top A B C D E hAne hCne hDne
  have hN1L := n1CubicThetaFace610_coeff_top theta A
  have hN2L := n2CubicThetaFace610_coeff_top theta A
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hx : theta = 0 :=
    n1n2_theta_column_det610 A.leadingCoeff
      ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff) theta
      (leadingCoeff_ne_zero.mpr hAne)
      (by simpa [add_comm] using hz1)
      (by
        have : (5 / 27 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 *
              D.leadingCoeff =
            -A.leadingCoeff *
              ((-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff) := by
          ring
        rw [this] at hz2
        simpa [add_comm, sub_eq_add_neg] using hz2)
  have hTpos : A.natDegree < 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  exact cubicLoadSigmaCone_CD_offWall_impossible 0 alpha 0 0 epsilon
    0 eta theta A B C D E hcone rfl (Or.inl rfl) (Or.inl rfl)
    (Or.inl rfl) (Or.inl hx) hTpos hmu hkap

end CubicLoadCDWallKills610

end Max11DegreeRoutes
