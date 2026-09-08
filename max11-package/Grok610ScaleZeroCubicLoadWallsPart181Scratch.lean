import Grok610ScaleZeroCubicLoadWallsPart08Scratch
import Grok610ScaleZeroCubicLoadWallsPart12Scratch
import Grok610ScaleZeroCubicLoadWallsPart86Scratch
import Grok610ScaleZeroCubicLoadWallsPart114Scratch
import Grok610ScaleZeroCubicLoadWallsPart150Scratch
import Grok610ScaleZeroCubicLoadWallsPart151Scratch
import Grok610ScaleZeroCubicLoadWallsPart158Scratch
import Grok610ScaleZeroCubicLoadWallsPart171Scratch
import Grok610ScaleZeroCubicLoadWallsPart180Scratch

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

section CubicLoadBCDEWallKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BCDE_betaWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hl : l = 0)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hAne := CubicLoadSigmaConeBCDE610_A_ne hcone
  have hBne : B ≠ 0 := hcone.2.1
  have hCne : C ≠ 0 := hcone.2.2.1
  have hDne : D ≠ 0 := hcone.2.2.2.1
  have hEne : E ≠ 0 := hcone.2.2.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha beta delta epsilon
      zeta eta theta A B C D E hmu hkap
  have hN2le := degreeZeroN2Cubic610_natDegree_le (j := j) (t := t) 0
      alpha beta delta epsilon zeta eta theta A B C D E hApos hkap hjdiv hder
  have hT1 : A.natDegree < 5 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hT2 : 2 * A.natDegree < 6 * A.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hdeg1 : 5 * A.natDegree =
      A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hBne', hCne', hDne', hEne', heq1, heq2, heq3⟩
    omega
  have hdeg2 : 6 * A.natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by omega
  have hz1 : (degreeZeroN1Cubic610 0 alpha beta delta epsilon zeta eta
        theta A B C D E).coeff (5 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hT1)
  have hz2 : (degreeZeroN2Cubic610 0 alpha beta delta epsilon zeta eta
        theta A B C D E).coeff (6 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN2le.trans_lt hT2)
  have hN1rest :=
    degreeZeroN1CubicBCDEWallBetaRest610_natDegree_lt alpha beta delta
      epsilon zeta eta theta A B C D E hcone hwall
  have hN2rest :=
    degreeZeroN2CubicBCDEWallBetaRest610_natDegree_lt alpha beta delta
      epsilon zeta eta theta A B C D E hcone hwall
  rw [degreeZeroN1Cubic610_eq_BCDE_betaWall, coeff_add, coeff_add] at hz1
  have hN1small :
      (degreeZeroN1CubicBCDEWallBetaRest610 alpha beta delta epsilon zeta
          eta theta A B C D E).coeff (5 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg1 ▸ hN1rest)
  rw [hN1small, add_zero] at hz1
  rw [degreeZeroN2Cubic610_eq_BCDE_betaWall, coeff_add, coeff_add] at hz2
  have hN2small :
      (degreeZeroN2CubicBCDEWallBetaRest610 alpha beta delta epsilon zeta
          eta theta A B C D E).coeff (6 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg2 ▸ hN2rest)
  rw [hN2small, add_zero] at hz2
  have hN1face := n1CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
  have hN2face := n2CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
  have hN1L := n1CubicBetaFace610_coeff_top beta A
  have hN2L := n2CubicBetaFace610_coeff_top beta A
  rw [← hdeg1] at hN1face
  rw [hN1face, hN1L] at hz1
  rw [← hdeg2] at hN2face
  rw [hN2face, hN2L] at hz2
  have hx : beta = 0 :=
    n1n2_beta_column_det610 A.leadingCoeff
      ((5 / 81 : k) * n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff) beta
      (leadingCoeff_ne_zero.mpr hAne)
      (by simpa [add_comm] using hz1)
      (by
        have :
            (-(5 / 81 : k)) *
                n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
                  C.leadingCoeff D.leadingCoeff E.leadingCoeff *
                A.leadingCoeff =
              -A.leadingCoeff *
                ((5 / 81 : k) *
                  n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
                    C.leadingCoeff D.leadingCoeff E.leadingCoeff) := by
          ring
        rw [this] at hz2
        simpa [add_comm, sub_eq_add_neg] using hz2)
  exact cubicLoadSigmaCone_BCDE_offWall_impossible (j := j) (t := t) 0
    alpha beta delta epsilon zeta eta theta A B C D E hcone rfl
    (Or.inl hx) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
    hlam hkap hmu homi

end CubicLoadBCDEWallKills610

end Max11DegreeRoutes
