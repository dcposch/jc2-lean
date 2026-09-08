import Grok610ScaleZeroCubicLoadWallsPart175Scratch
import Grok610ScaleZeroCubicLoadWallsPart197Scratch
import Grok610ScaleZeroCubicLoadWallsPart199Scratch

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

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CD_chamber_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hl : l = 0)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hB0 : B = 0 := cubicLoadSigmaConeCD610_B_eq_zero_of_chamber hcone hTle
  subst hB0
  have hbT := cubicLoadSigmaConeCD610_chamber_n1BetaTop hcone hTle rfl
  have hb0 : beta = 0 :=
    cubicN1_beta_eq_zero 0 alpha beta delta epsilon zeta eta theta
      A 0 C D E hbT rfl hmu hkap
  subst hb0
  have hdT := cubicLoadSigmaConeCD610_chamber_n1DeltaTop hcone hTle rfl
  have hd0 : delta = 0 :=
    cubicN1_delta_eq_zero 0 alpha 0 delta epsilon zeta eta theta
      A 0 C D E hdT rfl rfl hmu hkap
  subst hd0
  have hzT := cubicLoadSigmaConeCD610_chamber_n1ZetaTop hcone hTle rfl
  have hz0 : zeta = 0 :=
    cubicN1_zeta_eq_zero 0 alpha 0 0 epsilon zeta eta theta
      A 0 C D E hzT rfl rfl rfl hmu hkap
  subst hz0
  have htT := cubicLoadSigmaConeCD610_chamber_n1ThetaTop hcone hTle rfl
  have ht0 : theta = 0 :=
    cubicN1_theta_eq_zero 0 alpha 0 0 epsilon 0 eta theta
      A 0 C D E htT rfl rfl rfl rfl hmu hkap
  subst ht0
  have hAne := CubicLoadSigmaConeCD610_A_ne hcone
  have hCne : C ≠ 0 := hcone.2.1
  have hDne : D ≠ 0 := hcone.2.2.1
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne', hDne', heq, hBcmp, hEcmp⟩
    omega
  by_cases hEz : E = 0
  · subst hEz
    exact cubicLoadSigmaCone_CD_chamber_E0_impossible alpha epsilon eta
      A C D hAne hCne hDne hApos hCD hTle hcone.1 hlam hkap homi
  · have hEcmp : 2 * E.natDegree < 3 * C.natDegree := by
      rcases hcone with ⟨_, hCne', hDne', heq, hBcmp, hEcmp⟩
      rcases hEcmp with hE0 | hlt
      · exact (hEz hE0).elim
      · exact hlt
    exact cubicLoadSigmaCone_CD_chamber_Ene_impossible alpha epsilon eta
      A C D E hAne hCne hDne hEz hApos hCD hTle hEcmp hlam hkap homi

end CubicLoadCDChamber610

end Max11DegreeRoutes
