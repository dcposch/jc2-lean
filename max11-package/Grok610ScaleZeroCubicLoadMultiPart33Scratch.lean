import Grok610ScaleZeroCubicLoadMultiPart01Scratch
import Grok610ScaleZeroCubicLoadMultiPart02Scratch
import Grok610ScaleZeroCubicLoadMultiPart03Scratch
import Grok610ScaleZeroCubicLoadMultiPart04Scratch
import Grok610ScaleZeroCubicLoadMultiPart14Scratch
import Grok610ScaleZeroCubicLoadMultiPart16Scratch
import Grok610ScaleZeroCubicLoadMultiPart31Scratch
import Grok610ScaleZeroCubicLoadMultiPart32Scratch

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

section CubicLoadSigmaBCKill610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BC_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hBne : B ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, heq, hDcmp, hEcmp⟩
    exact hBne
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, heq, hDcmp, hEcmp⟩
    exact hCne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBC610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBC610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeBC610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBC610_specialize_theta hcone ht4
  have hkappainner :
      kappaCubicSigmaInnerBC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroKappaCubicNoSigmaBC610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hct := kappaCubicSigmaFaceBC610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz0 : (degreeZeroKappaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
      omega
    rw [degreeZeroKappaCubic610_eq_sigmaBC_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (1 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner :
      lambdaCubicSigmaInnerBC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroLambdaCubicNoSigmaBC610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hct := lambdaCubicSigmaFaceBC610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz0 : (degreeZeroLambdaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, heq, _⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_sigmaBC_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (1 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicSigmaInner_BC_identity A.leadingCoeff B.leadingCoeff
      C.leadingCoeff
  have hpow : C.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hlambdainner] at hid
    simpa using hid.symm
  have hlc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)

end CubicLoadSigmaBCKill610

end Max11DegreeRoutes
