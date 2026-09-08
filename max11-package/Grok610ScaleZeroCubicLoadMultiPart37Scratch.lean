import Grok610ScaleZeroCubicLoadMultiPart05Scratch
import Grok610ScaleZeroCubicLoadMultiPart06Scratch
import Grok610ScaleZeroCubicLoadMultiPart07Scratch
import Grok610ScaleZeroCubicLoadMultiPart08Scratch
import Grok610ScaleZeroCubicLoadMultiPart18Scratch
import Grok610ScaleZeroCubicLoadMultiPart20Scratch
import Grok610ScaleZeroCubicLoadMultiPart22Scratch
import Grok610ScaleZeroCubicLoadMultiPart34Scratch
import Grok610ScaleZeroCubicLoadMultiPart35Scratch
import Grok610ScaleZeroCubicLoadMultiPart36Scratch

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

section CubicLoadSigmaBCEKill610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BCE_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
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
          eta theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hBne : B ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hEne, heq1, heq2, hDcmp⟩
    exact hBne
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hEne, heq1, heq2, hDcmp⟩
    exact hCne
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hEne, heq1, heq2, hDcmp⟩
    exact hEne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBCE610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBCE610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeBCE610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBCE610_specialize_theta hcone ht4
  have hkappainner :
      kappaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroKappaCubicNoSigmaBCE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hct := kappaCubicSigmaFaceBCE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz0 : (degreeZeroKappaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
      omega
    rw [degreeZeroKappaCubic610_eq_sigmaBCE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (1 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner :
      lambdaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroLambdaCubicNoSigmaBCE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hct := lambdaCubicSigmaFaceBCE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz0 : (degreeZeroLambdaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, _, heq1, heq2, _⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_sigmaBCE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (1 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner :
      omicronCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroOmicronCubicNoSigmaBCE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hct := omicronCubicSigmaFaceBCE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz0 : (degreeZeroOmicronCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, _, heq1, heq2, _⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_sigmaBCE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (1 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicSigmaInner_BCE_identity A.leadingCoeff B.leadingCoeff
      C.leadingCoeff E.leadingCoeff
  have hpow : C.leadingCoeff ^ 7 = 0 := by
    rw [hkappainner, hlambdainner, homicroninner] at hid
    simpa using hid.symm
  have hlc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact hlc ((pow_eq_zero_iff (by decide : (7 : ℕ) ≠ 0)).mp hpow)

end CubicLoadSigmaBCEKill610

end Max11DegreeRoutes
