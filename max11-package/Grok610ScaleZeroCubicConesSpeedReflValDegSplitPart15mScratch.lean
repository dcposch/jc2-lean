import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart15lScratch

noncomputable section

open scoped Polynomial.Bivariate
open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8000000

section CubicKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem cubicCone_ABCDE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCDE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoABCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceABCDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
      omega
    rw [degreeZeroKappaCubic610_eq_ABCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoABCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceABCDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_ABCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoABCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceABCDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
      omega
    rw [degreeZeroMuCubic610_eq_ABCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1458 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronCubicNoABCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := omicronCubicFaceABCDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_ABCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 486 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoABCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceABCDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_ABCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2916 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_ABCDE_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff
  have hpow : D.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, homicroninner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)

end CubicKills610

end Max11DegreeRoutes

end
