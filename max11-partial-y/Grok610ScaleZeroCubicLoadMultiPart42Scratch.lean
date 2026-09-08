import Grok610ScaleZeroCubicLoadMultiPart24Scratch
import Grok610ScaleZeroCubicLoadMultiPart26Scratch
import Grok610ScaleZeroCubicLoadMultiPart28Scratch
import Grok610ScaleZeroCubicLoadMultiPart30Scratch
import Grok610ScaleZeroCubicLoadMultiPart38Scratch
import Grok610ScaleZeroCubicLoadMultiPart39Scratch
import Grok610ScaleZeroCubicLoadMultiPart40Scratch
import Grok610ScaleZeroCubicLoadMultiPart41Scratch

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

section CubicLoadSigmaBCDEKill610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Off-wall N₁ + κ + λ + ο identity kill.  Strict N₁ bands so the odd
pure-`A` columns stay below the σ-7 face. -/
theorem cubicLoadSigmaCone_BCDE_offWall_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hl : l = 0)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) < 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) < 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree < 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) < 54 * A.natDegree + 42 * B.natDegree)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
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
    rcases hcone with ⟨_, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
    exact hBne
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
    exact hCne
  have hDne : D ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
    exact hDne
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
    exact hEne
  -- κ/λ/ο rest bounds use non-strict specialised bands; strict implies ≤.
  have hbLe : beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree := by
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (le_of_lt h)
  have hdLe : delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree := by
    rcases hd with h | h
    · exact Or.inl h
    · exact Or.inr (le_of_lt h)
  have hzLe : zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree := by
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr (le_of_lt h)
  have htLe : theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree := by
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (le_of_lt h)
  have hG1 :
      kappaCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroKappaCubicNoSigmaBCDE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hbLe hdLe hzLe htLe
    have hct := kappaCubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
    have hz0 : (degreeZeroKappaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
      omega
    rw [degreeZeroKappaCubic610_eq_sigmaBCDE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hG2 :
      lambdaCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroLambdaCubicNoSigmaBCDE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hbLe hdLe hzLe htLe
    have hct := lambdaCubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
    have hz0 : (degreeZeroLambdaCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, _, _, heq1, heq2, heq3⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_sigmaBCDE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hG3 :
      omicronCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest :=
      degreeZeroOmicronCubicNoSigmaBCDE610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hbLe hdLe hzLe htLe
    have hct := omicronCubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
    have hz0 : (degreeZeroOmicronCubic610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, _, _, heq1, heq2, heq3⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_sigmaBCDE_add_rest, coeff_add,
      coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz0
    have hden : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hG4 :
      n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff = 0 := by
    have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha beta delta epsilon
        zeta eta theta A B C D E hmu hkap
    have hΔ : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
      rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
        _, _, _, _, heq1, heq2, heq3⟩
      omega
    have hrest :=
      degreeZeroN1CubicNoSigmaBCDENoL610_natDegree_lt_of_loadCone alpha beta
        delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
    have hz0 : (degreeZeroN1Cubic610 0 alpha beta delta epsilon zeta eta theta
          A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 :=
      coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hΔ)
    rw [degreeZeroN1Cubic610_eq_sigmaBCDE_add_rest,
      degreeZeroN1CubicNoSigmaBCDE610_eq_L_add_rest, coeff_add, coeff_add] at hz0
    have hsmall :
        (degreeZeroN1CubicNoSigmaBCDENoL610 0 alpha beta delta epsilon zeta
            eta theta A B C D E).coeff
          (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 :=
      coeff_eq_zero_of_natDegree_lt hrest
    have hL0 : (n1CubicLFace610 0 A).coeff
        (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 := by
      simp only [n1CubicLFace610, mul_zero, zero_smul, coeff_zero]
    rw [hsmall, hL0, add_zero, add_zero] at hz0
    have hct := n1CubicSigmaFaceBCDE610_coeff_top_of_loadCone
      (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
      (hDne := hDne) (hEne := hEne)
    have hden : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz0)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicSigmaInner_BCDE_identity A.leadingCoeff B.leadingCoeff
      C.leadingCoeff D.leadingCoeff E.leadingCoeff
  have hpow : E.leadingCoeff ^ 5 = 0 := by
    rw [hG1, hG2, hG3, hG4] at hid
    simpa using hid.symm
  have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)

end CubicLoadSigmaBCDEKill610

end Max11DegreeRoutes
