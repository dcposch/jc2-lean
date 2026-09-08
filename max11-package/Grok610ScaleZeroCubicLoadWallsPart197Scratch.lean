import Grok610ScaleZeroCubicLoadWallsPart187Scratch
import Grok610ScaleZeroCubicLoadWallsPart189Scratch
import Grok610ScaleZeroCubicLoadWallsPart191Scratch
import Grok610ScaleZeroCubicLoadWallsPart194Scratch

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
/-- Chamber `E = 0`: κ kills `α`, then ο has positive degree. -/
theorem cubicLoadSigmaCone_CD_chamber_E0_impossible
    (alpha epsilon eta : k) (A C D : k[X])
    (hAne : A ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hApos : 0 < A.natDegree)
    (hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hload : cubicLoadCompetes610 A 0 C D 0)
    (hlam : (degreeZeroLambdaCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D 0).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D 0).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D 0).natDegree = 0) :
    False := by
  have hCpos : 0 < C.natDegree := by
    have : ¬ C.natDegree = 0 := by
      intro hc0
      omega
    exact Nat.pos_of_ne_zero this
  have halpha0 : alpha = 0 := by
    by_contra halpha
    have hc : (4 / 9 * alpha : k) ≠ 0 :=
      mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) halpha
    have hlead :
        ((4 / 9 * alpha : k) • (C * D)).natDegree =
          C.natDegree + D.natDegree := by
      rw [natDegree_smul _ hc, natDegree_mul hCne hDne]
    have hrest :
        ((2 / 3 * epsilon : k) • D).natDegree <
          C.natDegree + D.natDegree := by
      refine (natDegree_smul_le610 _ _).trans_lt ?_
      have : D.natDegree < C.natDegree + D.natDegree := by omega
      exact this
    have hdeg :
        ((4 / 9 * alpha : k) • (C * D) + (2 / 3 * epsilon : k) • D).natDegree =
          C.natDegree + D.natDegree := by
      rw [← hlead]
      refine natDegree_add_eq_left_of_natDegree_lt ?_
      rw [hlead]
      exact hrest
    have hkap0 := hkap
    rw [degreeZeroKappaCubic610_eq_chamber alpha epsilon eta A C D 0,
      kappaChamberCD610_of_E_eq_zero] at hkap0
    rw [hdeg] at hkap0
    omega
  subst halpha0
  have h2c_gt : C.natDegree + 2 * D.natDegree < 2 * C.natDegree := by omega
  have heps0 : epsilon = 0 := by
    by_contra heps
    have hc : (-(1 / 9 * epsilon : k)) ≠ 0 :=
      neg_ne_zero.mpr
        (mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) heps)
    have hlead :
        ((-(1 / 9 * epsilon : k)) • C ^ 2).natDegree = 2 * C.natDegree := by
      rw [natDegree_smul _ hc, natDegree_pow]
    have hrest :
        ((-(5 / 27 : k)) • (C * D ^ 2)).natDegree < 2 * C.natDegree := by
      refine (natDegree_smul_le610 _ _).trans_lt ?_
      have : (C * D ^ 2).natDegree = C.natDegree + 2 * D.natDegree := by
        rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
      rw [this]
      exact h2c_gt
    have hdeg :
        ((-(5 / 27 : k)) • (C * D ^ 2) +
            (-(1 / 9 * epsilon : k)) • C ^ 2).natDegree =
          2 * C.natDegree := by
      rw [← hlead]
      refine natDegree_add_eq_right_of_natDegree_lt ?_
      rw [hlead]
      exact hrest
    have hom0 := homi
    rw [degreeZeroOmicronCubic610_eq_chamber 0 epsilon eta A C D 0,
      omicronChamberCD610_of_alpha_eq_zero_E_eq_zero] at hom0
    rw [hdeg] at hom0
    omega
  subst heps0
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have homi0 :
      omicronChamberCD610 0 0 eta A C D 0 =
        (-(5 / 27 : k)) • (C * D ^ 2) := by
    rw [omicronChamberCD610_of_alpha_eq_zero_E_eq_zero]
    have hC2 : (-(1 / 9 * (0 : k) : k)) • C ^ 2 = 0 := by
      have hz : (1 / 9 * (0 : k) : k) = 0 := by ring
      rw [hz, neg_zero, zero_smul]
    rw [hC2, add_zero]
  have hdeg :
      ((-(5 / 27 : k)) • (C * D ^ 2)).natDegree =
        C.natDegree + 2 * D.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul hCne (pow_ne_zero 2 hDne),
      natDegree_pow]
  have hom0 := homi
  rw [degreeZeroOmicronCubic610_eq_chamber 0 0 eta A C D 0, homi0, hdeg] at hom0
  omega

end CubicLoadCDChamber610

end Max11DegreeRoutes
