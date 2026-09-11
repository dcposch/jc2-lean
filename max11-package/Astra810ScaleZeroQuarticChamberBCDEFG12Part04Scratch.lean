import Astra810ScaleZeroQuarticChamberBCDEFG12Part02Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part03Scratch

/-! # BCDEFG12 chamber, part 4

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
-/

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

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- The auxiliary kills l whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_l_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 11 * A.natDegree)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    l = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticBetaTowerFace810 beta A + n7QuarticDeltaTowerFace810 delta A + n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 8 * A.natDegree := by
    simp only [S, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticLTowerFace810 l A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    dsimp [S]
    abel
  have hlead : (n7QuarticLTowerFace810 l A).natDegree = 8 * A.natDegree := by
    simp only [n7QuarticLTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills beta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_beta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 9 * A.natDegree)
    (hl0 : l = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    beta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticDeltaTowerFace810 delta A + n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 7 * A.natDegree := by
    simp only [S, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticBetaTowerFace810 beta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, n7QuarticLTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticBetaTowerFace810 beta A).natDegree = 7 * A.natDegree := by
    simp only [n7QuarticBetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills delta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_delta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 7 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    delta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 6 * A.natDegree := by
    simp only [S, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticDeltaTowerFace810 delta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticDeltaTowerFace810 delta A).natDegree = 6 * A.natDegree := by
    simp only [n7QuarticDeltaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills zeta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_zeta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 5 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    zeta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inl hdelta0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 5 * A.natDegree := by
    simp only [S, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticZetaTowerFace810 zeta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, hdelta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticZetaTowerFace810 zeta A).natDegree = 5 * A.natDegree := by
    simp only [n7QuarticZetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills theta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_theta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 3 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (hzeta0 : zeta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    theta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inl hdelta0
    · exact Or.inl hzeta0
    · exact Or.inr (by omega)
  have hrem := hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticThetaTowerFace810 theta A +
      (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, hdelta0, hzeta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
  have hlead : (n7QuarticThetaTowerFace810 theta A).natDegree = 4 * A.natDegree := by
    simp only [n7QuarticThetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

end Max11DegreeRoutes
