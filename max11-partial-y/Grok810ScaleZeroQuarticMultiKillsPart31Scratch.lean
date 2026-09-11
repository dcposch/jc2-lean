import Grok810ScaleZeroQuarticMultiKillsPart28Scratch
import Grok810ScaleZeroQuarticMultiKillsPart30Scratch

/-! Part 31 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

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

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBCD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCD810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBCD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroKappaQuarticNoBCD810_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
    Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    mul_one, one_mul, and_true, true_and, natDegree_zero]
  repeat' apply And.intro
  all_goals first
    | (right; right; omega)
    | (left; norm_num; done)
    | (right; left; simp; done)
    | trivial


theorem kappaQuarticFaceBCD810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCD810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (kappaQuarticFaceBCD810 A B C D E F G).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBCD810 B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt, hFlt, hGlt⟩
  simp only [kappaQuarticFaceBCD810, kappaQuarticInnerBCD810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hcf_B2D : ((B ^ 2 * D)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B2D, hcf_BC2]
  ring


set_option maxHeartbeats 16000000 in
def muQuarticFaceBCD810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3


set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoBCD810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2
  - (45 / 262144 * l : k) • (A ^ 4 * B)
  - (9 / 8192 * l : k) • (A ^ 3 * D)
  - (9 / 8192 * l : k) • (A ^ 2 * B * C)
  + (63 / 8192 * l : k) • (A * B ^ 3)
  - (9 / 1024 * l : k) • (A ^ 2 * F)
  - (9 / 512 * l : k) • (A * B * E)
  - (9 / 512 * l : k) • (A * C * D)
  - (63 / 1024 * l : k) • (B ^ 2 * D)
  - (63 / 1024 * l : k) • (B * C ^ 2)
  + (9 / 64 * l : k) • (B * G)
  + (9 / 64 * l : k) • (C * F)
  + (9 / 64 * l : k) • (D * E)
  - (7 / 8192 * beta : k) • (A ^ 3 * B)
  - (7 / 1024 * beta : k) • (A ^ 2 * D)
  + (7 / 512 * beta : k) • (A * B * C)
  + (21 / 1024 * beta : k) • B ^ 3
  - (7 / 64 * beta : k) • (A * F)
  - (7 / 64 * beta : k) • (B * E)
  - (7 / 64 * beta : k) • (C * D)
  + (3 / 128 * gamma : k) • (A * B ^ 2)
  - (3 / 16 * gamma : k) • (B * D)
  - (3 / 32 * gamma : k) • C ^ 2
  + (3 / 4 * gamma : k) • G
  - (5 / 1024 * delta : k) • (A ^ 2 * B)
  - (5 / 64 * delta : k) • (A * D)
  - (15 / 64 * delta : k) • (B * C)
  + (5 / 8 * delta : k) • F
  - (1 / 8 * epsilon : k) • B ^ 2
  + (1 / 2 * epsilon : k) • E
  - (3 / 64 * zeta : k) • (A * B)
  + (3 / 8 * zeta : k) • D
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B


end QuarticKills810
end Max11DegreeRoutes
end
