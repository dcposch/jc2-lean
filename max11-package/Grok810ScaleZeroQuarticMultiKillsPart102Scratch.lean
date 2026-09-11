import Grok810ScaleZeroQuarticDefsScratch
import Grok810ScaleZeroQuarticMultiKillsPart101Scratch

/-! Part 7 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


theorem muQuarticFaceCG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCG810 A B C D E F G)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceCG810 A B C D E F G).coeff (3 * C.natDegree) =
      (1 / 128 : k) * muQuarticInnerCG810 C.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hCpos, hGpos, hCG, hAlt, hBlt, hDlt, hElt, hFlt⟩
  simp only [muQuarticFaceCG810, muQuarticInnerCG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C3 : (C ^ 3).natDegree = 3 * C.natDegree := by
    rw [natDegree_pow]
  have hcf_C3 : (C ^ 3).coeff (3 * C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hCne hGne]
    omega
  have hcf_CG : ((C * G)).coeff (3 * C.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_C3, hcf_CG]
  ring


set_option maxHeartbeats 16000000 in
def piQuarticFaceCG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2


set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoCG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F


set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_CG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceCG810 A B C D E F G +
        degreeZeroPiQuarticNoCG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceCG810, degreeZeroPiQuarticNoCG810]
  all_goals module


end QuarticKills810
end Max11DegreeRoutes
end
/-! Part 10 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def omicronQuarticInnerABC810 (a b c : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + 60 * a ^ 2 * b * c ^ 2 + (-1120 : k) * a * b ^ 3 * c + (-336 : k) * b ^ 5 + 2880 * b * c ^ 3


def piQuarticInnerABC810 (a b c : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-360 : k) * a * b ^ 2 * c ^ 2 + (-560 : k) * b ^ 4 * c + 240 * c ^ 4


def primitiveQuarticInnerABC810 (a b c : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + 60 * a ^ 3 * b * c ^ 2 + 120 * a ^ 2 * b ^ 3 * c + 520 * a * b ^ 5 + (-960 : k) * a * b * c ^ 3 + (-8480 : k) * b ^ 3 * c ^ 2


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABC_identity
    (a b c : k) :
    ((-73 / 5120 : k) * a * b * c + (-21 / 2560 : k) * b ^ 3) * kappaQuarticInnerABC810 a b c +
      ((3 / 2560 : k) * a * b ^ 2 + (-1 / 80 : k) * c ^ 2) * muQuarticInnerABC810 a b c +
      ((-1 / 5120 : k) * b * c) * nuQuarticInnerABC810 a b c =
      c ^ 5 := by
  simp only [kappaQuarticInnerABC810, muQuarticInnerABC810, nuQuarticInnerABC810, xiQuarticInnerABC810, omicronQuarticInnerABC810, piQuarticInnerABC810, primitiveQuarticInnerABC810]
  ring


end QuarticKills810
end Max11DegreeRoutes
end
/-! Part 12 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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
theorem degreeZeroKappaQuarticNoABC810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABC810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABC810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt, hFlt, hGlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroKappaQuarticNoABC810_eq_polyOf]
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


theorem kappaQuarticFaceABC810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABC810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    : (kappaQuarticFaceABC810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 512 : k) * kappaQuarticInnerABC810 A.leadingCoeff B.leadingCoeff C.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt, hFlt, hGlt⟩
  simp only [kappaQuarticFaceABC810, kappaQuarticInnerABC810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB3, hcf_BC2]
  ring


set_option maxHeartbeats 16000000 in
def muQuarticFaceABC810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • C ^ 3


set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoABC810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
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
/-! Part 25 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoACG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
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


set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_ACG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceACG810 A B C D E F G +
        degreeZeroMuQuarticNoACG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceACG810, degreeZeroMuQuarticNoACG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroMuQuarticNoACG810` (41 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoACG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoACG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k), (5 / 32 : k), (-(45 / 262144 * l) : k),
      (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k), (63 / 8192 * l : k),
      (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k), (-(9 / 512 * l) : k),
      (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (-(7 / 8192 * beta) : k),
      (-(7 / 1024 * beta) : k), (7 / 512 * beta : k), (21 / 1024 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k),
      (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k), (-(5 / 64 * delta) : k),
      (-(15 / 64 * delta) : k), (5 / 8 * delta : k), (-(1 / 8 * epsilon) : k),
      (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k), (3 / 8 * zeta : k),
      (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0],
      [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuQuarticNoACG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoACG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACG810 A B C D E F G) :
    (degreeZeroMuQuarticNoACG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hGpos, hAC, hAG, hBlt, hDlt, hElt, hFlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroMuQuarticNoACG810_eq_polyOf]
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


end QuarticKills810
end Max11DegreeRoutes
end
/-! Part 26 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


theorem muQuarticFaceACG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceACG810 A B C D E F G).coeff (3 * C.natDegree) =
      (1 / 128 : k) * muQuarticInnerACG810 A.leadingCoeff C.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hGpos, hAC, hAG, hBlt, hDlt, hElt, hFlt⟩
  simp only [muQuarticFaceACG810, muQuarticInnerACG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C3 : (C ^ 3).natDegree = 3 * C.natDegree := by
    rw [natDegree_pow]
  have hcf_C3 : (C ^ 3).coeff (3 * C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hCne hGne]
    omega
  have hcf_CG : ((C * G)).coeff (3 * C.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_C3, hcf_CG]
  ring


set_option maxHeartbeats 16000000 in
def piQuarticFaceACG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2


set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoACG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F


set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_ACG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceACG810 A B C D E F G +
        degreeZeroPiQuarticNoACG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceACG810, degreeZeroPiQuarticNoACG810]
  all_goals module


end QuarticKills810
end Max11DegreeRoutes
end
/-! Part 29 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def omicronQuarticInnerBCD810 (b c d : k) : k :=
  (-21 : k) * b ^ 5 + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-160 : k) * d ^ 3


def piQuarticInnerBCD810 (b c d : k) : k :=
  (-35 : k) * b ^ 4 * c + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + 15 * c ^ 4


def primitiveQuarticInnerBCD810 (b c d : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 720 * b * c * d ^ 2 + 240 * c ^ 3 * d


set_option maxHeartbeats 32000000 in
theorem quarticInner_BCD_identity
    (b c d : k) :
    ((-16 / 105 : k) * b ^ 2 * c + (-64 / 49 : k) * d ^ 2) * kappaQuarticInnerBCD810 b c d +
      ((1 / 35 : k) * b ^ 3) * muQuarticInnerBCD810 b c d +
      ((16 / 49 : k) * b * d) * nuQuarticInnerBCD810 b c d =
      b ^ 7 := by
  simp only [kappaQuarticInnerBCD810, muQuarticInnerBCD810, nuQuarticInnerBCD810, xiQuarticInnerBCD810, omicronQuarticInnerBCD810, piQuarticInnerBCD810, primitiveQuarticInnerBCD810]
  ring


end QuarticKills810
end Max11DegreeRoutes
end
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
/-! Part 4 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroOmicronQuarticNoBE810` (99 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronQuarticNoBE810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroOmicronQuarticNoBE810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 65536) : k), (-(45 / 16384) : k), (15 / 16384 : k),
      (-(35 / 2048) : k), (-(5 / 2048) : k), (-(5 / 2048) : k),
      (-(5 / 2048) : k), (25 / 1024 : k), (15 / 512 : k),
      (35 / 1024 : k), (15 / 1024 : k), (135 / 1024 : k),
      (45 / 1024 : k), (-(5 / 128) : k), (-(5 / 128) : k),
      (-(15 / 128) : k), (-(5 / 32) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(5 / 128) : k), (5 / 16 : k),
      (135 / 33554432 * l : k), (225 / 2097152 * l : k), (-(171 / 4194304 * l) : k),
      (81 / 262144 * l : k), (-(9 / 65536 * l) : k), (99 / 131072 * l : k),
      (-(45 / 131072 * l) : k), (-(189 / 65536 * l) : k), (9 / 8192 * l : k),
      (-(9 / 4096 * l) : k), (27 / 8192 * l : k), (45 / 4096 * l : k),
      (99 / 4096 * l : k), (9 / 8192 * l : k), (189 / 8192 * l : k),
      (567 / 16384 * l : k), (9 / 512 * l : k), (-(9 / 256 * l) : k),
      (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k), (-(45 / 512 * l) : k),
      (-(45 / 1024 * l) : k), (-(27 / 512 * l) : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 2097152 * beta : k), (49 / 131072 * beta : k),
      (-(35 / 131072 * beta) : k), (7 / 8192 * beta : k), (-(7 / 4096 * beta) : k),
      (21 / 8192 * beta : k), (-(91 / 8192 * beta) : k), (-(189 / 32768 * beta) : k),
      (7 / 512 * beta : k), (7 / 512 * beta : k), (35 / 1024 * beta : k),
      (21 / 256 * beta : k), (7 / 512 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (3 / 2048 * gamma : k), (-(9 / 1024 * gamma) : k),
      (-(3 / 512 * gamma) : k), (3 / 128 * gamma : k), (3 / 128 * gamma : k),
      (9 / 128 * gamma : k), (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (9 / 131072 * delta : k), (5 / 4096 * delta : k),
      (-(5 / 4096 * delta) : k), (5 / 128 * delta : k), (5 / 512 * delta : k),
      (45 / 512 * delta : k), (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k),
      (-(15 / 128 * delta) : k), (-(1 / 256 * epsilon) : k), (1 / 32 * epsilon : k),
      (1 / 32 * epsilon : k), (-(1 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k),
      (-(3 / 16 * epsilon) : k), (9 / 32768 * zeta : k), (3 / 1024 * zeta : k),
      (9 / 512 * zeta : k), (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k),
      (3 / 8 * zeta : k), (-(1 / 512 * eta) : k), (-(1 / 32 * eta) : k),
      (-(3 / 32 * eta) : k), (1 / 4 * eta : k), (1 / 1024 * theta : k),
      (1 / 64 * theta : k), (-(3 / 128 * theta) : k), (1 / 8 * theta : k)]
      [
      [3, 3, 0, 0, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0],
      [2, 1, 0, 0, 0, 0, 1], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0],
      [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0], [0, 2, 1, 1, 0, 0, 0],
      [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1],
      [0, 1, 0, 1, 0, 1, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 1], [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0],
      [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0],
      [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0], [2, 0, 1, 0, 1, 0, 0],
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0], [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0],
      [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0],
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0],
      [2, 2, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0],
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [degreeZeroOmicronQuarticNoBE810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoBE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBE810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoBE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroOmicronQuarticNoBE810_eq_polyOf]
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


theorem omicronQuarticFaceBE810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBE810 A B C D E F G)
    (hBne : B ≠ 0)
    (hEne : E ≠ 0)
    : (omicronQuarticFaceBE810 A B C D E F G).coeff (5 * B.natDegree) =
      (1 / 4096 : k) * omicronQuarticInnerBE810 B.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt, hFlt, hGlt⟩
  simp only [omicronQuarticFaceBE810, omicronQuarticInnerBE810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 5 * B.natDegree := by
    rw [natDegree_pow]
  have hcf_B5 : (B ^ 5).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BE2 : ((B * E ^ 2)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_BE2 : ((B * E ^ 2)).coeff (5 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_BE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B5, hcf_B3E, hcf_BE2]
  ring


set_option maxHeartbeats 16000000 in
theorem quarticCone_BE_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBE810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hmuinner : muQuarticInnerBE810 B.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoBE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceBE810_coeff_top (hcone := hcone) (hBne := hBne) (hEne := hEne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt, hFlt, hGlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_BE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerBE810 B.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoBE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceBE810_coeff_top (hcone := hcone) (hBne := hBne) (hEne := hEne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt, hFlt, hGlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_BE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_BE_identity B.leadingCoeff E.leadingCoeff
  have hpow : B.leadingCoeff ^ 7 = 0 := by
    rw [hmuinner, homicroninner] at hid
    simpa using hid.symm
  have hlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  exact hlc ((pow_eq_zero_iff (by decide : (7 : ℕ) ≠ 0)).mp hpow)



end QuarticKills810
end Max11DegreeRoutes
end
/-! Part 8 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroPiQuarticNoCG810` (92 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPiQuarticNoCG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPiQuarticNoCG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 16) : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k),
      (45 / 131072 * l : k), (-(3 / 32768 * l) : k), (-(45 / 32768 * l) : k),
      (9 / 4096 * l : k), (9 / 4096 * l : k), (-(27 / 4096 * l) : k),
      (9 / 4096 * l : k), (-(189 / 4096 * l) : k), (-(63 / 4096 * l) : k),
      (-(27 / 1024 * l) : k), (9 / 512 * l : k), (63 / 1024 * l : k),
      (9 / 128 * l : k), (27 / 256 * l : k), (9 / 256 * l : k),
      (63 / 512 * l : k), (189 / 512 * l : k), (63 / 512 * l : k),
      (-(9 / 64 * l) : k), (-(9 / 32 * l) : k), (-(27 / 64 * l) : k),
      (-(9 / 32 * l) : k), (-(27 / 128 * l) : k), (-(9 / 16 * l) : k),
      (-(3 / 32 * l) : k), (9 / 8 * l : k), (7 / 4096 * beta : k),
      (7 / 4096 * beta : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (7 / 512 * beta : k), (-(21 / 256 * beta) : k), (-(7 / 256 * beta) : k),
      (-(63 / 512 * beta) : k), (-(7 / 64 * beta) : k), (7 / 32 * beta : k),
      (21 / 128 * beta : k), (7 / 16 * beta : k), (7 / 32 * beta : k),
      (7 / 32 * beta : k), (-(7 / 8 * beta) : k), (-(3 / 32 * gamma) : k),
      (-(15 / 256 * gamma) : k), (3 / 16 * gamma : k), (3 / 8 * gamma : k),
      (3 / 4 * gamma : k), (1 / 8 * gamma : k), (-(3 / 4 * gamma) : k),
      (-(3 / 4 * gamma) : k), (5 / 512 * delta : k), (-(15 / 256 * delta) : k),
      (-(5 / 128 * delta) : k), (5 / 32 * delta : k), (5 / 32 * delta : k),
      (15 / 32 * delta : k), (15 / 32 * delta : k), (-(5 / 8 * delta) : k),
      (-(5 / 4 * delta) : k), (1 / 4 * epsilon : k), (1 / 2 * epsilon : k),
      (-(1 / 2 * epsilon) : k), (-(1 * epsilon) : k), (-(1 / 2 * epsilon) : k),
      (3 / 32 * zeta : k), (5 / 32 * zeta : k), (-(3 / 8 * zeta) : k),
      (-(3 / 4 * zeta) : k), (-(3 / 4 * zeta) : k), (1 / 16 * eta : k),
      (-(1 / 2 * eta) : k), (-(1 / 4 * eta) : k), (2 * eta : k),
      (-(1 / 4 * theta) : k), (1 * theta : k)]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [4, 1, 1, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0],
      [4, 0, 0, 0, 0, 1, 0], [3, 1, 0, 0, 1, 0, 0], [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0],
      [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0],
      [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0],
      [1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1],
      [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0],
      [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0], [1, 2, 1, 0, 0, 0, 0],
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [degreeZeroPiQuarticNoCG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoCG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCG810 A B C D E F G) :
    (degreeZeroPiQuarticNoCG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * C.natDegree := by
  rcases hcone with ⟨hCpos, hGpos, hCG, hAlt, hBlt, hDlt, hElt, hFlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroPiQuarticNoCG810_eq_polyOf]
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


theorem piQuarticFaceCG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCG810 A B C D E F G)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceCG810 A B C D E F G).coeff (4 * C.natDegree) =
      (1 / 256 : k) * piQuarticInnerCG810 C.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hCpos, hGpos, hCG, hAlt, hBlt, hDlt, hElt, hFlt⟩
  simp only [piQuarticFaceCG810, piQuarticInnerCG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 4 * C.natDegree := by
    rw [natDegree_pow]
  have hcf_C4 : (C ^ 4).coeff (4 * C.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (4 * C.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_G2 : (G ^ 2).natDegree = 4 * C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (4 * C.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_C4, hcf_C2G, hcf_G2]
  ring


set_option maxHeartbeats 16000000 in
theorem quarticCone_CG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hGpos, hCG, hAlt, hBlt, hDlt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hGpos, hCG, hAlt, hBlt, hDlt, hElt, hFlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hmuinner : muQuarticInnerCG810 C.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoCG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceCG810_coeff_top (hcone := hcone) (hCne := hCne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hCpos, hGpos, hCG, hAlt, hBlt, hDlt, hElt, hFlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_CG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerCG810 C.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoCG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceCG810_coeff_top (hcone := hcone) (hCne := hCne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hCpos, hGpos, hCG, hAlt, hBlt, hDlt, hElt, hFlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_CG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 256 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_CG_identity C.leadingCoeff G.leadingCoeff
  have hpow : C.leadingCoeff ^ 5 = 0 := by
    rw [hmuinner, hpiinner] at hid
    simpa using hid.symm
  have hlc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)



end QuarticKills810
end Max11DegreeRoutes
end
