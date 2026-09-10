import Grok810ScaleZeroQuarticMultiKillsPart42Scratch

/-! Part 43 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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
theorem degreeZeroMuQuartic810_eq_CEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceCEG810 A B C D E F G +
        degreeZeroMuQuarticNoCEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceCEG810, degreeZeroMuQuarticNoCEG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroMuQuarticNoCEG810` (40 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoCEG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoCEG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k), (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k),
      (-(9 / 8192 * l) : k), (63 / 8192 * l : k), (-(9 / 1024 * l) : k),
      (-(9 / 512 * l) : k), (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k),
      (-(63 / 1024 * l) : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k),
      (7 / 512 * beta : k), (21 / 1024 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (3 / 128 * gamma : k),
      (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k),
      (-(5 / 1024 * delta) : k), (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k),
      (5 / 8 * delta : k), (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k),
      (-(3 / 64 * zeta) : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [4, 1, 0, 0, 0, 0, 0],
      [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0],
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuQuarticNoCEG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoCEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCEG810 A B C D E F G) :
    (degreeZeroMuQuarticNoCEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hEpos, hGpos, hCE, hCG, hAlt, hBlt, hDlt, hFlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroMuQuarticNoCEG810_eq_polyOf]
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


theorem muQuarticFaceCEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCEG810 A B C D E F G)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceCEG810 A B C D E F G).coeff (3 * C.natDegree) =
      (1 / 128 : k) * muQuarticInnerCEG810 C.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hCpos, hEpos, hGpos, hCE, hCG, hAlt, hBlt, hDlt, hFlt⟩
  simp only [muQuarticFaceCEG810, muQuarticInnerCEG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_E2 : (E ^ 2).natDegree = 3 * C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (3 * C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_C3, hcf_CG, hcf_E2]
  ring


end QuarticKills810
end Max11DegreeRoutes
end
