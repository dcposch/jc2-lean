import Grok610ScaleZeroCubicLoadWallsPart84Scratch

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

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicBCDEWallBetaRest610_chunk1_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN1CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 14 * B.natDegree = 15 * A.natDegree := by omega
  have hface : A.natDegree + 2 * B.natDegree + D.natDegree = 5 * A.natDegree := by omega
  have hBpos : 0 + 1 ≤ B.natDegree := by omega
  have hCpos : 0 + 1 ≤ C.natDegree := by omega
  have hDpos : 0 + 1 ≤ D.natDegree := by omega
  have hEpos : 0 + 1 ≤ E.natDegree := by omega
  rw [speedRefl_degreeZeroN1CubicBCDEWallBetaRest610_chunk1_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
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

end CubicLoadWallRests610

end Max11DegreeRoutes
