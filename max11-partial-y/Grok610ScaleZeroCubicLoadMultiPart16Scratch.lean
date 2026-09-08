import Grok610ScaleZeroCubicLoadMultiPart15Scratch

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

section CubicLoadSigmaBC610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaBC610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBC610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroLambdaCubicNoSigmaBC610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, heq, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have htieBC : 4 * A.natDegree + 2 * B.natDegree =
      3 * A.natDegree + 2 * C.natDegree := heq
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := by
    rcases hDcmp with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := by
    rcases hEcmp with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rw [speedRefl_degreeZeroLambdaCubicNoSigmaBC610_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial

end CubicLoadSigmaBC610

end Max11DegreeRoutes
