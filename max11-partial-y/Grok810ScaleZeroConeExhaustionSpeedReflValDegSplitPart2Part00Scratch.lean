import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart1Scratch

/-! # Part 0 of `Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Scratch`.

One declaration split out of `Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Scratch`; statements are byte-identical.
-/

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

section ExhaustRests810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoAC02_natDegree_lt_of_ABC0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ABC0RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAC02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, htie, h4b, h5b, hD, hE, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroXiNoAC02Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hD, hE, hF, hG]
  compute_degree
  simp only [hD, hE, hF, hG, htie, h4b, h5b]
  have h4a2b : 4 * A.natDegree + 2 * B.natDegree + 1 ≤ 7 * A.natDegree := by
    omega
  have ha4b : A.natDegree + 4 * B.natDegree + 1 ≤ 7 * A.natDegree := by omega
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoAE06_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE06RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAE06Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hEpos, htie, hB, hC, hD, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroMuNoAE06Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hC, hD, hF,
    hG]
  compute_degree
  simp only [hB, hC, hD, hF, hG, htie]
  omega

end ExhaustRests810

end Max11DegreeRoutes
