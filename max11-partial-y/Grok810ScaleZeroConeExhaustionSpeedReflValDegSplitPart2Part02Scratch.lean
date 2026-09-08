import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Part01Scratch

/-! # Part 2 of `Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Scratch`.

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
theorem degreeZeroOmicronNoBE02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BE02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoBE02Polynomial810 l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, htie, hA, hC, hD, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroOmicronNoBE02Polynomial810, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0),
    zero_pow (by decide : (4 : ℕ) ≠ 0), zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0),
    hA, hC, hD, hF, hG]
  compute_degree
  simp only [hA, hC, hD, hF, hG, htie]
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoAD05_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AD05RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAD05Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hDpos, htie, hB, hC, hE, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroMuNoAD05Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hC, hE, hF,
    hG]
  compute_degree
  simp only [hB, hC, hE, hF, hG, htie]
  omega

end ExhaustRests810

end Max11DegreeRoutes
