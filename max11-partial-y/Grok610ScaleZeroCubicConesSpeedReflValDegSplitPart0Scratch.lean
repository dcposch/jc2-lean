import Grok610ScaleZeroCubicConesSpeedReflValDegSplitBaseScratch

/-! # SPEED: theorems of `Grok610ScaleZeroCubicConesSpeedReflValDegScratch`, part 0 of 16, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

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

section CubicCoordinates610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicC610_add (A C0 : k[X]) :
    cubicC610 A C0 + (1 / 3 : k) • A ^ 2 = C0 := by
  simp only [cubicC610]
  exact sub_add_cancel _ _


theorem cubicD610_add (A B D0 : k[X]) :
    cubicD610 A B D0 + (1 / 3 : k) • (A * B) = D0 := by
  simp only [cubicD610]
  exact sub_add_cancel _ _


set_option maxHeartbeats 8000000 in
theorem cubicE610_inv (A C0 E0 : k[X]) :
    E0 =
      cubicE610 A C0 E0 + (1 / 3 : k) • (A * cubicC610 A C0) +
        (1 / 27 : k) • A ^ 3 := by
  simp only [cubicC610, cubicE610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


end CubicCoordinates610

section CubicIntegrals610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveCubic610_eq_flat
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E =
      degreeZeroPrimitiveCubicFlat610 l alpha beta delta epsilon zeta
        eta theta A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroPrimitiveCubic610,
    degreeZeroPrimitiveCubicFlat610, degreeZeroBaseGroupCubic610,
    degreeZeroAlphaGroupCubic610, degreeZeroBetaGroupCubic610,
    degreeZeroDeltaGroupCubic610, degreeZeroEpsilonGroupCubic610,
    degreeZeroZetaGroupCubic610, degreeZeroEtaGroupCubic610,
    degreeZeroThetaGroupCubic610, smul_add, smul_sub, smul_smul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring



end CubicIntegrals610

section CubicTransport610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta theta
        A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E := by
  simp only [degreeZeroKappaPolynomial610, degreeZeroKappaCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta theta
        A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E := by
  simp only [degreeZeroLambdaPolynomial610, degreeZeroLambdaCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
        A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E := by
  simp only [degreeZeroMuPolynomial610, degreeZeroMuCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroRawFourthTailPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroRawFourthTailPolynomial610 l alpha beta delta epsilon
        zeta eta theta A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroRawFourthTailCubic610 l alpha beta delta epsilon zeta
        eta theta A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroRawFourthTailPolynomial610, degreeZeroRawFourthTailCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E := by
  simp only [degreeZeroOmicronPolynomial610]
  rw [degreeZeroRawFourthTailPolynomial610_eq_cubic,
    degreeZeroKappaPolynomial610_eq_cubic,
    degreeZeroLambdaPolynomial610_eq_cubic]
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroOmicronCubic610, degreeZeroRawFourthTailCubic610, degreeZeroKappaCubic610, degreeZeroLambdaCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroBaseGroupPolynomial610_eq_cubic
    (l : k) (A B C D E : k[X]) :
    degreeZeroBaseGroupPolynomial610 l A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroBaseGroupCubic610 l A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroBaseGroupPolynomial610, degreeZeroBaseGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroAlphaGroupPolynomial610_eq_cubic
    (A B C D E : k[X]) :
    degreeZeroAlphaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroAlphaGroupCubic610 A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroAlphaGroupPolynomial610, degreeZeroAlphaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroBetaGroupPolynomial610_eq_cubic
    (A B C D E : k[X]) :
    degreeZeroBetaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroBetaGroupCubic610 A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroBetaGroupPolynomial610, degreeZeroBetaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroDeltaGroupPolynomial610_eq_cubic
    (A B C D : k[X]) :
    degreeZeroDeltaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B)) =
      degreeZeroDeltaGroupCubic610 A B C D := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroDeltaGroupPolynomial610, degreeZeroDeltaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroEpsilonGroupPolynomial610_eq_cubic
    (A B C D : k[X]) :
    degreeZeroEpsilonGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B)) =
      degreeZeroEpsilonGroupCubic610 A B C D := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroEpsilonGroupPolynomial610, degreeZeroEpsilonGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroZetaGroupPolynomial610_eq_cubic
    (A B C D : k[X]) :
    degreeZeroZetaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B)) =
      degreeZeroZetaGroupCubic610 A B C D := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroZetaGroupPolynomial610, degreeZeroZetaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroEtaGroupPolynomial610_eq_cubic
    (A B C D : k[X]) :
    degreeZeroEtaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B)) =
      degreeZeroEtaGroupCubic610 A B C D := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroEtaGroupPolynomial610, degreeZeroEtaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroThetaGroupPolynomial610_eq_cubic
    (A B C E : k[X]) :
    degreeZeroThetaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2)
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroThetaGroupCubic610 A B C E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroThetaGroupPolynomial610, degreeZeroThetaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitivePolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
        eta theta A B (C + (1 / 3 : k) • A ^ 2)
        (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveCubic610, degreeZeroBaseGroupPolynomial610_eq_cubic,
    degreeZeroAlphaGroupPolynomial610_eq_cubic,
    degreeZeroBetaGroupPolynomial610_eq_cubic,
    degreeZeroDeltaGroupPolynomial610_eq_cubic,
    degreeZeroEpsilonGroupPolynomial610_eq_cubic,
    degreeZeroZetaGroupPolynomial610_eq_cubic,
    degreeZeroEtaGroupPolynomial610_eq_cubic,
    degreeZeroThetaGroupPolynomial610_eq_cubic]
  all_goals module



end CubicTransport610

end Max11DegreeRoutes

end
