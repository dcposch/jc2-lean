import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart0Scratch

/-! # SPEED: theorems of `Grok810ScaleZeroConeExhaustionSpeedReflValDegScratch`, part 1 of 8, so that no single
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

section ExhaustCombined810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_eq_BE02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muBE02Combined810 B E0 +
        degreeZeroMuNoBE02Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuPolynomial810, muBE02Combined810,
    degreeZeroMuNoBE02Polynomial810]
  module


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronPolynomial810_eq_BE02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      omicronBE02Combined810 B E0 +
        degreeZeroOmicronNoBE02Polynomial810 l beta gamma delta epsilon
          zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroOmicronPolynomial810, omicronBE02Combined810,
    degreeZeroOmicronNoBE02Polynomial810]
  module


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_eq_AD05_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muAD05Combined810 A D0 +
        degreeZeroMuNoAD05Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuPolynomial810, muAD05Combined810,
    degreeZeroMuNoAD05Polynomial810]
  module


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiPolynomial810_eq_AD05_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      xiAD05Combined810 A D0 +
        degreeZeroXiNoAD05Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroXiPolynomial810, xiAD05Combined810,
    degreeZeroXiNoAD05Polynomial810]
  module


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiPolynomial810_eq_C0E0_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      xiC0E0Face810 C0 E0 +
        degreeZeroXiNoC0E0Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroXiPolynomial810, xiC0E0Face810,
    degreeZeroXiNoC0E0Polynomial810]
  module


end ExhaustCombined810

section ExhaustRests810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoA6_natDegree_lt_of_mixedB
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedBCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hBpos, h3, hC, hD, hE, hF, hG⟩
  unfold degreeZeroMuNoA6Polynomial810
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul,
    zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0),
    zero_pow (by decide : (7 : ℕ) ≠ 0), hC, hD, hE, hF, hG,
    eq_self_iff_true, true_or, or_true, and_true, true_and]
  repeat' apply And.intro
  all_goals first | omega | exact Or.inr (Or.inr (by omega))


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoA6_natDegree_lt_of_mixedC0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedC0Cone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hAC, h2, hB, hD, hE, hF, hG⟩
  unfold degreeZeroMuNoA6Polynomial810
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul,
    zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0),
    zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hD, hE, hF, hG,
    eq_self_iff_true, true_or, or_true, and_true, true_and]
  repeat' apply And.intro
  all_goals first | omega | exact Or.inr (Or.inr (by omega))


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoA6_natDegree_lt_of_mixedD0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedD0Cone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hDpos, h5, hB, hC, hE, hF, hG⟩
  unfold degreeZeroMuNoA6Polynomial810
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul,
    zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0),
    zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hC, hE, hF, hG,
    eq_self_iff_true, true_or, or_true, and_true, true_and]
  repeat' apply And.intro
  all_goals first | omega | exact Or.inr (Or.inr (by omega))


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoA6_natDegree_lt_of_AE03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE03RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hEpos, htie, hB, hC, hD, hF, hG⟩
  unfold degreeZeroMuNoA6Polynomial810
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul,
    zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0),
    zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hC, hD, hF, hG,
    eq_self_iff_true, true_or, or_true, and_true, true_and]
  repeat' apply And.intro
  all_goals first | omega | exact Or.inr (Or.inr (by omega))


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoA6_natDegree_lt_of_AF07
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AF07RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hFpos, htie, hB, hC, hD, hE, hG⟩
  unfold degreeZeroMuNoA6Polynomial810
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul,
    zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0),
    zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hC, hD, hE, hG,
    eq_self_iff_true, true_or, or_true, and_true, true_and]
  repeat' apply And.intro
  all_goals first | omega | exact Or.inr (Or.inr (by omega))


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoAC02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AC02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAC02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hCpos, htie, hB, hD, hE, hF, hG⟩
  unfold degreeZeroMuNoAC02Polynomial810
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul,
    zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0),
    zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hD, hE, hF, hG,
    eq_self_iff_true, true_or, or_true, and_true, true_and]
  repeat' apply And.intro
  all_goals first | omega | exact Or.inr (Or.inr (by omega))


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoAC02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AC02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAC02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hCpos, htie, hB, hD, hE, hF, hG⟩
  unfold degreeZeroXiNoAC02Polynomial810
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul,
    zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0),
    zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hD, hE, hF, hG,
    eq_self_iff_true, true_or, or_true, and_true, true_and]
  repeat' apply And.intro
  all_goals first | omega | exact Or.inr (Or.inr (by omega))


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoAC02_natDegree_lt_of_ABC0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ABC0RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAC02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, htie, h4b, h5b, hD, hE, hF, hG⟩
  unfold degreeZeroMuNoAC02Polynomial810
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul,
    zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0),
    zero_pow (by decide : (7 : ℕ) ≠ 0), hD, hE, hF, hG,
    eq_self_iff_true, true_or, or_true, and_true, true_and]
  repeat' apply And.intro
  all_goals first | omega | exact Or.inr (Or.inr (by omega))


end ExhaustRests810

end Max11DegreeRoutes

end
