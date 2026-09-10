import Grok610ScaleZeroConeCascadePart01Scratch
import Grok610ScaleZeroConeCascadePart06Scratch
import Grok610ScaleZeroConeCascadePart08Scratch
import Grok610ScaleZeroConeCascadePart10Scratch
import Grok610ScaleZeroConeCascadePart37Scratch
import Max11SpeedReflectDegLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighACone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the unique-high-A rest bound. -/
private theorem cascade55SpeedT_degreeZeroBaseGroupHighA_noA6B_Rest610_eq_polyOf
    (l : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroBaseGroupHighA_noA6B_Rest610 l A B C0 D0 E0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0]
      [
      (113724 / 2239488 * l : k), (92160 / 2239488 : k), (301806 / 2239488 * l : k),
      (491520 / 2239488 : k), (-(122472 / 2239488 * l) : k), (343040 / 2239488 : k),
      (-(769824 / 2239488 * l) : k), (-(483840 / 2239488) : k), (-(384912 / 2239488 * l) : k),
      (-(668160 / 2239488) : k), (-(1224720 / 2239488 * l) : k), (-(1071360 / 2239488) : k),
      (-(1071360 / 2239488) : k), (699840 / 2239488 * l : k), (559872 / 2239488 * l : k),
      (622080 / 2239488 : k), (-(209952 / 2239488 * l) : k), (-(737280 / 2239488) : k),
      (839808 / 2239488 * l : k), (2519424 / 2239488 * l : k), (1658880 / 2239488 : k),
      (1244160 / 2239488 : k), (419904 / 2239488 * l : k), (1244160 / 2239488 : k),
      (-(36864 / 2239488) : k), (419904 / 2239488 * l : k), (276480 / 2239488 : k),
      (629856 / 2239488 * l : k), (1244160 / 2239488 : k), (414720 / 2239488 : k),
      (-(1679616 / 2239488 * l) : k), (-(839808 / 2239488 * l) : k), (-(1679616 / 2239488 * l) : k),
      (-(2488320 / 2239488) : k), (-(829440 / 2239488) : k)]
      [
      [5, 0, 1, 0, 0], [5, 0, 0, 1, 0], [4, 2, 0, 0, 0], [4, 1, 1, 0, 0],
      [4, 0, 0, 0, 1], [3, 3, 0, 0, 0], [3, 1, 0, 1, 0], [3, 1, 0, 0, 1],
      [3, 0, 2, 0, 0], [3, 0, 1, 1, 0], [2, 2, 1, 0, 0], [2, 2, 0, 1, 0],
      [2, 1, 2, 0, 0], [2, 0, 1, 0, 1], [2, 0, 0, 2, 0], [2, 0, 0, 1, 1],
      [1, 4, 0, 0, 0], [1, 3, 1, 0, 0], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0],
      [1, 1, 1, 0, 1], [1, 1, 0, 2, 0], [1, 0, 3, 0, 0], [1, 0, 2, 1, 0],
      [0, 5, 0, 0, 0], [0, 3, 0, 1, 0], [0, 3, 0, 0, 1], [0, 2, 2, 0, 0],
      [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1],
      [0, 0, 1, 2, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0]] := by
  simp only [degreeZeroBaseGroupHighA_noA6B_Rest610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the unique-high-A rest bound. -/
private theorem cascade55SpeedT_degreeZeroAlphaGroupPolynomial610_eq_polyOf
    (A B C0 D0 E0 : k[X]) :
    degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0]
      [
      (35 / 729 : k), (-(51 / 729) : k), (-(222 / 729) : k),
      (-(117 / 729) : k), (189 / 729 : k), (297 / 729 : k),
      (324 / 729 : k), (324 / 729 : k), (-(324 / 729) : k),
      (108 / 729 : k), (-(324 / 729) : k), (-(324 / 729) : k),
      (-(324 / 729) : k)]
      [
      [5, 1, 0, 0, 0], [4, 0, 0, 1, 0], [3, 1, 1, 0, 0], [2, 3, 0, 0, 0],
      [2, 1, 0, 0, 1], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0],
      [1, 0, 0, 1, 1], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [0, 0, 2, 1, 0]] := by
  simp only [degreeZeroAlphaGroupPolynomial610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the unique-high-A rest bound. -/
private theorem cascade55SpeedT_degreeZeroBetaGroupPolynomial610_eq_polyOf
    (A B C0 D0 E0 : k[X]) :
    degreeZeroBetaGroupPolynomial610 A B C0 D0 E0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0]
      [
      (2695 / 559872 : k), (-(23940 / 559872) : k), (-(51660 / 559872) : k),
      (21168 / 559872 : k), (127008 / 559872 : k), (63504 / 559872 : k),
      (136080 / 559872 : k), (-(108864 / 559872) : k), (-(108864 / 559872) : k),
      (11340 / 559872 : k), (-(54432 / 559872) : k), (-(217728 / 559872) : k),
      (-(36288 / 559872) : k), (326592 / 559872 : k)]
      [
      [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
      [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [1, 0, 1, 0, 1],
      [1, 0, 0, 2, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2]] := by
  simp only [degreeZeroBetaGroupPolynomial610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the unique-high-A rest bound. -/
private theorem cascade55SpeedT_degreeZeroDeltaGroupPolynomial610_eq_polyOf
    (A B C0 D0 : k[X]) :
    degreeZeroDeltaGroupPolynomial610 A B C0 D0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0]
      [
      (49 / 5184 : k), (-(360 / 5184) : k), (-(600 / 5184) : k),
      (1440 / 5184 : k), (720 / 5184 : k), (720 / 5184 : k),
      (-(2160 / 5184) : k)]
      [
      [5, 0, 0, 0], [3, 0, 1, 0], [2, 2, 0, 0], [1, 1, 0, 1],
      [1, 0, 2, 0], [0, 2, 1, 0], [0, 0, 0, 2]] := by
  simp only [degreeZeroDeltaGroupPolynomial610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the unique-high-A rest bound. -/
private theorem cascade55SpeedT_degreeZeroEpsilonGroupPolynomial610_eq_polyOf
    (A B C0 D0 : k[X]) :
    degreeZeroEpsilonGroupPolynomial610 A B C0 D0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0]
      [
      (-(7 / 54) : k), (9 / 54 : k), (24 / 54 : k),
      (4 / 54 : k), (-(36 / 54) : k)]
      [
      [3, 1, 0, 0], [2, 0, 0, 1], [1, 1, 1, 0], [0, 3, 0, 0],
      [0, 0, 1, 1]] := by
  simp only [degreeZeroEpsilonGroupPolynomial610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the unique-high-A rest bound. -/
private theorem cascade55SpeedT_degreeZeroZetaGroupPolynomial610_eq_polyOf
    (A B C0 D0 : k[X]) :
    degreeZeroZetaGroupPolynomial610 A B C0 D0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0]
      [
      (-(7 / 192) : k), (40 / 192 : k), (48 / 192 : k),
      (-(96 / 192) : k), (-(48 / 192) : k)]
      [
      [4, 0, 0, 0], [2, 0, 1, 0], [1, 2, 0, 0], [0, 1, 0, 1],
      [0, 0, 2, 0]] := by
  simp only [degreeZeroZetaGroupPolynomial610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the unique-high-A rest bound. -/
private theorem cascade55SpeedT_degreeZeroEtaGroupPolynomial610_eq_polyOf
    (A B C0 D0 : k[X]) :
    degreeZeroEtaGroupPolynomial610 A B C0 D0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0]
      [
      (7 / 36 : k), (-(12 / 36) : k), (-(12 / 36) : k)]
      [
      [2, 1, 0, 0], [1, 0, 0, 1], [0, 1, 1, 0]] := by
  simp only [degreeZeroEtaGroupPolynomial610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the unique-high-A rest bound. -/
private theorem cascade55SpeedT_degreeZeroThetaGroupPolynomial610_eq_polyOf
    (A B C0 E0 : k[X]) :
    degreeZeroThetaGroupPolynomial610 A B C0 E0 =
      Max11ReflectDeg.polyOf [A, B, C0, E0]
      [
      (7 / 216 : k), (-(36 / 216) : k), (-(18 / 216) : k),
      (216 / 216 : k)]
      [
      [3, 0, 0, 0], [1, 0, 1, 0], [0, 2, 0, 0], [0, 0, 0, 1]] := by
  simp only [degreeZeroThetaGroupPolynomial610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem uniqueHighA_impossible_of_l_zero_B_pos610
    (alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A B C0 D0 E0)
    (hBpos : 0 < B.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hc : (-(62720 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(62720 / 2239488 : k)) • (A ^ 6 * B)).natDegree =
        6 * A.natDegree + B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 6 hA) hBne,
      natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighA_noA6B_Rest610 0 alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0).natDegree <
        6 * A.natDegree + B.natDegree := by
    rcases hcone with ⟨hApos, hBlt, hC, hD, hE⟩
    have hbase :
        (degreeZeroBaseGroupHighA_noA6B_Rest610 0 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      rw [cascade55SpeedT_degreeZeroBaseGroupHighA_noA6B_Rest610_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      rw [cascade55SpeedT_degreeZeroAlphaGroupPolynomial610_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      rw [cascade55SpeedT_degreeZeroBetaGroupPolynomial610_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      rw [cascade55SpeedT_degreeZeroDeltaGroupPolynomial610_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      rw [cascade55SpeedT_degreeZeroEpsilonGroupPolynomial610_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      rw [cascade55SpeedT_degreeZeroZetaGroupPolynomial610_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      rw [cascade55SpeedT_degreeZeroEtaGroupPolynomial610_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      rw [cascade55SpeedT_degreeZeroThetaGroupPolynomial610_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    simp only [degreeZeroPrimitiveHighA_noA6B_Rest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_A6B_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end HighACone610

end Max11DegreeRoutes
