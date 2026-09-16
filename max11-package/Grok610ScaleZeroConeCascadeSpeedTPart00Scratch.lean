import Grok610ScaleZeroConeCascadePart101Scratch
import Max11SpeedReflectDegLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroAlphaGroupPolynomial610
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
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroAlphaGroupPolynomial610
    (A B C0 D0 E0 : k[X]) :
    (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree, E0.natDegree]
      [
      [5, 1, 0, 0, 0], [4, 0, 0, 1, 0], [3, 1, 1, 0, 0], [2, 3, 0, 0, 0],
      [2, 1, 0, 0, 1], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0],
      [1, 0, 0, 1, 1], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [0, 0, 2, 1, 0]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroAlphaGroupPolynomial610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroBetaGroupPolynomial610
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
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroBetaGroupPolynomial610
    (A B C0 D0 E0 : k[X]) :
    (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree, E0.natDegree]
      [
      [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
      [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [1, 0, 1, 0, 1],
      [1, 0, 0, 2, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroBetaGroupPolynomial610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroBetaGroupNoA6Polynomial610
    (A B C0 D0 E0 : k[X]) :
    degreeZeroBetaGroupNoA6Polynomial610 A B C0 D0 E0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0]
      [
      (-(23940 / 559872) : k), (-(51660 / 559872) : k), (21168 / 559872 : k),
      (127008 / 559872 : k), (63504 / 559872 : k), (136080 / 559872 : k),
      (-(108864 / 559872) : k), (-(108864 / 559872) : k), (11340 / 559872 : k),
      (-(54432 / 559872) : k), (-(217728 / 559872) : k), (-(36288 / 559872) : k),
      (326592 / 559872 : k)]
      [
      [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
      [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 2, 0],
      [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2]] := by
  simp only [degreeZeroBetaGroupNoA6Polynomial610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroBetaGroupNoA6Polynomial610
    (A B C0 D0 E0 : k[X]) :
    (degreeZeroBetaGroupNoA6Polynomial610 A B C0 D0 E0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree, E0.natDegree]
      [
      [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
      [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 2, 0],
      [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroBetaGroupNoA6Polynomial610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroBetaGroupNoE2Polynomial610
    (A B C0 D0 E0 : k[X]) :
    degreeZeroBetaGroupNoE2Polynomial610 A B C0 D0 E0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0]
      [
      (2695 / 559872 : k), (-(23940 / 559872) : k), (-(51660 / 559872) : k),
      (21168 / 559872 : k), (127008 / 559872 : k), (63504 / 559872 : k),
      (136080 / 559872 : k), (-(108864 / 559872) : k), (-(108864 / 559872) : k),
      (11340 / 559872 : k), (-(54432 / 559872) : k), (-(217728 / 559872) : k),
      (-(36288 / 559872) : k)]
      [
      [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
      [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [1, 0, 1, 0, 1],
      [1, 0, 0, 2, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0]] := by
  simp only [degreeZeroBetaGroupNoE2Polynomial610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroBetaGroupNoE2Polynomial610
    (A B C0 D0 E0 : k[X]) :
    (degreeZeroBetaGroupNoE2Polynomial610 A B C0 D0 E0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree, E0.natDegree]
      [
      [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
      [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [1, 0, 1, 0, 1],
      [1, 0, 0, 2, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroBetaGroupNoE2Polynomial610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroDeltaGroupPolynomial610
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
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroDeltaGroupPolynomial610
    (A B C0 D0 : k[X]) :
    (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree]
      [
      [5, 0, 0, 0], [3, 0, 1, 0], [2, 2, 0, 0], [1, 1, 0, 1],
      [1, 0, 2, 0], [0, 2, 1, 0], [0, 0, 0, 2]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroDeltaGroupPolynomial610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroEpsilonGroupPolynomial610
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
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroEpsilonGroupPolynomial610
    (A B C0 D0 : k[X]) :
    (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree]
      [
      [3, 1, 0, 0], [2, 0, 0, 1], [1, 1, 1, 0], [0, 3, 0, 0],
      [0, 0, 1, 1]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroEpsilonGroupPolynomial610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroZetaGroupPolynomial610
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
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroZetaGroupPolynomial610
    (A B C0 D0 : k[X]) :
    (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree]
      [
      [4, 0, 0, 0], [2, 0, 1, 0], [1, 2, 0, 0], [0, 1, 0, 1],
      [0, 0, 2, 0]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroZetaGroupPolynomial610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroEtaGroupPolynomial610
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
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroEtaGroupPolynomial610
    (A B C0 D0 : k[X]) :
    (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree]
      [
      [2, 1, 0, 0], [1, 0, 0, 1], [0, 1, 1, 0]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroEtaGroupPolynomial610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroThetaGroupPolynomial610
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
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroThetaGroupPolynomial610
    (A B C0 E0 : k[X]) :
    (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, E0.natDegree]
      [
      [3, 0, 0, 0], [1, 0, 1, 0], [0, 2, 0, 0], [0, 0, 0, 1]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroThetaGroupPolynomial610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroBaseGroupHighARest610
    (l : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroBaseGroupHighARest610 l A B C0 D0 E0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0]
      [
      (-(62720 / 2239488) : k), (113724 / 2239488 * l : k), (92160 / 2239488 : k),
      (301806 / 2239488 * l : k), (491520 / 2239488 : k), (-(122472 / 2239488 * l) : k),
      (343040 / 2239488 : k), (-(769824 / 2239488 * l) : k), (-(483840 / 2239488) : k),
      (-(384912 / 2239488 * l) : k), (-(668160 / 2239488) : k), (-(1224720 / 2239488 * l) : k),
      (-(1071360 / 2239488) : k), (-(1071360 / 2239488) : k), (699840 / 2239488 * l : k),
      (559872 / 2239488 * l : k), (622080 / 2239488 : k), (-(209952 / 2239488 * l) : k),
      (-(737280 / 2239488) : k), (839808 / 2239488 * l : k), (2519424 / 2239488 * l : k),
      (1658880 / 2239488 : k), (1244160 / 2239488 : k), (419904 / 2239488 * l : k),
      (1244160 / 2239488 : k), (-(36864 / 2239488) : k), (419904 / 2239488 * l : k),
      (276480 / 2239488 : k), (629856 / 2239488 * l : k), (1244160 / 2239488 : k),
      (414720 / 2239488 : k), (-(1679616 / 2239488 * l) : k), (-(839808 / 2239488 * l) : k),
      (-(1679616 / 2239488 * l) : k), (-(2488320 / 2239488) : k), (-(829440 / 2239488) : k)]
      [
      [6, 1, 0, 0, 0], [5, 0, 1, 0, 0], [5, 0, 0, 1, 0], [4, 2, 0, 0, 0],
      [4, 1, 1, 0, 0], [4, 0, 0, 0, 1], [3, 3, 0, 0, 0], [3, 1, 0, 1, 0],
      [3, 1, 0, 0, 1], [3, 0, 2, 0, 0], [3, 0, 1, 1, 0], [2, 2, 1, 0, 0],
      [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [2, 0, 1, 0, 1], [2, 0, 0, 2, 0],
      [2, 0, 0, 1, 1], [1, 4, 0, 0, 0], [1, 3, 1, 0, 0], [1, 2, 0, 0, 1],
      [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0], [1, 0, 3, 0, 0],
      [1, 0, 2, 1, 0], [0, 5, 0, 0, 0], [0, 3, 0, 1, 0], [0, 3, 0, 0, 1],
      [0, 2, 2, 0, 0], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 1, 0, 1, 1],
      [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0]] := by
  simp only [degreeZeroBaseGroupHighARest610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroBaseGroupHighARest610
    (l : k) (A B C0 D0 E0 : k[X]) :
    (degreeZeroBaseGroupHighARest610 l A B C0 D0 E0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree, E0.natDegree]
      [
      [6, 1, 0, 0, 0], [5, 0, 1, 0, 0], [5, 0, 0, 1, 0], [4, 2, 0, 0, 0],
      [4, 1, 1, 0, 0], [4, 0, 0, 0, 1], [3, 3, 0, 0, 0], [3, 1, 0, 1, 0],
      [3, 1, 0, 0, 1], [3, 0, 2, 0, 0], [3, 0, 1, 1, 0], [2, 2, 1, 0, 0],
      [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [2, 0, 1, 0, 1], [2, 0, 0, 2, 0],
      [2, 0, 0, 1, 1], [1, 4, 0, 0, 0], [1, 3, 1, 0, 0], [1, 2, 0, 0, 1],
      [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0], [1, 0, 3, 0, 0],
      [1, 0, 2, 1, 0], [0, 5, 0, 0, 0], [0, 3, 0, 1, 0], [0, 3, 0, 0, 1],
      [0, 2, 2, 0, 0], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 1, 0, 1, 1],
      [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroBaseGroupHighARest610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroBaseGroupHighBRest610
    (l : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroBaseGroupHighBRest610 l A B C0 D0 E0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0]
      [
      (-(10935 / 2239488 * l) : k), (-(62720 / 2239488) : k), (113724 / 2239488 * l : k),
      (92160 / 2239488 : k), (301806 / 2239488 * l : k), (491520 / 2239488 : k),
      (-(122472 / 2239488 * l) : k), (343040 / 2239488 : k), (-(769824 / 2239488 * l) : k),
      (-(483840 / 2239488) : k), (-(384912 / 2239488 * l) : k), (-(668160 / 2239488) : k),
      (-(1224720 / 2239488 * l) : k), (-(1071360 / 2239488) : k), (-(1071360 / 2239488) : k),
      (699840 / 2239488 * l : k), (559872 / 2239488 * l : k), (622080 / 2239488 : k),
      (-(209952 / 2239488 * l) : k), (-(737280 / 2239488) : k), (839808 / 2239488 * l : k),
      (2519424 / 2239488 * l : k), (1658880 / 2239488 : k), (1244160 / 2239488 : k),
      (419904 / 2239488 * l : k), (1244160 / 2239488 : k), (419904 / 2239488 * l : k),
      (276480 / 2239488 : k), (629856 / 2239488 * l : k), (1244160 / 2239488 : k),
      (414720 / 2239488 : k), (-(1679616 / 2239488 * l) : k), (-(839808 / 2239488 * l) : k),
      (-(1679616 / 2239488 * l) : k), (-(2488320 / 2239488) : k), (-(829440 / 2239488) : k)]
      [
      [7, 0, 0, 0, 0], [6, 1, 0, 0, 0], [5, 0, 1, 0, 0], [5, 0, 0, 1, 0],
      [4, 2, 0, 0, 0], [4, 1, 1, 0, 0], [4, 0, 0, 0, 1], [3, 3, 0, 0, 0],
      [3, 1, 0, 1, 0], [3, 1, 0, 0, 1], [3, 0, 2, 0, 0], [3, 0, 1, 1, 0],
      [2, 2, 1, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [2, 0, 1, 0, 1],
      [2, 0, 0, 2, 0], [2, 0, 0, 1, 1], [1, 4, 0, 0, 0], [1, 3, 1, 0, 0],
      [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0],
      [1, 0, 3, 0, 0], [1, 0, 2, 1, 0], [0, 3, 0, 1, 0], [0, 3, 0, 0, 1],
      [0, 2, 2, 0, 0], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 1, 0, 1, 1],
      [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0]] := by
  simp only [degreeZeroBaseGroupHighBRest610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroBaseGroupHighBRest610
    (l : k) (A B C0 D0 E0 : k[X]) :
    (degreeZeroBaseGroupHighBRest610 l A B C0 D0 E0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree, E0.natDegree]
      [
      [7, 0, 0, 0, 0], [6, 1, 0, 0, 0], [5, 0, 1, 0, 0], [5, 0, 0, 1, 0],
      [4, 2, 0, 0, 0], [4, 1, 1, 0, 0], [4, 0, 0, 0, 1], [3, 3, 0, 0, 0],
      [3, 1, 0, 1, 0], [3, 1, 0, 0, 1], [3, 0, 2, 0, 0], [3, 0, 1, 1, 0],
      [2, 2, 1, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [2, 0, 1, 0, 1],
      [2, 0, 0, 2, 0], [2, 0, 0, 1, 1], [1, 4, 0, 0, 0], [1, 3, 1, 0, 0],
      [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0],
      [1, 0, 3, 0, 0], [1, 0, 2, 1, 0], [0, 3, 0, 1, 0], [0, 3, 0, 0, 1],
      [0, 2, 2, 0, 0], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 1, 0, 1, 1],
      [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroBaseGroupHighBRest610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroBaseGroupHighDRest610
    (l : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroBaseGroupHighDRest610 l A B C0 D0 E0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0]
      [
      (-(10935 / 2239488 * l) : k), (-(62720 / 2239488) : k), (113724 / 2239488 * l : k),
      (92160 / 2239488 : k), (301806 / 2239488 * l : k), (491520 / 2239488 : k),
      (-(122472 / 2239488 * l) : k), (343040 / 2239488 : k), (-(769824 / 2239488 * l) : k),
      (-(483840 / 2239488) : k), (-(384912 / 2239488 * l) : k), (-(668160 / 2239488) : k),
      (-(1224720 / 2239488 * l) : k), (-(1071360 / 2239488) : k), (-(1071360 / 2239488) : k),
      (699840 / 2239488 * l : k), (559872 / 2239488 * l : k), (622080 / 2239488 : k),
      (-(209952 / 2239488 * l) : k), (-(737280 / 2239488) : k), (839808 / 2239488 * l : k),
      (2519424 / 2239488 * l : k), (1658880 / 2239488 : k), (1244160 / 2239488 : k),
      (419904 / 2239488 * l : k), (1244160 / 2239488 : k), (-(36864 / 2239488) : k),
      (419904 / 2239488 * l : k), (276480 / 2239488 : k), (629856 / 2239488 * l : k),
      (1244160 / 2239488 : k), (414720 / 2239488 : k), (-(1679616 / 2239488 * l) : k),
      (-(839808 / 2239488 * l) : k), (-(1679616 / 2239488 * l) : k), (-(2488320 / 2239488) : k)]
      [
      [7, 0, 0, 0, 0], [6, 1, 0, 0, 0], [5, 0, 1, 0, 0], [5, 0, 0, 1, 0],
      [4, 2, 0, 0, 0], [4, 1, 1, 0, 0], [4, 0, 0, 0, 1], [3, 3, 0, 0, 0],
      [3, 1, 0, 1, 0], [3, 1, 0, 0, 1], [3, 0, 2, 0, 0], [3, 0, 1, 1, 0],
      [2, 2, 1, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [2, 0, 1, 0, 1],
      [2, 0, 0, 2, 0], [2, 0, 0, 1, 1], [1, 4, 0, 0, 0], [1, 3, 1, 0, 0],
      [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0],
      [1, 0, 3, 0, 0], [1, 0, 2, 1, 0], [0, 5, 0, 0, 0], [0, 3, 0, 1, 0],
      [0, 3, 0, 0, 1], [0, 2, 2, 0, 0], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
      [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [0, 0, 1, 1, 1]] := by
  simp only [degreeZeroBaseGroupHighDRest610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroBaseGroupHighDRest610
    (l : k) (A B C0 D0 E0 : k[X]) :
    (degreeZeroBaseGroupHighDRest610 l A B C0 D0 E0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree, E0.natDegree]
      [
      [7, 0, 0, 0, 0], [6, 1, 0, 0, 0], [5, 0, 1, 0, 0], [5, 0, 0, 1, 0],
      [4, 2, 0, 0, 0], [4, 1, 1, 0, 0], [4, 0, 0, 0, 1], [3, 3, 0, 0, 0],
      [3, 1, 0, 1, 0], [3, 1, 0, 0, 1], [3, 0, 2, 0, 0], [3, 0, 1, 1, 0],
      [2, 2, 1, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [2, 0, 1, 0, 1],
      [2, 0, 0, 2, 0], [2, 0, 0, 1, 1], [1, 4, 0, 0, 0], [1, 3, 1, 0, 0],
      [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0],
      [1, 0, 3, 0, 0], [1, 0, 2, 1, 0], [0, 5, 0, 0, 0], [0, 3, 0, 1, 0],
      [0, 3, 0, 0, 1], [0, 2, 2, 0, 0], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
      [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [0, 0, 1, 1, 1]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroBaseGroupHighDRest610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroBaseGroupPolynomial610
    (l : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0]
      [
      (-(10935 / 2239488 * l) : k), (-(62720 / 2239488) : k), (113724 / 2239488 * l : k),
      (92160 / 2239488 : k), (301806 / 2239488 * l : k), (491520 / 2239488 : k),
      (-(122472 / 2239488 * l) : k), (343040 / 2239488 : k), (-(769824 / 2239488 * l) : k),
      (-(483840 / 2239488) : k), (-(384912 / 2239488 * l) : k), (-(668160 / 2239488) : k),
      (-(1224720 / 2239488 * l) : k), (-(1071360 / 2239488) : k), (-(1071360 / 2239488) : k),
      (699840 / 2239488 * l : k), (559872 / 2239488 * l : k), (622080 / 2239488 : k),
      (-(209952 / 2239488 * l) : k), (-(737280 / 2239488) : k), (839808 / 2239488 * l : k),
      (2519424 / 2239488 * l : k), (1658880 / 2239488 : k), (1244160 / 2239488 : k),
      (419904 / 2239488 * l : k), (1244160 / 2239488 : k), (-(36864 / 2239488) : k),
      (419904 / 2239488 * l : k), (276480 / 2239488 : k), (629856 / 2239488 * l : k),
      (1244160 / 2239488 : k), (414720 / 2239488 : k), (-(1679616 / 2239488 * l) : k),
      (-(839808 / 2239488 * l) : k), (-(1679616 / 2239488 * l) : k), (-(2488320 / 2239488) : k),
      (-(829440 / 2239488) : k)]
      [
      [7, 0, 0, 0, 0], [6, 1, 0, 0, 0], [5, 0, 1, 0, 0], [5, 0, 0, 1, 0],
      [4, 2, 0, 0, 0], [4, 1, 1, 0, 0], [4, 0, 0, 0, 1], [3, 3, 0, 0, 0],
      [3, 1, 0, 1, 0], [3, 1, 0, 0, 1], [3, 0, 2, 0, 0], [3, 0, 1, 1, 0],
      [2, 2, 1, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [2, 0, 1, 0, 1],
      [2, 0, 0, 2, 0], [2, 0, 0, 1, 1], [1, 4, 0, 0, 0], [1, 3, 1, 0, 0],
      [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0],
      [1, 0, 3, 0, 0], [1, 0, 2, 1, 0], [0, 5, 0, 0, 0], [0, 3, 0, 1, 0],
      [0, 3, 0, 0, 1], [0, 2, 2, 0, 0], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
      [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [0, 0, 1, 1, 1],
      [0, 0, 0, 3, 0]] := by
  simp only [degreeZeroBaseGroupPolynomial610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroBaseGroupPolynomial610
    (l : k) (A B C0 D0 E0 : k[X]) :
    (degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree, E0.natDegree]
      [
      [7, 0, 0, 0, 0], [6, 1, 0, 0, 0], [5, 0, 1, 0, 0], [5, 0, 0, 1, 0],
      [4, 2, 0, 0, 0], [4, 1, 1, 0, 0], [4, 0, 0, 0, 1], [3, 3, 0, 0, 0],
      [3, 1, 0, 1, 0], [3, 1, 0, 0, 1], [3, 0, 2, 0, 0], [3, 0, 1, 1, 0],
      [2, 2, 1, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [2, 0, 1, 0, 1],
      [2, 0, 0, 2, 0], [2, 0, 0, 1, 1], [1, 4, 0, 0, 0], [1, 3, 1, 0, 0],
      [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0],
      [1, 0, 3, 0, 0], [1, 0, 2, 1, 0], [0, 5, 0, 0, 0], [0, 3, 0, 1, 0],
      [0, 3, 0, 0, 1], [0, 2, 2, 0, 0], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
      [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [0, 0, 1, 1, 1],
      [0, 0, 0, 3, 0]] := by
  rw [coneCascade610SpeedTReflect_degreeZeroBaseGroupPolynomial610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal once. -/
private theorem coneCascade610SpeedTReflect_degreeZeroBaseGroupHighA_noA6B_Rest610
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
  try module

set_option maxHeartbeats 64000000 in
/-- A reusable degree bound, independent of the scalar coefficients. -/
theorem coneCascade610SpeedTBound_degreeZeroBaseGroupHighA_noA6B_Rest610
    (l : k) (A B C0 D0 E0 : k[X]) :
    (degreeZeroBaseGroupHighA_noA6B_Rest610 l A B C0 D0 E0).natDegree ≤
      Max11ReflectDeg.bnd [A.natDegree, B.natDegree, C0.natDegree, D0.natDegree, E0.natDegree]
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
  rw [coneCascade610SpeedTReflect_degreeZeroBaseGroupHighA_noA6B_Rest610]
  exact Max11ReflectDeg.natDegree_polyOf_le _ _ _

end Max11DegreeRoutes
