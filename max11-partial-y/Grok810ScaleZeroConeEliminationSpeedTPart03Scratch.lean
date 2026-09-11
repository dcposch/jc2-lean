import Grok810ScaleZeroConeEliminationSpeedTPart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Unique-face elimination -/

section UniqueFaces810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoBaseGroupPolynomial810` (84 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoBaseGroupPolynomial810_eq_polyOf
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (19635 / 1048576 : k), (369495 / 268435456 * l : k), (-(17115 / 131072) : k),
      (-(315 / 2048) : k), (-(189945 / 4194304 * l) : k), (-(3255 / 131072) : k),
      (-(61425 / 4194304 * l) : k), (315 / 8192 : k), (1575 / 4096 : k),
      (14175 / 262144 * l : k), (6185 / 16384 : k), (6115 / 16384 : k),
      (28161 / 131072 * l : k), (1495 / 8192 : k), (27279 / 524288 * l : k),
      (1425 / 8192 : k), (27279 / 262144 * l : k), (515 / 16384 : k),
      (4977 / 262144 * l : k), (-(265 / 2048) : k), (-(125 / 2048) : k),
      (-(567 / 16384 * l) : k), (-(255 / 1024) : k), (-(375 / 512) : k),
      (-(3339 / 16384 * l) : k), (-(235 / 1024) : k), (-(1071 / 8192 * l) : k),
      (-(735 / 2048) : k), (-(1071 / 16384 * l) : k), (-(735 / 2048) : k),
      (-(705 / 1024) : k), (-(3213 / 8192 * l) : k), (-(165 / 512) : k),
      (-(189 / 1024 * l) : k), (-(455 / 2048) : k), (-(261 / 4096 * l) : k),
      (-(425 / 2048) : k), (-(981 / 8192 * l) : k), (-(255 / 2048) : k),
      (-(459 / 4096 * l) : k), (-(459 / 32768 * l) : k), (15 / 128 : k),
      (63 / 4096 * l : k), (45 / 128 : k), (45 / 128 : k),
      (189 / 1024 * l : k), (85 / 256 : k), (45 / 512 * l : k),
      (85 / 256 : k), (45 / 256 * l : k), (15 / 256 : k),
      (27 / 512 * l : k), (15 / 128 : k), (85 / 128 : k),
      (45 / 256 * l : k), (5 / 16 : k), (171 / 1024 * l : k),
      (5 / 16 : k), (5 / 8 : k), (171 / 512 * l : k),
      (45 / 128 : k), (81 / 256 * l : k), (81 / 1024 * l : k),
      (75 / 256 : k), (81 / 1024 * l : k), (45 / 256 : k),
      (81 / 512 * l : k), (81 / 1024 * l : k), (-(5 / 16) : k),
      (-(5 / 16) : k), (-(9 / 64 * l) : k), (-(5 / 8) : k),
      (-(9 / 64 * l) : k), (-(5 / 16) : k), (-(9 / 32 * l) : k),
      (-(9 / 128 * l) : k), (-(5 / 16) : k), (-(5 / 16) : k),
      (-(9 / 32 * l) : k), (-(9 / 64 * l) : k), (-(5 / 16) : k),
      (-(9 / 64 * l) : k), (-(9 / 64 * l) : k), (9 / 16 * l : k)]
      [
      [7, 1, 0, 0, 0, 0, 0], [8, 0, 0, 0, 0, 0, 0], [4, 3, 0, 0, 0, 0, 0], [5, 1, 1, 0, 0, 0, 0],
      [5, 2, 0, 0, 0, 0, 0], [6, 0, 0, 1, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0],
      [2, 3, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [3, 1, 2, 0, 0, 0, 0], [3, 2, 0, 1, 0, 0, 0],
      [3, 2, 1, 0, 0, 0, 0], [4, 0, 1, 1, 0, 0, 0], [4, 0, 2, 0, 0, 0, 0], [4, 1, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0], [5, 0, 0, 0, 0, 1, 0], [5, 0, 0, 0, 1, 0, 0], [0, 3, 2, 0, 0, 0, 0],
      [0, 4, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 3, 0, 0, 0, 0], [1, 2, 1, 1, 0, 0, 0],
      [1, 2, 2, 0, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [1, 3, 0, 1, 0, 0, 0], [2, 0, 2, 1, 0, 0, 0],
      [2, 0, 3, 0, 0, 0, 0], [2, 1, 0, 2, 0, 0, 0], [2, 1, 1, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0],
      [2, 2, 0, 0, 0, 1, 0], [2, 2, 0, 0, 1, 0, 0], [3, 0, 0, 1, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0],
      [3, 0, 1, 0, 0, 1, 0], [3, 0, 1, 0, 1, 0, 0], [3, 1, 0, 0, 0, 0, 1], [3, 1, 0, 0, 0, 1, 0],
      [4, 0, 0, 0, 0, 0, 1], [0, 0, 3, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 1, 1, 2, 0, 0, 0],
      [0, 1, 2, 0, 1, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 2, 0, 1, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 2, 1, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1], [0, 3, 0, 0, 0, 1, 0],
      [1, 0, 0, 3, 0, 0, 0], [1, 0, 1, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [1, 0, 2, 0, 0, 1, 0],
      [1, 0, 2, 0, 1, 0, 0], [1, 1, 0, 0, 2, 0, 0], [1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0],
      [1, 1, 1, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 2, 0, 0, 0, 0, 1], [2, 0, 0, 0, 1, 1, 0],
      [2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 1, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0], [2, 0, 1, 0, 0, 0, 1],
      [0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 1, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0, 1],
      [1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2]] := by
  simp only [rhoBaseGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoBetaGroupPolynomial810` (23 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoBetaGroupPolynomial810_eq_polyOf
    (A B C0 D0 E0 F0 : k[X]) :
    rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (2601 / 1048576 : k), (-(15687 / 262144) : k), (-(189 / 8192) : k),
      (567 / 16384 : k), (1701 / 8192 : k), (273 / 4096 : k),
      (273 / 2048 : k), (483 / 16384 : k), (-(91 / 1024) : k),
      (-(7 / 128) : k), (-(7 / 128) : k), (-(21 / 64) : k),
      (-(77 / 512) : k), (-(21 / 256) : k), (-(77 / 512) : k),
      (-(35 / 256) : k), (7 / 64 : k), (7 / 64 : k),
      (7 / 32 : k), (7 / 32 : k), (7 / 64 : k),
      (7 / 32 : k), (-(7 / 16) : k)]
      [
      [7, 0, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0], [1, 4, 0, 0, 0, 0],
      [2, 2, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0], [3, 1, 0, 1, 0, 0], [4, 0, 0, 0, 1, 0],
      [0, 2, 2, 0, 0, 0], [0, 3, 0, 1, 0, 0], [1, 0, 3, 0, 0, 0], [1, 1, 1, 1, 0, 0],
      [1, 2, 0, 0, 1, 0], [2, 0, 0, 2, 0, 0], [2, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 1],
      [0, 0, 1, 2, 0, 0], [0, 0, 2, 0, 1, 0], [0, 1, 0, 1, 1, 0], [0, 1, 1, 0, 0, 1],
      [1, 0, 0, 0, 2, 0], [1, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2]] := by
  simp only [rhoBetaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoGammaGroupPolynomial810` (17 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoGammaGroupPolynomial810_eq_polyOf
    (A B C0 D0 E0 F0 : k[X]) :
    rhoGammaGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (-(765 / 16384) : k), (135 / 1024 : k), (531 / 2048 : k),
      (63 / 1024 : k), (-(27 / 256) : k), (-(39 / 128) : k),
      (-(75 / 256) : k), (-(75 / 256) : k), (-(69 / 256) : k),
      (-(33 / 512) : k), (3 / 16 : k), (3 / 16 : k),
      (3 / 8 : k), (9 / 64 : k), (3 / 8 : k),
      (9 / 32 : k), (-(3 / 4) : k)]
      [
      [5, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0], [3, 1, 1, 0, 0, 0], [4, 0, 0, 1, 0, 0],
      [0, 3, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0], [1, 2, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0],
      [2, 1, 0, 0, 1, 0], [3, 0, 0, 0, 0, 1], [0, 0, 2, 1, 0, 0], [0, 1, 0, 2, 0, 0],
      [0, 1, 1, 0, 1, 0], [0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 1],
      [0, 0, 0, 0, 1, 1]] := by
  simp only [rhoGammaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoDeltaGroupPolynomial810` (16 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoDeltaGroupPolynomial810_eq_polyOf
    (A B C0 D0 E0 F0 : k[X]) :
    rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (-(2805 / 262144) : k), (2925 / 16384 : k), (1395 / 16384 : k),
      (-(135 / 4096) : k), (-(405 / 1024) : k), (-(195 / 1024) : k),
      (-(195 / 512) : k), (-(105 / 1024) : k), (5 / 64 : k),
      (15 / 32 : k), (25 / 128 : k), (15 / 64 : k),
      (25 / 64 : k), (5 / 16 : k), (-(5 / 16) : k),
      (-(5 / 8) : k)]
      [
      [6, 0, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0], [0, 4, 0, 0, 0, 0],
      [1, 2, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0], [2, 1, 0, 1, 0, 0], [3, 0, 0, 0, 1, 0],
      [0, 0, 3, 0, 0, 0], [0, 1, 1, 1, 0, 0], [0, 2, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0],
      [1, 0, 1, 0, 1, 0], [1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0], [0, 0, 0, 1, 0, 1]] := by
  simp only [rhoDeltaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoEpsilonGroupPolynomial810` (11 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoEpsilonGroupPolynomial810_eq_polyOf
    (A B C0 D0 E0 F0 : k[X]) :
    rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (51 / 512 : k), (-(9 / 64) : k), (-(27 / 64) : k),
      (-(33 / 256) : k), (1 / 4 : k), (7 / 32 : k),
      (7 / 16 : k), (3 / 8 : k), (5 / 32 : k),
      (-(1 / 2) : k), (-(1 / 2) : k)]
      [
      [4, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0], [2, 1, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0],
      [0, 1, 2, 0, 0, 0], [0, 2, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0], [1, 1, 0, 0, 1, 0],
      [2, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0], [0, 0, 1, 0, 0, 1]] := by
  simp only [rhoEpsilonGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoZetaGroupPolynomial810` (10 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoZetaGroupPolynomial810_eq_polyOf
    (A B C0 D0 E0 F0 : k[X]) :
    rhoZetaGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (153 / 8192 : k), (-(405 / 2048) : k), (-(63 / 512) : k),
      (27 / 128 : k), (3 / 16 : k), (3 / 8 : k),
      (21 / 128 : k), (-(3 / 16) : k), (-(3 / 8) : k),
      (-(3 / 8) : k)]
      [
      [5, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0],
      [1, 0, 2, 0, 0, 0], [1, 1, 0, 1, 0, 0], [2, 0, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0],
      [0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 0, 1]] := by
  simp only [rhoZetaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoEtaGroupPolynomial810` (7 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoEtaGroupPolynomial810_eq_polyOf
    (A B C0 D0 E0 F0 : k[X]) :
    rhoEtaGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (-(51 / 512) : k), (3 / 64 : k), (9 / 32 : k),
      (9 / 64 : k), (-(1 / 4) : k), (-(1 / 4) : k),
      (-(1 / 4) : k)]
      [
      [3, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0], [2, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0], [0, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 1]] := by
  simp only [rhoEtaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoThetaGroupPolynomial810` (7 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoThetaGroupPolynomial810_eq_polyOf
    (A B C0 D0 E0 G0 : k[X]) :
    rhoThetaGroupPolynomial810 A B C0 D0 E0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, G0]
      [
      (-(51 / 4096) : k), (9 / 128 : k), (9 / 128 : k),
      (-(1 / 16) : k), (-(1 / 8) : k), (-(1 / 8) : k),
      (1 / 1 : k)]
      [
      [4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0],
      [0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]] := by
  simp only [rhoThetaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitivePolynomial810_false_of_constant_core
    (l beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0)
    (hG : G0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  rw [eq_C_of_natDegree_eq_zero hA, eq_C_of_natDegree_eq_zero hB,
    eq_C_of_natDegree_eq_zero hC, eq_C_of_natDegree_eq_zero hD,
    eq_C_of_natDegree_eq_zero hE, eq_C_of_natDegree_eq_zero hF,
    eq_C_of_natDegree_eq_zero hG] at hder
  simp only [degreeZeroPrimitivePolynomial810, rhoBaseGroupPolynomial810,
    rhoBetaGroupPolynomial810, rhoGammaGroupPolynomial810,
    rhoDeltaGroupPolynomial810, rhoEpsilonGroupPolynomial810,
    rhoZetaGroupPolynomial810, rhoEtaGroupPolynomial810,
    rhoThetaGroupPolynomial810, ← Polynomial.C_pow, ← Polynomial.C_mul,
    smul_C, ← Polynomial.C_add, ← Polynomial.C_sub, derivative_C] at hder
  exact hj (Polynomial.C_eq_zero.mp hder.symm)

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoBaseGroupHighARest810` (83 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoBaseGroupHighARest810_eq_polyOf
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupHighARest810 l A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (19635 / 1048576 : k), (-(17115 / 131072) : k), (-(315 / 2048) : k),
      (-(189945 / 4194304 * l) : k), (-(3255 / 131072) : k), (-(61425 / 4194304 * l) : k),
      (315 / 8192 : k), (1575 / 4096 : k), (14175 / 262144 * l : k),
      (6185 / 16384 : k), (6115 / 16384 : k), (28161 / 131072 * l : k),
      (1495 / 8192 : k), (27279 / 524288 * l : k), (1425 / 8192 : k),
      (27279 / 262144 * l : k), (515 / 16384 : k), (4977 / 262144 * l : k),
      (-(265 / 2048) : k), (-(125 / 2048) : k), (-(567 / 16384 * l) : k),
      (-(255 / 1024) : k), (-(375 / 512) : k), (-(3339 / 16384 * l) : k),
      (-(235 / 1024) : k), (-(1071 / 8192 * l) : k), (-(735 / 2048) : k),
      (-(1071 / 16384 * l) : k), (-(735 / 2048) : k), (-(705 / 1024) : k),
      (-(3213 / 8192 * l) : k), (-(165 / 512) : k), (-(189 / 1024 * l) : k),
      (-(455 / 2048) : k), (-(261 / 4096 * l) : k), (-(425 / 2048) : k),
      (-(981 / 8192 * l) : k), (-(255 / 2048) : k), (-(459 / 4096 * l) : k),
      (-(459 / 32768 * l) : k), (15 / 128 : k), (63 / 4096 * l : k),
      (45 / 128 : k), (45 / 128 : k), (189 / 1024 * l : k),
      (85 / 256 : k), (45 / 512 * l : k), (85 / 256 : k),
      (45 / 256 * l : k), (15 / 256 : k), (27 / 512 * l : k),
      (15 / 128 : k), (85 / 128 : k), (45 / 256 * l : k),
      (5 / 16 : k), (171 / 1024 * l : k), (5 / 16 : k),
      (5 / 8 : k), (171 / 512 * l : k), (45 / 128 : k),
      (81 / 256 * l : k), (81 / 1024 * l : k), (75 / 256 : k),
      (81 / 1024 * l : k), (45 / 256 : k), (81 / 512 * l : k),
      (81 / 1024 * l : k), (-(5 / 16) : k), (-(5 / 16) : k),
      (-(9 / 64 * l) : k), (-(5 / 8) : k), (-(9 / 64 * l) : k),
      (-(5 / 16) : k), (-(9 / 32 * l) : k), (-(9 / 128 * l) : k),
      (-(5 / 16) : k), (-(5 / 16) : k), (-(9 / 32 * l) : k),
      (-(9 / 64 * l) : k), (-(5 / 16) : k), (-(9 / 64 * l) : k),
      (-(9 / 64 * l) : k), (9 / 16 * l : k)]
      [
      [7, 1, 0, 0, 0, 0, 0], [4, 3, 0, 0, 0, 0, 0], [5, 1, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0],
      [6, 0, 0, 1, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0], [2, 3, 1, 0, 0, 0, 0],
      [2, 4, 0, 0, 0, 0, 0], [3, 1, 2, 0, 0, 0, 0], [3, 2, 0, 1, 0, 0, 0], [3, 2, 1, 0, 0, 0, 0],
      [4, 0, 1, 1, 0, 0, 0], [4, 0, 2, 0, 0, 0, 0], [4, 1, 0, 0, 1, 0, 0], [4, 1, 0, 1, 0, 0, 0],
      [5, 0, 0, 0, 0, 1, 0], [5, 0, 0, 0, 1, 0, 0], [0, 3, 2, 0, 0, 0, 0], [0, 4, 0, 1, 0, 0, 0],
      [0, 4, 1, 0, 0, 0, 0], [1, 1, 3, 0, 0, 0, 0], [1, 2, 1, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0],
      [1, 3, 0, 0, 1, 0, 0], [1, 3, 0, 1, 0, 0, 0], [2, 0, 2, 1, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0],
      [2, 1, 0, 2, 0, 0, 0], [2, 1, 1, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0], [2, 2, 0, 0, 0, 1, 0],
      [2, 2, 0, 0, 1, 0, 0], [3, 0, 0, 1, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0], [3, 0, 1, 0, 0, 1, 0],
      [3, 0, 1, 0, 1, 0, 0], [3, 1, 0, 0, 0, 0, 1], [3, 1, 0, 0, 0, 1, 0], [4, 0, 0, 0, 0, 0, 1],
      [0, 0, 3, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 1, 1, 2, 0, 0, 0], [0, 1, 2, 0, 1, 0, 0],
      [0, 1, 2, 1, 0, 0, 0], [0, 2, 0, 1, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 2, 1, 0, 0, 1, 0],
      [0, 2, 1, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1], [0, 3, 0, 0, 0, 1, 0], [1, 0, 0, 3, 0, 0, 0],
      [1, 0, 1, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [1, 0, 2, 0, 0, 1, 0], [1, 0, 2, 0, 1, 0, 0],
      [1, 1, 0, 0, 2, 0, 0], [1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 1, 1, 0, 0, 0, 1],
      [1, 1, 1, 0, 0, 1, 0], [1, 2, 0, 0, 0, 0, 1], [2, 0, 0, 0, 1, 1, 0], [2, 0, 0, 0, 2, 0, 0],
      [2, 0, 0, 1, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0], [2, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 2, 0, 0],
      [0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0], [0, 0, 1, 0, 2, 0, 0],
      [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 1, 0, 0, 0, 2, 0],
      [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0, 1], [1, 0, 0, 0, 0, 1, 1],
      [1, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2]] := by
  simp only [rhoBaseGroupHighARest810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveHighARest810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : UniqueHighACone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroPrimitiveHighARest810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      8 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  have hbase :
      (rhoBaseGroupHighARest810 l A B C0 D0 E0 F0 G0).natDegree <
        8 * A.natDegree := by
    rw [speedRefl_rhoBaseGroupHighARest810_eq_polyOf]
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
  have hbetaG :
      (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    rw [speedRefl_rhoBetaGroupPolynomial810_eq_polyOf]
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
  have hgammaG :
      (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    rw [speedRefl_rhoGammaGroupPolynomial810_eq_polyOf]
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
  have hdeltaG :
      (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    rw [speedRefl_rhoDeltaGroupPolynomial810_eq_polyOf]
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
  have hepsilonG :
      (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    rw [speedRefl_rhoEpsilonGroupPolynomial810_eq_polyOf]
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
  have hzetaG :
      (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    rw [speedRefl_rhoZetaGroupPolynomial810_eq_polyOf]
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
  have hetaG :
      (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
        8 * A.natDegree := by
    rw [speedRefl_rhoEtaGroupPolynomial810_eq_polyOf]
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
  have hthetaG :
      (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree <
        8 * A.natDegree := by
    rw [speedRefl_rhoThetaGroupPolynomial810_eq_polyOf]
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
  simp only [degreeZeroPrimitiveHighARest810]
  exact natDegree_add8_lt810 hbase (natDegree_smul_lt810 beta hbetaG)
    (natDegree_smul_lt810 gamma hgammaG) (natDegree_smul_lt810 delta hdeltaG)
    (natDegree_smul_lt810 epsilon hepsilonG) (natDegree_smul_lt810 zeta hzetaG)
    (natDegree_smul_lt810 eta hetaG) (natDegree_smul_lt810 theta hthetaG)
set_option maxHeartbeats 64000000 in

theorem uniqueHighA_impossible_of_l_ne
    (l beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hcone : UniqueHighACone810 A B C0 D0 E0 F0 G0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (369495 / 268435456 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead :
      ((369495 / 268435456 * l : k) • A ^ 8).natDegree =
        8 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroPrimitiveHighARest810_natDegree_lt l beta gamma delta
      epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroPrimitivePolynomial810_eq_A8_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead])] at hdeg
  rw [hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoBaseGroupHighA_noA7B_Rest810` (82 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoBaseGroupHighA_noA7B_Rest810_eq_polyOf
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupHighA_noA7B_Rest810 l A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(17115 / 131072) : k), (-(315 / 2048) : k), (-(189945 / 4194304 * l) : k),
      (-(3255 / 131072) : k), (-(61425 / 4194304 * l) : k), (315 / 8192 : k),
      (1575 / 4096 : k), (14175 / 262144 * l : k), (6185 / 16384 : k),
      (6115 / 16384 : k), (28161 / 131072 * l : k), (1495 / 8192 : k),
      (27279 / 524288 * l : k), (1425 / 8192 : k), (27279 / 262144 * l : k),
      (515 / 16384 : k), (4977 / 262144 * l : k), (-(265 / 2048) : k),
      (-(125 / 2048) : k), (-(567 / 16384 * l) : k), (-(255 / 1024) : k),
      (-(375 / 512) : k), (-(3339 / 16384 * l) : k), (-(235 / 1024) : k),
      (-(1071 / 8192 * l) : k), (-(735 / 2048) : k), (-(1071 / 16384 * l) : k),
      (-(735 / 2048) : k), (-(705 / 1024) : k), (-(3213 / 8192 * l) : k),
      (-(165 / 512) : k), (-(189 / 1024 * l) : k), (-(455 / 2048) : k),
      (-(261 / 4096 * l) : k), (-(425 / 2048) : k), (-(981 / 8192 * l) : k),
      (-(255 / 2048) : k), (-(459 / 4096 * l) : k), (-(459 / 32768 * l) : k),
      (15 / 128 : k), (63 / 4096 * l : k), (45 / 128 : k),
      (45 / 128 : k), (189 / 1024 * l : k), (85 / 256 : k),
      (45 / 512 * l : k), (85 / 256 : k), (45 / 256 * l : k),
      (15 / 256 : k), (27 / 512 * l : k), (15 / 128 : k),
      (85 / 128 : k), (45 / 256 * l : k), (5 / 16 : k),
      (171 / 1024 * l : k), (5 / 16 : k), (5 / 8 : k),
      (171 / 512 * l : k), (45 / 128 : k), (81 / 256 * l : k),
      (81 / 1024 * l : k), (75 / 256 : k), (81 / 1024 * l : k),
      (45 / 256 : k), (81 / 512 * l : k), (81 / 1024 * l : k),
      (-(5 / 16) : k), (-(5 / 16) : k), (-(9 / 64 * l) : k),
      (-(5 / 8) : k), (-(9 / 64 * l) : k), (-(5 / 16) : k),
      (-(9 / 32 * l) : k), (-(9 / 128 * l) : k), (-(5 / 16) : k),
      (-(5 / 16) : k), (-(9 / 32 * l) : k), (-(9 / 64 * l) : k),
      (-(5 / 16) : k), (-(9 / 64 * l) : k), (-(9 / 64 * l) : k),
      (9 / 16 * l : k)]
      [
      [4, 3, 0, 0, 0, 0, 0], [5, 1, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [6, 0, 0, 1, 0, 0, 0],
      [6, 0, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0], [2, 3, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0],
      [3, 1, 2, 0, 0, 0, 0], [3, 2, 0, 1, 0, 0, 0], [3, 2, 1, 0, 0, 0, 0], [4, 0, 1, 1, 0, 0, 0],
      [4, 0, 2, 0, 0, 0, 0], [4, 1, 0, 0, 1, 0, 0], [4, 1, 0, 1, 0, 0, 0], [5, 0, 0, 0, 0, 1, 0],
      [5, 0, 0, 0, 1, 0, 0], [0, 3, 2, 0, 0, 0, 0], [0, 4, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 1, 3, 0, 0, 0, 0], [1, 2, 1, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0],
      [1, 3, 0, 1, 0, 0, 0], [2, 0, 2, 1, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0], [2, 1, 0, 2, 0, 0, 0],
      [2, 1, 1, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0], [2, 2, 0, 0, 0, 1, 0], [2, 2, 0, 0, 1, 0, 0],
      [3, 0, 0, 1, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0], [3, 0, 1, 0, 0, 1, 0], [3, 0, 1, 0, 1, 0, 0],
      [3, 1, 0, 0, 0, 0, 1], [3, 1, 0, 0, 0, 1, 0], [4, 0, 0, 0, 0, 0, 1], [0, 0, 3, 1, 0, 0, 0],
      [0, 0, 4, 0, 0, 0, 0], [0, 1, 1, 2, 0, 0, 0], [0, 1, 2, 0, 1, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 2, 0, 1, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 2, 1, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0],
      [0, 3, 0, 0, 0, 0, 1], [0, 3, 0, 0, 0, 1, 0], [1, 0, 0, 3, 0, 0, 0], [1, 0, 1, 1, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0], [1, 0, 2, 0, 0, 1, 0], [1, 0, 2, 0, 1, 0, 0], [1, 1, 0, 0, 2, 0, 0],
      [1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 1, 1, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0],
      [1, 2, 0, 0, 0, 0, 1], [2, 0, 0, 0, 1, 1, 0], [2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 1, 0, 0, 1],
      [2, 0, 0, 1, 0, 1, 0], [2, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 2, 0, 1, 0],
      [0, 0, 0, 2, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 1, 1, 0, 0, 1],
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 1, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 0, 1],
      [0, 1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0, 1], [1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 2, 0],
      [1, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2]] := by
  simp only [rhoBaseGroupHighA_noA7B_Rest810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem uniqueHighA_impossible_of_l_zero_B_pos
    (beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone810 A B C0 D0 E0 F0 G0)
    (hBpos : 0 < B.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hc : (19635 / 1048576 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((19635 / 1048576 : k) • (A ^ 7 * B)).natDegree =
        7 * A.natDegree + B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 7 hA) hBne,
      natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighA_noA7B_Rest810 0 beta gamma delta epsilon
          zeta eta theta A B C0 D0 E0 F0 G0).natDegree <
        7 * A.natDegree + B.natDegree := by
    rcases hcone with ⟨hApos, hBlt, hC, hD, hE, hF, hG⟩
    have hbase :
        (rhoBaseGroupHighA_noA7B_Rest810 0 A B C0 D0 E0 F0 G0).natDegree <
          7 * A.natDegree + B.natDegree := by
      rw [speedRefl_rhoBaseGroupHighA_noA7B_Rest810_eq_polyOf]
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
    have hbetaG :
        (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      rw [speedRefl_rhoBetaGroupPolynomial810_eq_polyOf]
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
    have hgammaG :
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      rw [speedRefl_rhoGammaGroupPolynomial810_eq_polyOf]
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
    have hdeltaG :
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      rw [speedRefl_rhoDeltaGroupPolynomial810_eq_polyOf]
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
    have hepsilonG :
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      rw [speedRefl_rhoEpsilonGroupPolynomial810_eq_polyOf]
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
    have hzetaG :
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      rw [speedRefl_rhoZetaGroupPolynomial810_eq_polyOf]
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
    have hetaG :
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree + B.natDegree := by
      rw [speedRefl_rhoEtaGroupPolynomial810_eq_polyOf]
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
    have hthetaG :
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree <
          7 * A.natDegree + B.natDegree := by
      rw [speedRefl_rhoThetaGroupPolynomial810_eq_polyOf]
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
    simp only [degreeZeroPrimitiveHighA_noA7B_Rest810]
    exact natDegree_add8_lt810 hbase (natDegree_smul_lt810 beta hbetaG)
      (natDegree_smul_lt810 gamma hgammaG)
      (natDegree_smul_lt810 delta hdeltaG)
      (natDegree_smul_lt810 epsilon hepsilonG)
      (natDegree_smul_lt810 zeta hzetaG) (natDegree_smul_lt810 eta hetaG)
      (natDegree_smul_lt810 theta hthetaG)
  rw [degreeZeroPrimitivePolynomial810_eq_A7B_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega
set_option maxHeartbeats 64000000 in

theorem highA_l0_A7Coefficient810_natDegree_eq_zero
    (beta : k) {B : k[X]} (hB : B.natDegree = 0) :
    (highA_l0_A7Coefficient810 beta B).natDegree = 0 := by
  have hsmul : ((19635 / 1048576 : k) • B).natDegree ≤ 0 :=
    (natDegree_smul_le810 _ B).trans hB.le
  have hc : (C (2601 / 1048576 * beta : k) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((19635 / 1048576 : k) • B +
      C (2601 / 1048576 * beta : k)).natDegree = 0
  exact natDegree_eq_zero_of_le_zero <|
    (natDegree_add_le _ _).trans (max_le hsmul hc.le)

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoBetaGroupNoA7Polynomial810` (22 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoBetaGroupNoA7Polynomial810_eq_polyOf
    (A B C0 D0 E0 F0 : k[X]) :
    rhoBetaGroupNoA7Polynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (-(15687 / 262144) : k), (-(189 / 8192) : k), (567 / 16384 : k),
      (1701 / 8192 : k), (273 / 4096 : k), (273 / 2048 : k),
      (483 / 16384 : k), (-(91 / 1024) : k), (-(7 / 128) : k),
      (-(7 / 128) : k), (-(21 / 64) : k), (-(77 / 512) : k),
      (-(21 / 256) : k), (-(77 / 512) : k), (-(35 / 256) : k),
      (7 / 64 : k), (7 / 64 : k), (7 / 32 : k),
      (7 / 32 : k), (7 / 64 : k), (7 / 32 : k),
      (-(7 / 16) : k)]
      [
      [4, 2, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0], [1, 4, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0],
      [3, 0, 2, 0, 0, 0], [3, 1, 0, 1, 0, 0], [4, 0, 0, 0, 1, 0], [0, 2, 2, 0, 0, 0],
      [0, 3, 0, 1, 0, 0], [1, 0, 3, 0, 0, 0], [1, 1, 1, 1, 0, 0], [1, 2, 0, 0, 1, 0],
      [2, 0, 0, 2, 0, 0], [2, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 1], [0, 0, 1, 2, 0, 0],
      [0, 0, 2, 0, 1, 0], [0, 1, 0, 1, 1, 0], [0, 1, 1, 0, 0, 1], [1, 0, 0, 0, 2, 0],
      [1, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2]] := by
  simp only [rhoBetaGroupNoA7Polynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem uniqueHighA_impossible_of_l_zero_B_const_A7_ne
    (beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone810 A B C0 D0 E0 F0 G0)
    (hB : B.natDegree = 0)
    (hK : highA_l0_A7Coefficient810 beta B ≠ 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hKdeg :
      (highA_l0_A7Coefficient810 beta B).natDegree = 0 :=
    highA_l0_A7Coefficient810_natDegree_eq_zero beta hB
  have hlead :
      (A ^ 7 * highA_l0_A7Coefficient810 beta B).natDegree =
        7 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 7 hA) hK, natDegree_pow, hKdeg, add_zero]
  have hrest :
      (degreeZeroPrimitiveHighA_l0_noA7_Rest810 beta gamma delta epsilon
          zeta eta theta A B C0 D0 E0 F0 G0).natDegree <
        7 * A.natDegree := by
    rcases hcone with ⟨hApos, hBlt, hC, hD, hE, hF, hG⟩
    have hbase :
        (rhoBaseGroupHighA_noA7B_Rest810 0 A B C0 D0 E0 F0 G0).natDegree <
          7 * A.natDegree := by
      rw [speedRefl_rhoBaseGroupHighA_noA7B_Rest810_eq_polyOf]
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
    have hbetaG :
        (rhoBetaGroupNoA7Polynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      rw [speedRefl_rhoBetaGroupNoA7Polynomial810_eq_polyOf]
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
    have hgammaG :
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      rw [speedRefl_rhoGammaGroupPolynomial810_eq_polyOf]
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
    have hdeltaG :
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      rw [speedRefl_rhoDeltaGroupPolynomial810_eq_polyOf]
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
    have hepsilonG :
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      rw [speedRefl_rhoEpsilonGroupPolynomial810_eq_polyOf]
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
    have hzetaG :
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      rw [speedRefl_rhoZetaGroupPolynomial810_eq_polyOf]
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
    have hetaG :
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          7 * A.natDegree := by
      rw [speedRefl_rhoEtaGroupPolynomial810_eq_polyOf]
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
    have hthetaG :
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree <
          7 * A.natDegree := by
      rw [speedRefl_rhoThetaGroupPolynomial810_eq_polyOf]
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
    simp only [degreeZeroPrimitiveHighA_l0_noA7_Rest810]
    exact natDegree_add8_lt810 hbase (natDegree_smul_lt810 beta hbetaG)
      (natDegree_smul_lt810 gamma hgammaG)
      (natDegree_smul_lt810 delta hdeltaG)
      (natDegree_smul_lt810 epsilon hepsilonG)
      (natDegree_smul_lt810 zeta hzetaG) (natDegree_smul_lt810 eta hetaG)
      (natDegree_smul_lt810 theta hthetaG)
  rw [degreeZeroPrimitivePolynomial810_eq_A7_combined_add_rest,
    highA_l0_A7_combined_eq,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoBaseGroupHighC0Rest810` (83 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoBaseGroupHighC0Rest810_eq_polyOf
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupHighC0Rest810 l A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (19635 / 1048576 : k), (369495 / 268435456 * l : k), (-(17115 / 131072) : k),
      (-(315 / 2048) : k), (-(189945 / 4194304 * l) : k), (-(3255 / 131072) : k),
      (-(61425 / 4194304 * l) : k), (315 / 8192 : k), (1575 / 4096 : k),
      (14175 / 262144 * l : k), (6185 / 16384 : k), (6115 / 16384 : k),
      (28161 / 131072 * l : k), (1495 / 8192 : k), (27279 / 524288 * l : k),
      (1425 / 8192 : k), (27279 / 262144 * l : k), (515 / 16384 : k),
      (4977 / 262144 * l : k), (-(265 / 2048) : k), (-(125 / 2048) : k),
      (-(567 / 16384 * l) : k), (-(255 / 1024) : k), (-(375 / 512) : k),
      (-(3339 / 16384 * l) : k), (-(235 / 1024) : k), (-(1071 / 8192 * l) : k),
      (-(735 / 2048) : k), (-(1071 / 16384 * l) : k), (-(735 / 2048) : k),
      (-(705 / 1024) : k), (-(3213 / 8192 * l) : k), (-(165 / 512) : k),
      (-(189 / 1024 * l) : k), (-(455 / 2048) : k), (-(261 / 4096 * l) : k),
      (-(425 / 2048) : k), (-(981 / 8192 * l) : k), (-(255 / 2048) : k),
      (-(459 / 4096 * l) : k), (-(459 / 32768 * l) : k), (15 / 128 : k),
      (45 / 128 : k), (45 / 128 : k), (189 / 1024 * l : k),
      (85 / 256 : k), (45 / 512 * l : k), (85 / 256 : k),
      (45 / 256 * l : k), (15 / 256 : k), (27 / 512 * l : k),
      (15 / 128 : k), (85 / 128 : k), (45 / 256 * l : k),
      (5 / 16 : k), (171 / 1024 * l : k), (5 / 16 : k),
      (5 / 8 : k), (171 / 512 * l : k), (45 / 128 : k),
      (81 / 256 * l : k), (81 / 1024 * l : k), (75 / 256 : k),
      (81 / 1024 * l : k), (45 / 256 : k), (81 / 512 * l : k),
      (81 / 1024 * l : k), (-(5 / 16) : k), (-(5 / 16) : k),
      (-(9 / 64 * l) : k), (-(5 / 8) : k), (-(9 / 64 * l) : k),
      (-(5 / 16) : k), (-(9 / 32 * l) : k), (-(9 / 128 * l) : k),
      (-(5 / 16) : k), (-(5 / 16) : k), (-(9 / 32 * l) : k),
      (-(9 / 64 * l) : k), (-(5 / 16) : k), (-(9 / 64 * l) : k),
      (-(9 / 64 * l) : k), (9 / 16 * l : k)]
      [
      [7, 1, 0, 0, 0, 0, 0], [8, 0, 0, 0, 0, 0, 0], [4, 3, 0, 0, 0, 0, 0], [5, 1, 1, 0, 0, 0, 0],
      [5, 2, 0, 0, 0, 0, 0], [6, 0, 0, 1, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0],
      [2, 3, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [3, 1, 2, 0, 0, 0, 0], [3, 2, 0, 1, 0, 0, 0],
      [3, 2, 1, 0, 0, 0, 0], [4, 0, 1, 1, 0, 0, 0], [4, 0, 2, 0, 0, 0, 0], [4, 1, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0], [5, 0, 0, 0, 0, 1, 0], [5, 0, 0, 0, 1, 0, 0], [0, 3, 2, 0, 0, 0, 0],
      [0, 4, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 3, 0, 0, 0, 0], [1, 2, 1, 1, 0, 0, 0],
      [1, 2, 2, 0, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [1, 3, 0, 1, 0, 0, 0], [2, 0, 2, 1, 0, 0, 0],
      [2, 0, 3, 0, 0, 0, 0], [2, 1, 0, 2, 0, 0, 0], [2, 1, 1, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0],
      [2, 2, 0, 0, 0, 1, 0], [2, 2, 0, 0, 1, 0, 0], [3, 0, 0, 1, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0],
      [3, 0, 1, 0, 0, 1, 0], [3, 0, 1, 0, 1, 0, 0], [3, 1, 0, 0, 0, 0, 1], [3, 1, 0, 0, 0, 1, 0],
      [4, 0, 0, 0, 0, 0, 1], [0, 0, 3, 1, 0, 0, 0], [0, 1, 1, 2, 0, 0, 0], [0, 1, 2, 0, 1, 0, 0],
      [0, 1, 2, 1, 0, 0, 0], [0, 2, 0, 1, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 2, 1, 0, 0, 1, 0],
      [0, 2, 1, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1], [0, 3, 0, 0, 0, 1, 0], [1, 0, 0, 3, 0, 0, 0],
      [1, 0, 1, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [1, 0, 2, 0, 0, 1, 0], [1, 0, 2, 0, 1, 0, 0],
      [1, 1, 0, 0, 2, 0, 0], [1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 1, 1, 0, 0, 0, 1],
      [1, 1, 1, 0, 0, 1, 0], [1, 2, 0, 0, 0, 0, 1], [2, 0, 0, 0, 1, 1, 0], [2, 0, 0, 0, 2, 0, 0],
      [2, 0, 0, 1, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0], [2, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 2, 0, 0],
      [0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0], [0, 0, 1, 0, 2, 0, 0],
      [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 1, 0, 0, 0, 2, 0],
      [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0, 1], [1, 0, 0, 0, 0, 1, 1],
      [1, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2]] := by
  simp only [rhoBaseGroupHighC0Rest810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem uniqueNonconstantC0_impossible_of_l_ne
    (l beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hCpos : 0 < C0.natDegree) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0)
    (hG : G0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hCne : C0 ≠ 0 := by
    intro hC0
    simp [hC0] at hCpos
  have hc : (63 / 4096 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead :
      ((63 / 4096 * l : k) • C0 ^ 4).natDegree =
        4 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighC0Rest810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree <
        4 * C0.natDegree := by
    have hbase :
        (rhoBaseGroupHighC0Rest810 l A B C0 D0 E0 F0 G0).natDegree <
          4 * C0.natDegree := by
      rw [speedRefl_rhoBaseGroupHighC0Rest810_eq_polyOf]
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
    have hbetaG :
        (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      rw [speedRefl_rhoBetaGroupPolynomial810_eq_polyOf]
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
    have hgammaG :
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      rw [speedRefl_rhoGammaGroupPolynomial810_eq_polyOf]
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
    have hdeltaG :
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      rw [speedRefl_rhoDeltaGroupPolynomial810_eq_polyOf]
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
    have hepsilonG :
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      rw [speedRefl_rhoEpsilonGroupPolynomial810_eq_polyOf]
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
    have hzetaG :
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      rw [speedRefl_rhoZetaGroupPolynomial810_eq_polyOf]
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
    have hetaG :
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          4 * C0.natDegree := by
      rw [speedRefl_rhoEtaGroupPolynomial810_eq_polyOf]
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
    have hthetaG :
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree <
          4 * C0.natDegree := by
      rw [speedRefl_rhoThetaGroupPolynomial810_eq_polyOf]
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
    simp only [degreeZeroPrimitiveHighC0Rest810]
    exact natDegree_add8_lt810 hbase (natDegree_smul_lt810 beta hbetaG)
      (natDegree_smul_lt810 gamma hgammaG)
      (natDegree_smul_lt810 delta hdeltaG)
      (natDegree_smul_lt810 epsilon hepsilonG)
      (natDegree_smul_lt810 zeta hzetaG) (natDegree_smul_lt810 eta hetaG)
      (natDegree_smul_lt810 theta hthetaG)
  rw [degreeZeroPrimitivePolynomial810_eq_C04_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected form of `rhoBaseGroupHighG0Rest810` (83 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoBaseGroupHighG0Rest810_eq_polyOf
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupHighG0Rest810 l A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (19635 / 1048576 : k), (369495 / 268435456 * l : k), (-(17115 / 131072) : k),
      (-(315 / 2048) : k), (-(189945 / 4194304 * l) : k), (-(3255 / 131072) : k),
      (-(61425 / 4194304 * l) : k), (315 / 8192 : k), (1575 / 4096 : k),
      (14175 / 262144 * l : k), (6185 / 16384 : k), (6115 / 16384 : k),
      (28161 / 131072 * l : k), (1495 / 8192 : k), (27279 / 524288 * l : k),
      (1425 / 8192 : k), (27279 / 262144 * l : k), (515 / 16384 : k),
      (4977 / 262144 * l : k), (-(265 / 2048) : k), (-(125 / 2048) : k),
      (-(567 / 16384 * l) : k), (-(255 / 1024) : k), (-(375 / 512) : k),
      (-(3339 / 16384 * l) : k), (-(235 / 1024) : k), (-(1071 / 8192 * l) : k),
      (-(735 / 2048) : k), (-(1071 / 16384 * l) : k), (-(735 / 2048) : k),
      (-(705 / 1024) : k), (-(3213 / 8192 * l) : k), (-(165 / 512) : k),
      (-(189 / 1024 * l) : k), (-(455 / 2048) : k), (-(261 / 4096 * l) : k),
      (-(425 / 2048) : k), (-(981 / 8192 * l) : k), (-(255 / 2048) : k),
      (-(459 / 4096 * l) : k), (-(459 / 32768 * l) : k), (15 / 128 : k),
      (63 / 4096 * l : k), (45 / 128 : k), (45 / 128 : k),
      (189 / 1024 * l : k), (85 / 256 : k), (45 / 512 * l : k),
      (85 / 256 : k), (45 / 256 * l : k), (15 / 256 : k),
      (27 / 512 * l : k), (15 / 128 : k), (85 / 128 : k),
      (45 / 256 * l : k), (5 / 16 : k), (171 / 1024 * l : k),
      (5 / 16 : k), (5 / 8 : k), (171 / 512 * l : k),
      (45 / 128 : k), (81 / 256 * l : k), (81 / 1024 * l : k),
      (75 / 256 : k), (81 / 1024 * l : k), (45 / 256 : k),
      (81 / 512 * l : k), (81 / 1024 * l : k), (-(5 / 16) : k),
      (-(5 / 16) : k), (-(9 / 64 * l) : k), (-(5 / 8) : k),
      (-(9 / 64 * l) : k), (-(5 / 16) : k), (-(9 / 32 * l) : k),
      (-(9 / 128 * l) : k), (-(5 / 16) : k), (-(5 / 16) : k),
      (-(9 / 32 * l) : k), (-(9 / 64 * l) : k), (-(5 / 16) : k),
      (-(9 / 64 * l) : k), (-(9 / 64 * l) : k)]
      [
      [7, 1, 0, 0, 0, 0, 0], [8, 0, 0, 0, 0, 0, 0], [4, 3, 0, 0, 0, 0, 0], [5, 1, 1, 0, 0, 0, 0],
      [5, 2, 0, 0, 0, 0, 0], [6, 0, 0, 1, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0],
      [2, 3, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [3, 1, 2, 0, 0, 0, 0], [3, 2, 0, 1, 0, 0, 0],
      [3, 2, 1, 0, 0, 0, 0], [4, 0, 1, 1, 0, 0, 0], [4, 0, 2, 0, 0, 0, 0], [4, 1, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0], [5, 0, 0, 0, 0, 1, 0], [5, 0, 0, 0, 1, 0, 0], [0, 3, 2, 0, 0, 0, 0],
      [0, 4, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 3, 0, 0, 0, 0], [1, 2, 1, 1, 0, 0, 0],
      [1, 2, 2, 0, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [1, 3, 0, 1, 0, 0, 0], [2, 0, 2, 1, 0, 0, 0],
      [2, 0, 3, 0, 0, 0, 0], [2, 1, 0, 2, 0, 0, 0], [2, 1, 1, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0],
      [2, 2, 0, 0, 0, 1, 0], [2, 2, 0, 0, 1, 0, 0], [3, 0, 0, 1, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0],
      [3, 0, 1, 0, 0, 1, 0], [3, 0, 1, 0, 1, 0, 0], [3, 1, 0, 0, 0, 0, 1], [3, 1, 0, 0, 0, 1, 0],
      [4, 0, 0, 0, 0, 0, 1], [0, 0, 3, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 1, 1, 2, 0, 0, 0],
      [0, 1, 2, 0, 1, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 2, 0, 1, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 2, 1, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1], [0, 3, 0, 0, 0, 1, 0],
      [1, 0, 0, 3, 0, 0, 0], [1, 0, 1, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [1, 0, 2, 0, 0, 1, 0],
      [1, 0, 2, 0, 1, 0, 0], [1, 1, 0, 0, 2, 0, 0], [1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0],
      [1, 1, 1, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 2, 0, 0, 0, 0, 1], [2, 0, 0, 0, 1, 1, 0],
      [2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 1, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0], [2, 0, 1, 0, 0, 0, 1],
      [0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 1, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0, 1],
      [1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 1, 0, 1]] := by
  simp only [rhoBaseGroupHighG0Rest810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem uniqueNonconstantG0_impossible_of_l_ne
    (l beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0)
    (hGpos : 0 < G0.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ j hj hder
  have hGne : G0 ≠ 0 := by
    intro hG0
    simp [hG0] at hGpos
  have hc : (9 / 16 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead :
      ((9 / 16 * l : k) • G0 ^ 2).natDegree =
        2 * G0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighG0Rest810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree <
        2 * G0.natDegree := by
    have hbase :
        (rhoBaseGroupHighG0Rest810 l A B C0 D0 E0 F0 G0).natDegree <
          2 * G0.natDegree := by
      rw [speedRefl_rhoBaseGroupHighG0Rest810_eq_polyOf]
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
    have hbetaG :
        (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      rw [speedRefl_rhoBetaGroupPolynomial810_eq_polyOf]
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
    have hgammaG :
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      rw [speedRefl_rhoGammaGroupPolynomial810_eq_polyOf]
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
    have hdeltaG :
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      rw [speedRefl_rhoDeltaGroupPolynomial810_eq_polyOf]
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
    have hepsilonG :
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      rw [speedRefl_rhoEpsilonGroupPolynomial810_eq_polyOf]
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
    have hzetaG :
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      rw [speedRefl_rhoZetaGroupPolynomial810_eq_polyOf]
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
    have hetaG :
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree <
          2 * G0.natDegree := by
      rw [speedRefl_rhoEtaGroupPolynomial810_eq_polyOf]
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
    have hthetaG :
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0).natDegree <
          2 * G0.natDegree := by
      rw [speedRefl_rhoThetaGroupPolynomial810_eq_polyOf]
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
    simp only [degreeZeroPrimitiveHighG0Rest810]
    exact natDegree_add8_lt810 hbase (natDegree_smul_lt810 beta hbetaG)
      (natDegree_smul_lt810 gamma hgammaG)
      (natDegree_smul_lt810 delta hdeltaG)
      (natDegree_smul_lt810 epsilon hepsilonG)
      (natDegree_smul_lt810 zeta hzetaG) (natDegree_smul_lt810 eta hetaG)
      (natDegree_smul_lt810 theta hthetaG)
  rw [degreeZeroPrimitivePolynomial810_eq_G02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end UniqueFaces810


end Max11DegreeRoutes
