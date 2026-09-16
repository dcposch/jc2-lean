import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part101Scratch
import Max11SpeedReflectDegLibScratch

/-! # BCDEFG12 chamber, part 16

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
-/

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

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- The integral splits into its chamber face and remainder. -/
theorem bcdefg12Pi_split810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12PiFace810 A B C D E F G + bcdefg12PiRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroPiQuartic810, bcdefg12PiFace810, bcdefg12PiRest810, bcdefg12PiRest0810, bcdefg12PiRest1810, bcdefg12PiRest2810, bcdefg12PiRest3810, bcdefg12PiRest4810, bcdefg12PiRest5810, bcdefg12PiRest6810, bcdefg12PiRest7810, bcdefg12PiRest8810, bcdefg12PiRest9810, bcdefg12PiRest10810, bcdefg12PiRest11810, bcdefg12PiRest12810, bcdefg12PiRest13810, bcdefg12PiRest14810, bcdefg12PiRest15810, bcdefg12PiRest16810, bcdefg12PiRest17810, piBaseGroupQuartic810, piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810, piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810, piThetaGroupQuartic810]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest0810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-15 / 128 : k), (-35 / 256 : k), (25 / 128 : k), (45 / 64 : k), (45 / 128 : k), (45 / 64 : k)]
        [[1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0]] := by
  simp only [bcdefg12PiRest0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest1810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-5 / 8 : k), (-15 / 16 : k), (-15 / 16 : k), (-5 / 8 : k)]
        [[0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0]] := by
  simp only [bcdefg12PiRest1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest2810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(45 / 131072 * l : k), (-45 / 32768 * l : k), (-3 / 32768 * l : k), (9 / 4096 * l : k), (9 / 4096 * l : k), (-27 / 4096 * l : k)]
        [[4, 1, 1, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0], [3, 3, 0, 0, 0, 0, 0], [3, 1, 0, 0, 1, 0, 0], [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0]] := by
  simp only [bcdefg12PiRest2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest3810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(9 / 4096 * l : k), (-27 / 1024 * l : k), (9 / 512 * l : k), (-189 / 4096 * l : k), (63 / 1024 * l : k), (9 / 128 * l : k)]
        [[2, 1, 2, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0], [1, 3, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0]] := by
  simp only [bcdefg12PiRest3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest4810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(27 / 256 * l : k), (9 / 256 * l : k), (-9 / 64 * l : k), (-63 / 4096 * l : k), (63 / 512 * l : k), (189 / 512 * l : k)]
        [[1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0], [0, 5, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0]] := by
  simp only [bcdefg12PiRest4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest5810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(63 / 512 * l : k), (-9 / 32 * l : k), (-27 / 64 * l : k), (-9 / 32 * l : k), (-27 / 128 * l : k), (-9 / 16 * l : k)]
        [[0, 1, 3, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0]] := by
  simp only [bcdefg12PiRest5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest6810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-3 / 32 * l : k), (9 / 8 * l : k)]
        [[0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1]] := by
  simp only [bcdefg12PiRest6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest7810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(7 / 4096 * beta : k), (-7 / 1024 * beta : k), (7 / 4096 * beta : k), (7 / 512 * beta : k), (7 / 512 * beta : k), (-21 / 256 * beta : k)]
        [[3, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 3, 0, 0, 0, 0, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0]] := by
  simp only [bcdefg12PiRest7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest8810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-7 / 256 * beta : k), (-7 / 64 * beta : k), (7 / 32 * beta : k), (-63 / 512 * beta : k), (21 / 128 * beta : k), (7 / 16 * beta : k)]
        [[1, 1, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0]] := by
  simp only [bcdefg12PiRest8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest9810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(7 / 32 * beta : k), (7 / 32 * beta : k), (-7 / 8 * beta : k)]
        [[0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]] := by
  simp only [bcdefg12PiRest9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest10810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-3 / 32 * gamma : k), (3 / 16 * gamma : k), (-15 / 256 * gamma : k), (3 / 8 * gamma : k), (3 / 4 * gamma : k), (1 / 8 * gamma : k)]
        [[1, 2, 1, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0]] := by
  simp only [bcdefg12PiRest10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest11810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest11810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-3 / 4 * gamma : k), (-3 / 4 * gamma : k)]
        [[0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]] := by
  simp only [bcdefg12PiRest11810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest12810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest12810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(5 / 512 * delta : k), (-5 / 128 * delta : k), (-15 / 256 * delta : k), (5 / 32 * delta : k), (5 / 32 * delta : k), (15 / 32 * delta : k)]
        [[2, 1, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0]] := by
  simp only [bcdefg12PiRest12810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest13810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest13810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest13810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(15 / 32 * delta : k), (-5 / 8 * delta : k), (-5 / 4 * delta : k)]
        [[0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]] := by
  simp only [bcdefg12PiRest13810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest14810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest14810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest14810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(1 / 4 * epsilon : k), (1 / 2 * epsilon : k), (-1 / 2 * epsilon : k), (-1 * epsilon : k), (-1 / 2 * epsilon : k)]
        [[1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]] := by
  simp only [bcdefg12PiRest14810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest15810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest15810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest15810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(3 / 32 * zeta : k), (-3 / 8 * zeta : k), (5 / 32 * zeta : k), (-3 / 4 * zeta : k), (-3 / 4 * zeta : k)]
        [[1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]] := by
  simp only [bcdefg12PiRest15810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest16810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest16810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest16810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(1 / 16 * eta : k), (-1 / 2 * eta : k), (-1 / 4 * eta : k), (2 * eta : k)]
        [[1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]] := by
  simp only [bcdefg12PiRest16810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12PiRest17810`. -/
private theorem astra4sReflChamber16_bcdefg12PiRest17810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12PiRest17810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-1 / 4 * theta : k), (1 * theta : k)]
        [[0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [bcdefg12PiRest17810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, add_assoc]

set_option maxHeartbeats 64000000 in
/-- All remainder chunks lie strictly below the face under the strict load bands. -/
theorem bcdefg12Pi_rest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12PiRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hr0 : (bcdefg12PiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rw [astra4sReflChamber16_bcdefg12PiRest0810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr1 : (bcdefg12PiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rw [astra4sReflChamber16_bcdefg12PiRest1810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr2 : (bcdefg12PiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12PiRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest2810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr3 : (bcdefg12PiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12PiRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest3810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr4 : (bcdefg12PiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12PiRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest4810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr5 : (bcdefg12PiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12PiRest5810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest5810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr6 : (bcdefg12PiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12PiRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest6810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr7 : (bcdefg12PiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbbeta with hz | hb
    ·
      simp only [bcdefg12PiRest7810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest7810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr8 : (bcdefg12PiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbbeta with hz | hb
    ·
      simp only [bcdefg12PiRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest8810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr9 : (bcdefg12PiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbbeta with hz | hb
    ·
      simp only [bcdefg12PiRest9810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest9810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr10 : (bcdefg12PiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rw [astra4sReflChamber16_bcdefg12PiRest10810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr11 : (bcdefg12PiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rw [astra4sReflChamber16_bcdefg12PiRest11810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr12 : (bcdefg12PiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbdelta with hz | hb
    ·
      simp only [bcdefg12PiRest12810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest12810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr13 : (bcdefg12PiRest13810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbdelta with hz | hb
    ·
      simp only [bcdefg12PiRest13810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest13810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr14 : (bcdefg12PiRest14810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rw [astra4sReflChamber16_bcdefg12PiRest14810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr15 : (bcdefg12PiRest15810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbzeta with hz | hb
    ·
      simp only [bcdefg12PiRest15810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest15810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr16 : (bcdefg12PiRest16810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rw [astra4sReflChamber16_bcdefg12PiRest16810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr17 : (bcdefg12PiRest17810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbtheta with hz | hb
    ·
      simp only [bcdefg12PiRest17810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4sReflChamber16_bcdefg12PiRest17810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  unfold bcdefg12PiRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10) hr11) hr12) hr13) hr14) hr15) hr16) hr17)

end Max11DegreeRoutes
