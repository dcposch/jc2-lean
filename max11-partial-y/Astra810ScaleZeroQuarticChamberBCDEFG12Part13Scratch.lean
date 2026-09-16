import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part101Scratch
import Max11SpeedReflectDegLibScratch

/-! # BCDEFG12 chamber, part 13

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
theorem bcdefg12Xi_split810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12XiFace810 A B C D E F G + bcdefg12XiRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroXiQuartic810, bcdefg12XiFace810, bcdefg12XiRest810, bcdefg12XiRest0810, bcdefg12XiRest1810, bcdefg12XiRest2810, bcdefg12XiRest3810, bcdefg12XiRest4810, bcdefg12XiRest5810, bcdefg12XiRest6810, bcdefg12XiRest7810, bcdefg12XiRest8810, bcdefg12XiRest9810, bcdefg12XiRest10810, bcdefg12XiRest11810, bcdefg12XiRest12810]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest12810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest12810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)
      ]
      [
      [0, 0, 0, 1, 0, 0, 0]
      ] := by
  simp only [bcdefg12XiRest12810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest11810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest11810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-1 / 16 * eta : k), (1 / 4 * eta : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [bcdefg12XiRest11810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest10810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 64 * zeta : k), (-3 / 16 * zeta : k), (3 / 8 * zeta : k)
      ]
      [
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [bcdefg12XiRest10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest9810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 32 * epsilon : k), (-3 / 16 * epsilon : k), (-1 / 8 * epsilon : k),
      (1 / 2 * epsilon : k)
      ]
      [
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [bcdefg12XiRest9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest8810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-5 / 1024 * delta : k), (5 / 128 * delta : k), (-5 / 64 * delta : k),
      (5 / 128 * delta : k), (-5 / 32 * delta : k), (-15 / 64 * delta : k)
      ]
      [
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [bcdefg12XiRest8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest7810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 64 * gamma : k), (3 / 32 * gamma : k), (-3 / 32 * gamma : k),
      (-3 / 16 * gamma : k), (-3 / 32 * gamma : k)
      ]
      [
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [bcdefg12XiRest7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest6810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (49 / 1024 * beta : k), (7 / 128 * beta : k), (-7 / 64 * beta : k),
      (-7 / 64 * beta : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [bcdefg12XiRest6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest5810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-7 / 8192 * beta : k), (7 / 2048 * beta : k), (-7 / 1024 * beta : k),
      (-7 / 1024 * beta : k), (7 / 256 * beta : k), (7 / 512 * beta : k)
      ]
      [
      [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 3, 0, 0, 0, 0, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [bcdefg12XiRest5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest4810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-27 / 256 * l : k), (-27 / 512 * l : k), (-63 / 1024 * l : k),
      (9 / 64 * l : k), (9 / 64 * l : k)
      ]
      [
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1],
      [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [bcdefg12XiRest4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (171 / 8192 * l : k), (9 / 1024 * l : k), (-9 / 512 * l : k),
      (-9 / 512 * l : k), (63 / 2048 * l : k), (-45 / 1024 * l : k)
      ]
      [
      [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0],
      [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0]
      ] := by
  simp only [bcdefg12XiRest3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-45 / 262144 * l : k), (9 / 16384 * l : k), (-9 / 8192 * l : k),
      (-9 / 16384 * l : k), (9 / 4096 * l : k), (-9 / 8192 * l : k)
      ]
      [
      [4, 0, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 3, 0, 0, 0, 0, 0],
      [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [bcdefg12XiRest2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest1810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-15 / 128 : k), (5 / 32 : k)
      ]
      [
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [bcdefg12XiRest1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12XiRest0810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12XiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-15 / 2048 : k), (55 / 1024 : k), (45 / 512 : k),
      (-5 / 64 : k), (-25 / 128 : k), (-25 / 128 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0]
      ] := by
  simp only [bcdefg12XiRest0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- All remainder chunks lie strictly below the face under the strict load bands. -/
theorem bcdefg12Xi_rest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12XiRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hr0 : (bcdefg12XiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest0810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr1 : (bcdefg12XiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest1810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr2 : (bcdefg12XiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12XiRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest2810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr3 : (bcdefg12XiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12XiRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest3810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr4 : (bcdefg12XiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12XiRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest4810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr5 : (bcdefg12XiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbbeta with hz | hb
    ·
      simp only [bcdefg12XiRest5810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest5810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr6 : (bcdefg12XiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbbeta with hz | hb
    ·
      simp only [bcdefg12XiRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest6810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr7 : (bcdefg12XiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest7810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr8 : (bcdefg12XiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbdelta with hz | hb
    ·
      simp only [bcdefg12XiRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest8810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr9 : (bcdefg12XiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest9810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr10 : (bcdefg12XiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbzeta with hz | hb
    ·
      simp only [bcdefg12XiRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest10810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr11 : (bcdefg12XiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest11810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr12 : (bcdefg12XiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbtheta with hz | hb
    ·
      simp only [bcdefg12XiRest12810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part13_bcdefg12XiRest12810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  unfold bcdefg12XiRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10) hr11) hr12)

end Max11DegreeRoutes
