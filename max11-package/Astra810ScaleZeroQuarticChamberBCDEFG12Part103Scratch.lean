import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part101Scratch
import Max11SpeedReflectDegLibScratch

/-! # BCDEFG12 chamber, part 2

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
/-- An exact expansion of the auxiliary; the remaining polynomial is grouped into small chunks. -/
theorem degreeZeroBandAuxBCDEFG12810_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticLTowerFace810 l A +
      n7QuarticBetaTowerFace810 beta A +
      n7QuarticDeltaTowerFace810 delta A +
      n7QuarticZetaTowerFace810 zeta A +
      n7QuarticThetaTowerFace810 theta A +
      bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroBandAuxBCDEFG12810,
    degreeZeroN7TowerQuartic810,
    degreeZeroPrimitiveQuartic810,
    rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810,
    rhoGammaGroupQuartic810,
    rhoDeltaGroupQuartic810,
    rhoEpsilonGroupQuartic810,
    rhoZetaGroupQuartic810,
    rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810,
    degreeZeroOmicronQuartic810,
    degreeZeroNuQuartic810,
    degreeZeroKappaQuartic810,
    bandAuxBCDEFG12Rest810,
    bandAuxBCDEFG12RestFree1810,
    bandAuxBCDEFG12RestFree2810,
    bandAuxBCDEFG12RestFree3810,
    bandAuxBCDEFG12RestL1810,
    bandAuxBCDEFG12RestL2810,
    bandAuxBCDEFG12RestL3810,
    bandAuxBCDEFG12RestL4810,
    bandAuxBCDEFG12RestL5810,
    bandAuxBCDEFG12RestL6810,
    bandAuxBCDEFG12RestBeta1810,
    bandAuxBCDEFG12RestBeta2810,
    bandAuxBCDEFG12RestBeta3810,
    bandAuxBCDEFG12RestBeta4810,
    bandAuxBCDEFG12RestGamma1810,
    bandAuxBCDEFG12RestDelta1810,
    bandAuxBCDEFG12RestDelta2810,
    bandAuxBCDEFG12RestDelta3810,
    bandAuxBCDEFG12RestEpsilon1810,
    bandAuxBCDEFG12RestZeta1810,
    bandAuxBCDEFG12RestZeta2810,
    bandAuxBCDEFG12RestEta1810,
    bandAuxBCDEFG12RestTheta1810,
    n7QuarticLTowerFace810,
    n7QuarticBetaTowerFace810,
    n7QuarticDeltaTowerFace810,
    n7QuarticZetaTowerFace810,
    n7QuarticThetaTowerFace810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- The auxiliary retains the degree bound of N7 on this chamber. -/
theorem degreeZeroBandAuxBCDEFG12810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree := by
  have hcone := hc.1
  obtain ⟨ha, hab, hac, had, hae, haf, hag⟩ := hcone
  have hn := degreeZeroN7TowerQuartic810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G
    ha hprim homi hnu hkap
  have hm : ((1 / 4 : k) • (A * C * (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G))).natDegree ≤
      3 * A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have h1 : (A * C * (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤
        (A * C).natDegree + (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    have h2 : (A * C).natDegree ≤ A.natDegree + C.natDegree := natDegree_mul_le
    rw [hkap] at h1
    omega
  exact natDegree_add_le810 hn hm

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 7

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
theorem bcdefg12Kappa_split810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12KappaFace810 A B C D E F G + bcdefg12KappaRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, bcdefg12KappaFace810, bcdefg12KappaRest810, bcdefg12KappaRest0810, bcdefg12KappaRest1810, bcdefg12KappaRest2810, bcdefg12KappaRest3810, bcdefg12KappaRest4810, bcdefg12KappaRest5810, bcdefg12KappaRest6810, bcdefg12KappaRest7810, bcdefg12KappaRest8810, bcdefg12KappaRest9810, bcdefg12KappaRest10810]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest10810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)
      ]
      [
      [1, 0, 0, 0, 0, 0, 0]
      ] := by
  simp only [bcdefg12KappaRest10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest9810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * eta : k)
      ]
      [
      [0, 1, 0, 0, 0, 0, 0]
      ] := by
  simp only [bcdefg12KappaRest9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest8810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 128 * zeta : k), (3 / 8 * zeta : k)
      ]
      [
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]
      ] := by
  simp only [bcdefg12KappaRest8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest7810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 2 * epsilon : k)
      ]
      [
      [0, 0, 0, 1, 0, 0, 0]
      ] := by
  simp only [bcdefg12KappaRest7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest6810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 1024 * delta : k), (5 / 64 * delta : k), (-15 / 128 * delta : k),
      (5 / 8 * delta : k)
      ]
      [
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [bcdefg12KappaRest6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest5810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 16 * gamma : k), (3 / 4 * gamma : k)
      ]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [bcdefg12KappaRest5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest4810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 8 * beta : k)
      ]
      [
      [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [bcdefg12KappaRest4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * beta : k), (21 / 1024 * beta : k), (7 / 1024 * beta : k),
      (7 / 64 * beta : k), (-7 / 64 * beta : k), (-7 / 128 * beta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [bcdefg12KappaRest3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest2810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 64 * l : k), (-63 / 1024 * l : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 128 * l : k)
      ]
      [
      [1, 0, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [bcdefg12KappaRest2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * l : k), (45 / 8192 * l : k), (-9 / 16384 * l : k),
      (27 / 1024 * l : k), (-9 / 512 * l : k), (9 / 1024 * l : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [bcdefg12KappaRest1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12KappaRest0810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12KappaRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-15 / 128 : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0]
      ] := by
  simp only [bcdefg12KappaRest0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- All remainder chunks lie strictly below the face under the strict load bands. -/
theorem bcdefg12Kappa_rest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12KappaRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hr0 : (bcdefg12KappaRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest0810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr1 : (bcdefg12KappaRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12KappaRest1810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest1810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr2 : (bcdefg12KappaRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12KappaRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest2810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr3 : (bcdefg12KappaRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbbeta with hz | hb
    ·
      simp only [bcdefg12KappaRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest3810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr4 : (bcdefg12KappaRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbbeta with hz | hb
    ·
      simp only [bcdefg12KappaRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest4810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr5 : (bcdefg12KappaRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest5810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr6 : (bcdefg12KappaRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbdelta with hz | hb
    ·
      simp only [bcdefg12KappaRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest6810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr7 : (bcdefg12KappaRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest7810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr8 : (bcdefg12KappaRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbzeta with hz | hb
    ·
      simp only [bcdefg12KappaRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest8810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr9 : (bcdefg12KappaRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest9810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr10 : (bcdefg12KappaRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbtheta with hz | hb
    ·
      simp only [bcdefg12KappaRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12KappaRest10810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  unfold bcdefg12KappaRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10)

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 10

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
theorem bcdefg12Mu_split810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12MuFace810 A B C D E F G + bcdefg12MuRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroMuQuartic810, bcdefg12MuFace810, bcdefg12MuRest810, bcdefg12MuRest0810, bcdefg12MuRest1810, bcdefg12MuRest2810, bcdefg12MuRest3810, bcdefg12MuRest4810, bcdefg12MuRest5810, bcdefg12MuRest6810, bcdefg12MuRest7810, bcdefg12MuRest8810, bcdefg12MuRest9810, bcdefg12MuRest10810]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest10810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)
      ]
      [
      [0, 1, 0, 0, 0, 0, 0]
      ] := by
  simp only [bcdefg12MuRest10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest9810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * eta : k)
      ]
      [
      [0, 0, 1, 0, 0, 0, 0]
      ] := by
  simp only [bcdefg12MuRest9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest8810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 64 * zeta : k), (3 / 8 * zeta : k)
      ]
      [
      [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0]
      ] := by
  simp only [bcdefg12MuRest8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest7810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-1 / 8 * epsilon : k), (1 / 2 * epsilon : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [bcdefg12MuRest7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest6810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-5 / 1024 * delta : k), (-5 / 64 * delta : k), (-15 / 64 * delta : k),
      (5 / 8 * delta : k)
      ]
      [
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [bcdefg12MuRest6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest5810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 128 * gamma : k), (-3 / 16 * gamma : k), (-3 / 32 * gamma : k),
      (3 / 4 * gamma : k)
      ]
      [
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [bcdefg12MuRest5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest4810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-7 / 64 * beta : k)
      ]
      [
      [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [bcdefg12MuRest4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-7 / 8192 * beta : k), (-7 / 1024 * beta : k), (7 / 512 * beta : k),
      (-7 / 64 * beta : k), (21 / 1024 * beta : k), (-7 / 64 * beta : k)
      ]
      [
      [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0]
      ] := by
  simp only [bcdefg12MuRest3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-9 / 512 * l : k), (-63 / 1024 * l : k), (-63 / 1024 * l : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k)
      ]
      [
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [bcdefg12MuRest2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-45 / 262144 * l : k), (-9 / 8192 * l : k), (-9 / 8192 * l : k),
      (-9 / 1024 * l : k), (63 / 8192 * l : k), (-9 / 512 * l : k)
      ]
      [
      [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0]
      ] := by
  simp only [bcdefg12MuRest1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bcdefg12MuRest0810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bcdefg12MuRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-15 / 128 : k), (-15 / 64 : k),
      (5 / 16 : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [bcdefg12MuRest0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- All remainder chunks lie strictly below the face under the strict load bands. -/
theorem bcdefg12Mu_rest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12MuRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hr0 : (bcdefg12MuRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest0810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr1 : (bcdefg12MuRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12MuRest1810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest1810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr2 : (bcdefg12MuRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbl with hz | hb
    ·
      simp only [bcdefg12MuRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest2810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr3 : (bcdefg12MuRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbbeta with hz | hb
    ·
      simp only [bcdefg12MuRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest3810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr4 : (bcdefg12MuRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbbeta with hz | hb
    ·
      simp only [bcdefg12MuRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest4810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr5 : (bcdefg12MuRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest5810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr6 : (bcdefg12MuRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbdelta with hz | hb
    ·
      simp only [bcdefg12MuRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest6810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr7 : (bcdefg12MuRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest7810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr8 : (bcdefg12MuRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbzeta with hz | hb
    ·
      simp only [bcdefg12MuRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest8810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr9 : (bcdefg12MuRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest9810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hr10 : (bcdefg12MuRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbtheta with hz | hb
    ·
      simp only [bcdefg12MuRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    ·
      rw [astra4aaChamberRefl_ChamberBCDEFG12Part103_bcdefg12MuRest10810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  unfold bcdefg12MuRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10)

end Max11DegreeRoutes
