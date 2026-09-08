import Astra810ScaleZeroQuarticChamberBCDEFG12Part01Scratch

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
