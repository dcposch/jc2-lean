import Astra810ScaleZeroQuarticChamberBCDEFG12Part25Scratch

/-! # BCDEFG12 chamber, part 26

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
/-- The sum of the remainder chunks. -/
def bcdefg12N6Rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12N6RestLF0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestLF1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestLF2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestLF3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL4 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL5 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL6 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestBeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestBeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestBeta2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestBeta3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestGamma1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestDelta2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestEpsilon1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestZeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestTheta1 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Exact expansion into face and remainder. -/
theorem bcdefg12N6_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN6TowerQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12N6Face A B C D E F G + bcdefg12N6Rest l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN6TowerQuartic810, degreeZeroPrimitiveQuartic810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810, rhoBaseGroupQuartic810, rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810, rhoThetaGroupQuartic810, bcdefg12N6Face, bcdefg12N6Rest, bcdefg12N6RestLF0, bcdefg12N6RestLF1, bcdefg12N6RestLF2, bcdefg12N6RestLF3, bcdefg12N6RestL0, bcdefg12N6RestL1, bcdefg12N6RestL2, bcdefg12N6RestL3, bcdefg12N6RestL4, bcdefg12N6RestL5, bcdefg12N6RestL6, bcdefg12N6RestBeta0, bcdefg12N6RestBeta1, bcdefg12N6RestBeta2, bcdefg12N6RestBeta3, bcdefg12N6RestGamma0, bcdefg12N6RestGamma1, bcdefg12N6RestDelta0, bcdefg12N6RestDelta1, bcdefg12N6RestDelta2, bcdefg12N6RestEpsilon0, bcdefg12N6RestEpsilon1, bcdefg12N6RestZeta0, bcdefg12N6RestZeta1, bcdefg12N6RestEta0, bcdefg12N6RestTheta0, bcdefg12N6RestTheta1]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Strict load bands put the whole remainder below the face. -/
theorem bcdefg12N6Rest_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbL : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbBeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbDelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbZeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbTheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6Rest l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  have hb0 := bcdefg12N6RestLF0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb1 := bcdefg12N6RestLF1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb2 := bcdefg12N6RestLF2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb3 := bcdefg12N6RestLF3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb4 := bcdefg12N6RestL0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb5 := bcdefg12N6RestL1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb6 := bcdefg12N6RestL2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb7 := bcdefg12N6RestL3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb8 := bcdefg12N6RestL4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb9 := bcdefg12N6RestL5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb10 := bcdefg12N6RestL6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb11 := bcdefg12N6RestBeta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb12 := bcdefg12N6RestBeta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb13 := bcdefg12N6RestBeta2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb14 := bcdefg12N6RestBeta3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb15 := bcdefg12N6RestGamma0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb16 := bcdefg12N6RestGamma1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb17 := bcdefg12N6RestDelta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbDelta
  have hb18 := bcdefg12N6RestDelta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbDelta
  have hb19 := bcdefg12N6RestDelta2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbDelta
  have hb20 := bcdefg12N6RestEpsilon0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb21 := bcdefg12N6RestEpsilon1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb22 := bcdefg12N6RestZeta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbZeta
  have hb23 := bcdefg12N6RestZeta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbZeta
  have hb24 := bcdefg12N6RestEta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb25 := bcdefg12N6RestTheta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbTheta
  have hb26 := bcdefg12N6RestTheta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbTheta
  unfold bcdefg12N6Rest
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hb0 hb1) hb2) hb3) hb4) hb5) hb6) hb7) hb8) hb9) hb10) hb11) hb12) hb13) hb14) hb15) hb16) hb17) hb18) hb19) hb20) hb21) hb22) hb23) hb24) hb25) hb26)

end Max11DegreeRoutes
