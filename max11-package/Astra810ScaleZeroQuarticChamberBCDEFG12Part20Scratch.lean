import Grok810ScaleZeroQuarticSigmaLadderPart35Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part18Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part19Scratch

/-! # BCDEFG12 chamber, part 20

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
def bcdefg12N2Rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12N2RestLF0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestL0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestL1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestL2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestBeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestBeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Exact expansion into face and remainder. -/
theorem bcdefg12N2_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12N2Face A B C D E F G + bcdefg12N2Rest l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN2Quartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, bcdefg12N2Face, bcdefg12N2Rest, bcdefg12N2RestLF0, bcdefg12N2RestL0, bcdefg12N2RestL1, bcdefg12N2RestL2, bcdefg12N2RestBeta0, bcdefg12N2RestBeta1, bcdefg12N2RestGamma0, bcdefg12N2RestDelta0, bcdefg12N2RestDelta1, bcdefg12N2RestEpsilon0, bcdefg12N2RestZeta0, bcdefg12N2RestEta0, bcdefg12N2RestTheta0]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Strict load bands put the whole remainder below the face. -/
theorem bcdefg12N2Rest_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbL : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbBeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbDelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbZeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbTheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2Rest l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  have hb0 := bcdefg12N2RestLF0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb1 := bcdefg12N2RestL0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb2 := bcdefg12N2RestL1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb3 := bcdefg12N2RestL2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb4 := bcdefg12N2RestBeta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb5 := bcdefg12N2RestBeta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb6 := bcdefg12N2RestGamma0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb7 := bcdefg12N2RestDelta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbDelta
  have hb8 := bcdefg12N2RestDelta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbDelta
  have hb9 := bcdefg12N2RestEpsilon0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb10 := bcdefg12N2RestZeta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbZeta
  have hb11 := bcdefg12N2RestEta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb12 := bcdefg12N2RestTheta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbTheta
  unfold bcdefg12N2Rest
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hb0 hb1) hb2) hb3) hb4) hb5) hb6) hb7) hb8) hb9) hb10) hb11) hb12)

end Max11DegreeRoutes
