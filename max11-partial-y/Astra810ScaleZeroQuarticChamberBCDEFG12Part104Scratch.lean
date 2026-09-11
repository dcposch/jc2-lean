import Grok810ScaleZeroQuarticSigmaLadderPart101Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part101Scratch
import Grok810ScaleZeroQuarticTowerSpeedTPart101Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part22Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part23Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part102Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part103Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part03Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part13Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part16Scratch

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
/-! # BCDEFG12 chamber, part 4

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
/-- The auxiliary kills l whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_l_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 11 * A.natDegree)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    l = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticBetaTowerFace810 beta A + n7QuarticDeltaTowerFace810 delta A + n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 8 * A.natDegree := by
    simp only [S, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticLTowerFace810 l A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    dsimp [S]
    abel
  have hlead : (n7QuarticLTowerFace810 l A).natDegree = 8 * A.natDegree := by
    simp only [n7QuarticLTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills beta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_beta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 9 * A.natDegree)
    (hl0 : l = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    beta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticDeltaTowerFace810 delta A + n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 7 * A.natDegree := by
    simp only [S, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticBetaTowerFace810 beta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, n7QuarticLTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticBetaTowerFace810 beta A).natDegree = 7 * A.natDegree := by
    simp only [n7QuarticBetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills delta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_delta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 7 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    delta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 6 * A.natDegree := by
    simp only [S, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticDeltaTowerFace810 delta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticDeltaTowerFace810 delta A).natDegree = 6 * A.natDegree := by
    simp only [n7QuarticDeltaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills zeta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_zeta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 5 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    zeta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inl hdelta0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 5 * A.natDegree := by
    simp only [S, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticZetaTowerFace810 zeta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, hdelta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticZetaTowerFace810 zeta A).natDegree = 5 * A.natDegree := by
    simp only [n7QuarticZetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills theta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_theta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 3 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (hzeta0 : zeta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    theta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inl hdelta0
    · exact Or.inl hzeta0
    · exact Or.inr (by omega)
  have hrem := hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticThetaTowerFace810 theta A +
      (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, hdelta0, hzeta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
  have hlead : (n7QuarticThetaTowerFace810 theta A).natDegree = 4 * A.natDegree := by
    simp only [n7QuarticThetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 8

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
/-- Coefficient of the chamber face at its common monomial degree. -/
theorem bcdefg12Kappa_face_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12KappaFace810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (5 / 512 : k) * kappaQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A * B ^ 3).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm0 : (A * B ^ 3).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (B * C ^ 2).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm1 : (B * C ^ 2).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (B * G).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm2 : (B * G).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C * F).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm3 : (C * F).coeff (A.natDegree + 3 * B.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (D * E).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm4 : (D * E).coeff (A.natDegree + 3 * B.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12KappaFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, kappaQuarticOpenIIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar chamber face vanishes, using the full constant-integral hypothesis. -/
theorem bcdefg12KappaFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    kappaQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := bcdefg12Kappa_rest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta
  have ht := bcdefg12Kappa_face_coeff810 A B C D E F G hc
  have hd : 0 < A.natDegree + 3 * B.natDegree := by
    obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
    obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree by omega)
  rw [bcdefg12Kappa_split810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 11

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
/-- Coefficient of the chamber face at its common monomial degree. -/
theorem bcdefg12Mu_face_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12MuFace810 A B C D E F G).coeff (3 * C.natDegree) =
      (5 / 512 : k) * muQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A * B ^ 2 * C).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm0 : (A * B ^ 2 * C).coeff (3 * C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A * B * F).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm1 : (A * B * F).coeff (3 * C.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A * D ^ 2).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm2 : (A * D ^ 2).coeff (3 * C.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C ^ 3).natDegree = 3 * C.natDegree := by
    rw [natDegree_pow] <;> omega
  have hm3 : (C ^ 3).coeff (3 * C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (C * G).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hCne hGne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm4 : (C * G).coeff (3 * C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (E ^ 2).natDegree = 3 * C.natDegree := by
    rw [natDegree_pow] <;> omega
  have hm5 : (E ^ 2).coeff (3 * C.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12MuFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, hm5, muQuarticOpenIIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar chamber face vanishes, using the full constant-integral hypothesis. -/
theorem bcdefg12MuFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    muQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := bcdefg12Mu_rest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta
  have ht := bcdefg12Mu_face_coeff810 A B C D E F G hc
  have hd : 0 < 3 * C.natDegree := by
    obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
    obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree by omega)
  rw [bcdefg12Mu_split810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 14

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
/-- Coefficient of the chamber face at its common monomial degree. -/
theorem bcdefg12Xi_face_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12XiFace810 A B C D E F G).coeff (E.natDegree + G.natDegree) =
      (5 / 512 : k) * xiQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A * B ^ 2 * E).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm0 : (A * B ^ 2 * E).coeff (E.natDegree + G.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A * B * C * D).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm1 : (A * B * C * D).coeff (E.natDegree + G.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A * D * F).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm2 : (A * D * F).coeff (E.natDegree + G.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C ^ 2 * E).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm3 : (C ^ 2 * E).coeff (E.natDegree + G.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (E * G).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_mul hEne hGne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm4 : (E * G).coeff (E.natDegree + G.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12XiFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, xiQuarticOpenIIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar chamber face vanishes, using the full constant-integral hypothesis. -/
theorem bcdefg12XiFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    xiQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := bcdefg12Xi_rest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta
  have ht := bcdefg12Xi_face_coeff810 A B C D E F G hc
  have hd : 0 < E.natDegree + G.natDegree := by
    obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
    obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree by omega)
  rw [bcdefg12Xi_split810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 17

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
/-- Coefficient of the chamber face at its common monomial degree. -/
theorem bcdefg12Pi_face_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12PiFace810 A B C D E F G).coeff (2 * G.natDegree) =
      (5 / 4096 : k) * piQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A ^ 2 * B ^ 4).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm0 : (A ^ 2 * B ^ 4).coeff (2 * G.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A * B ^ 2 * C ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm1 : (A * B ^ 2 * C ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A * B ^ 2 * G).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm2 : (A * B ^ 2 * G).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (A * B * C * F).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm3 : (A * B * C * F).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (A * B * D * E).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm4 : (A * B * D * E).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (A * C * D ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne, natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm5 : (A * C * D ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd6 : (A * F ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm6 : (A * F ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd6, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd7 : (C ^ 4).natDegree = 2 * G.natDegree := by
    rw [natDegree_pow] <;> omega
  have hm7 : (C ^ 4).coeff (2 * G.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd7, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd8 : (C ^ 2 * G).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm8 : (C ^ 2 * G).coeff (2 * G.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd8, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd9 : (C * E ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm9 : (C * E ^ 2).coeff (2 * G.natDegree) = C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hd9, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd10 : (G ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_pow] <;> omega
  have hm10 : (G ^ 2).coeff (2 * G.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd10, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12PiFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, piQuarticOpenIIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar chamber face vanishes, using the full constant-integral hypothesis. -/
theorem bcdefg12PiFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    piQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := bcdefg12Pi_rest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta
  have ht := bcdefg12Pi_face_coeff810 A B C D E F G hc
  have hd : 0 < 2 * G.natDegree := by
    obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
    obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree by omega)
  rw [bcdefg12Pi_split810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 21

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
/-- Coefficient of the homogeneous polynomial face. -/
theorem bcdefg12N2Face_coeff
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2Face A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) =
      (5 / 512 : k) * n2QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  have hA : A ≠ 0 := by intro hz; simp [hz] at hApos
  have hd0 : (A * B ^ 2 * D).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hD, natDegree_mul hA (pow_ne_zero 2 hB)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf0 : (A * B ^ 2 * D).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (B * C * E).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hB hC) hE, natDegree_mul hB hC] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf1 : (B * C * E).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 2 * D).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hC) hD] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf2 : (C ^ 2 * D).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd2, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (D * G).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hD hG] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf3 : (D * G).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = D.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (E * F).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hE hF] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf4 : (E * F).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = E.leadingCoeff * F.leadingCoeff := by
    rw [← hd4, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12N2Face, n2QuarticOpenIIFace810, coeff_add, coeff_smul, smul_eq_mul, hcf0, hcf1, hcf2, hcf3, hcf4]
  ring

set_option maxHeartbeats 64000000 in
/-- Vanishing of the scalar N2 face under the strict load bands. -/
theorem bcdefg12N2Face_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbL : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbBeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbDelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbZeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbTheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    n2QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hrest := bcdefg12N2Rest_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL hbBeta hbDelta hbZeta hbTheta
  have hface := bcdefg12N2Face_coeff A B C D E F G hc
  have hApos := hc.1.1
  have hcarrier := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G hnu hkap
  have htop : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    have hApos := hcone.1
    omega
  have hz := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hcarrier htop)
  rw [bcdefg12N2_split, coeff_add, coeff_eq_zero_of_natDegree_lt hrest, add_zero, hface] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num : (5 / 512 : k) ≠ 0)

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 5

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
/-- Strict bands for all five pure-A loads throughout the maximal-tie chamber. -/
theorem quarticBCDEFG12_loadBands810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) ∧
    (beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) ∧
    (delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) ∧
    (zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree) ∧
    (theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) := by
  have haux := degreeZeroBandAuxBCDEFG12810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G
    hc hprim homi hnu hkap
  have hl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 11 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      exact quarticBCDEFG12_l_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) haux
  have hbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 9 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      exact quarticBCDEFG12_beta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 haux
  have hdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 7 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      have hbeta0 : beta = 0 := by
        rcases hbeta with hz | hh
        · exact hz
        · omega
      exact quarticBCDEFG12_delta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 hbeta0 haux
  have hzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 5 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      have hbeta0 : beta = 0 := by
        rcases hbeta with hz | hh
        · exact hz
        · omega
      have hdelta0 : delta = 0 := by
        rcases hdelta with hz | hh
        · exact hz
        · omega
      exact quarticBCDEFG12_zeta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 hbeta0 hdelta0 haux
  have htheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 3 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      have hbeta0 : beta = 0 := by
        rcases hbeta with hz | hh
        · exact hz
        · omega
      have hdelta0 : delta = 0 := by
        rcases hdelta with hz | hh
        · exact hz
        · omega
      have hzeta0 : zeta = 0 := by
        rcases hzeta with hz | hh
        · exact hz
        · omega
      exact quarticBCDEFG12_theta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 hbeta0 hdelta0 hzeta0 haux
  exact ⟨hl, hbeta, hdelta, hzeta, htheta⟩

end Max11DegreeRoutes
/-! # BCDEFG12 chamber, part 27

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
/-- Coefficient of the homogeneous polynomial face. -/
theorem bcdefg12N6Face_coeff
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6Face A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) =
      (5 / 12288 : k) * A.leadingCoeff * n6QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  have hA : A ≠ 0 := by intro hz; simp [hz] at hApos
  have hd0 : (A ^ 2 * B ^ 3 * C).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 3 hB)) hC, natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 3 hB)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf0 : (A ^ 2 * B ^ 3 * C).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A ^ 2 * B ^ 2 * F).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)) hF, natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf1 : (A ^ 2 * B ^ 2 * F).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A ^ 2 * B * D ^ 2).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) hB) (pow_ne_zero 2 hD), natDegree_mul (pow_ne_zero 2 hA) hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf2 : (A ^ 2 * B * D ^ 2).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (A * B * C ^ 3).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hB) (pow_ne_zero 3 hC), natDegree_mul hA hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf3 : (A * B * C ^ 3).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hd3, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (A * B * C * G).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hA hB) hC) hG, natDegree_mul (mul_ne_zero hA hB) hC, natDegree_mul hA hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf4 : (A * B * C * G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (A * B * E ^ 2).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hB) (pow_ne_zero 2 hE), natDegree_mul hA hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf5 : (A * B * E ^ 2).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd6 : (A * C * D * E).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hA hC) hD) hE, natDegree_mul (mul_ne_zero hA hC) hD, natDegree_mul hA hC] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf6 : (A * C * D * E).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd6, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd7 : (A * F * G).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hF) hG, natDegree_mul hA hF] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf7 : (A * F * G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * F.leadingCoeff * G.leadingCoeff := by
    rw [← hd7, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd8 : (A * C ^ 2 * F).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hC)) hF, natDegree_mul hA (pow_ne_zero 2 hC)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf8 : (A * C ^ 2 * F).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hd8, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12N6Face, n6QuarticOpenIIFace810, coeff_add, coeff_smul, smul_eq_mul, hcf0, hcf1, hcf2, hcf3, hcf4, hcf5, hcf6, hcf7, hcf8]
  ring

set_option maxHeartbeats 64000000 in
/-- Vanishing of the scalar N6 face under the strict load bands. -/
theorem bcdefg12N6Face_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbL : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbBeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbDelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbZeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbTheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    n6QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hrest := bcdefg12N6Rest_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL hbBeta hbDelta hbZeta hbTheta
  have hface := bcdefg12N6Face_coeff A B C D E F G hc
  have hApos := hc.1.1
  have hcarrier := degreeZeroN6TowerQuartic810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G hApos hprim homi hnu
  have htop : 2 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    have hApos := hcone.1
    omega
  have hz := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hcarrier htop)
  rw [bcdefg12N6_split, coeff_add, coeff_eq_zero_of_natDegree_lt hrest, add_zero, hface] at hz
  have hA : A ≠ 0 := by intro hz; simp [hz] at hApos
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (by norm_num : (5 / 12288 : k) ≠ 0) (leadingCoeff_ne_zero.mpr hA))

end Max11DegreeRoutes
