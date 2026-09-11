import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part101Scratch

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
    simp only [bcdefg12PiRest0810]
    compute_degree
    omega
  have hr1 : (bcdefg12PiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest1810]
    compute_degree
    omega
  have hr2 : (bcdefg12PiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12PiRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest2810]
      compute_degree
      omega
  have hr3 : (bcdefg12PiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12PiRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest3810]
      compute_degree
      omega
  have hr4 : (bcdefg12PiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12PiRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest4810]
      compute_degree
      omega
  have hr5 : (bcdefg12PiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12PiRest5810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest5810]
      compute_degree
      omega
  have hr6 : (bcdefg12PiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12PiRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest6810]
      compute_degree
      omega
  have hr7 : (bcdefg12PiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12PiRest7810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest7810]
      compute_degree
      omega
  have hr8 : (bcdefg12PiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12PiRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest8810]
      compute_degree
      omega
  have hr9 : (bcdefg12PiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12PiRest9810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest9810]
      compute_degree
      omega
  have hr10 : (bcdefg12PiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest10810]
    compute_degree
    omega
  have hr11 : (bcdefg12PiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest11810]
    compute_degree
    omega
  have hr12 : (bcdefg12PiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbdelta with hz | hb
    · simp only [bcdefg12PiRest12810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest12810]
      compute_degree
      omega
  have hr13 : (bcdefg12PiRest13810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbdelta with hz | hb
    · simp only [bcdefg12PiRest13810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest13810]
      compute_degree
      omega
  have hr14 : (bcdefg12PiRest14810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest14810]
    compute_degree
    omega
  have hr15 : (bcdefg12PiRest15810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbzeta with hz | hb
    · simp only [bcdefg12PiRest15810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest15810]
      compute_degree
      omega
  have hr16 : (bcdefg12PiRest16810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest16810]
    compute_degree
    omega
  have hr17 : (bcdefg12PiRest17810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbtheta with hz | hb
    · simp only [bcdefg12PiRest17810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest17810]
      compute_degree
      omega
  unfold bcdefg12PiRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10) hr11) hr12) hr13) hr14) hr15) hr16) hr17)

end Max11DegreeRoutes
