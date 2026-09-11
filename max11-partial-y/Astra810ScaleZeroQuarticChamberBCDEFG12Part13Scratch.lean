import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part12Scratch

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
    simp only [bcdefg12XiRest0810]
    compute_degree
    omega
  have hr1 : (bcdefg12XiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    simp only [bcdefg12XiRest1810]
    compute_degree
    omega
  have hr2 : (bcdefg12XiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12XiRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest2810]
      compute_degree
      omega
  have hr3 : (bcdefg12XiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12XiRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest3810]
      compute_degree
      omega
  have hr4 : (bcdefg12XiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12XiRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest4810]
      compute_degree
      omega
  have hr5 : (bcdefg12XiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12XiRest5810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest5810]
      compute_degree
      omega
  have hr6 : (bcdefg12XiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12XiRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest6810]
      compute_degree
      omega
  have hr7 : (bcdefg12XiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    simp only [bcdefg12XiRest7810]
    compute_degree
    omega
  have hr8 : (bcdefg12XiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbdelta with hz | hb
    · simp only [bcdefg12XiRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest8810]
      compute_degree
      omega
  have hr9 : (bcdefg12XiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    simp only [bcdefg12XiRest9810]
    compute_degree
    omega
  have hr10 : (bcdefg12XiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbzeta with hz | hb
    · simp only [bcdefg12XiRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest10810]
      compute_degree
      omega
  have hr11 : (bcdefg12XiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    simp only [bcdefg12XiRest11810]
    compute_degree
    omega
  have hr12 : (bcdefg12XiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbtheta with hz | hb
    · simp only [bcdefg12XiRest12810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest12810]
      compute_degree
      omega
  unfold bcdefg12XiRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10) hr11) hr12)

end Max11DegreeRoutes
