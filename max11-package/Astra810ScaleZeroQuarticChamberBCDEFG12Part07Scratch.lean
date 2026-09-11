import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part06Scratch

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
    simp only [bcdefg12KappaRest0810]
    compute_degree
    omega
  have hr1 : (bcdefg12KappaRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12KappaRest1810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest1810]
      compute_degree
      omega
  have hr2 : (bcdefg12KappaRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12KappaRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest2810]
      compute_degree
      omega
  have hr3 : (bcdefg12KappaRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12KappaRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest3810]
      compute_degree
      omega
  have hr4 : (bcdefg12KappaRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12KappaRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest4810]
      compute_degree
      omega
  have hr5 : (bcdefg12KappaRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    simp only [bcdefg12KappaRest5810]
    compute_degree
    omega
  have hr6 : (bcdefg12KappaRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbdelta with hz | hb
    · simp only [bcdefg12KappaRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest6810]
      compute_degree
      omega
  have hr7 : (bcdefg12KappaRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    simp only [bcdefg12KappaRest7810]
    compute_degree
    omega
  have hr8 : (bcdefg12KappaRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbzeta with hz | hb
    · simp only [bcdefg12KappaRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest8810]
      compute_degree
      omega
  have hr9 : (bcdefg12KappaRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    simp only [bcdefg12KappaRest9810]
    compute_degree
    omega
  have hr10 : (bcdefg12KappaRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbtheta with hz | hb
    · simp only [bcdefg12KappaRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest10810]
      compute_degree
      omega
  unfold bcdefg12KappaRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10)

end Max11DegreeRoutes
