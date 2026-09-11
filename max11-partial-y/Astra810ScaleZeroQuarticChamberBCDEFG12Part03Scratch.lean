import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part101Scratch

/-! # BCDEFG12 chamber, part 3

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
/-- Every non-pure auxiliary monomial is strictly below the candidate pure load degree, including equality at the old tower face. -/
theorem bandAuxBCDEFG12Rest810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hd : 5 * A.natDegree + 8 * B.natDegree ≤ 2 * d)
    (hl : l = 0 ∨ 8 * A.natDegree ≤ d)
    (hbeta : beta = 0 ∨ 7 * A.natDegree ≤ d)
    (hdelta : delta = 0 ∨ 6 * A.natDegree ≤ d)
    (hzeta : zeta = 0 ∨ 5 * A.natDegree ≤ d)
    (htheta : theta = 0 ∨ 4 * A.natDegree ≤ d)
    : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  simp only [QuarticChamberBCDEFG12810, QuarticRatioConeA810] at hc
  rcases hc with ⟨⟨ha, hab, hac, had, hae, haf, hag⟩, hB, hC, hD, hE, hF, hG,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22⟩
  have hc0 : (bandAuxBCDEFG12RestFree1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestFree1810]
    compute_degree
    omega
  have hc1 : (bandAuxBCDEFG12RestFree2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestFree2810]
    compute_degree
    omega
  have hc2 : (bandAuxBCDEFG12RestFree3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestFree3810]
    compute_degree
    omega
  have hc3 : (bandAuxBCDEFG12RestL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL1810]
      compute_degree
      omega
  have hc4 : (bandAuxBCDEFG12RestL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL2810]
      compute_degree
      omega
  have hc5 : (bandAuxBCDEFG12RestL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL3810]
      compute_degree
      omega
  have hc6 : (bandAuxBCDEFG12RestL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL4810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL4810]
      compute_degree
      omega
  have hc7 : (bandAuxBCDEFG12RestL5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL5810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL5810]
      compute_degree
      omega
  have hc8 : (bandAuxBCDEFG12RestL6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL6810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL6810]
      compute_degree
      omega
  have hc9 : (bandAuxBCDEFG12RestBeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestBeta1810]
      compute_degree
      omega
  have hc10 : (bandAuxBCDEFG12RestBeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestBeta2810]
      compute_degree
      omega
  have hc11 : (bandAuxBCDEFG12RestBeta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestBeta3810]
      compute_degree
      omega
  have hc12 : (bandAuxBCDEFG12RestBeta4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta4810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestBeta4810]
      compute_degree
      omega
  have hc13 : (bandAuxBCDEFG12RestGamma1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestGamma1810]
    compute_degree
    omega
  have hc14 : (bandAuxBCDEFG12RestDelta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    · simp only [bandAuxBCDEFG12RestDelta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestDelta1810]
      compute_degree
      omega
  have hc15 : (bandAuxBCDEFG12RestDelta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    · simp only [bandAuxBCDEFG12RestDelta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestDelta2810]
      compute_degree
      omega
  have hc16 : (bandAuxBCDEFG12RestDelta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    · simp only [bandAuxBCDEFG12RestDelta3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestDelta3810]
      compute_degree
      omega
  have hc17 : (bandAuxBCDEFG12RestEpsilon1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestEpsilon1810]
    compute_degree
    omega
  have hc18 : (bandAuxBCDEFG12RestZeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hzeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestZeta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestZeta1810]
      compute_degree
      omega
  have hc19 : (bandAuxBCDEFG12RestZeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hzeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestZeta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestZeta2810]
      compute_degree
      omega
  have hc20 : (bandAuxBCDEFG12RestEta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestEta1810]
    compute_degree
    omega
  have hc21 : (bandAuxBCDEFG12RestTheta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases htheta with hz | hdload
    · simp only [bandAuxBCDEFG12RestTheta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestTheta1810]
      compute_degree
      omega
  simp only [bandAuxBCDEFG12Rest810]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc0 hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9) hc10) hc11) hc12) hc13) hc14) hc15) hc16) hc17) hc18) hc19) hc20) hc21)

end Max11DegreeRoutes
