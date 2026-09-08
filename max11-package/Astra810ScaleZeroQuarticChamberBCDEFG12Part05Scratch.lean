import Astra810ScaleZeroQuarticChamberBCDEFG12Part04Scratch

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
