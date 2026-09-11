import Grok810ScaleZeroQuarticDefsScratch

/-! Part 35 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

section QuarticN2_810


/-- `ν + (1/8)·A·κ` : weight 13, level-2 face `(5/16)(DG+EF)`, zero on `S ⊆ {B,C}`. -/
def degreeZeroN2Quartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G +
    (1 / 8 : k) • (A * degreeZeroKappaQuartic810 l beta gamma delta
      epsilon zeta eta theta A B C D E F G)


theorem degreeZeroN2Quartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree ≤
      A.natDegree := by
  simp only [degreeZeroN2Quartic810]
  have h1 : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
        theta A B C D E F G).natDegree ≤ A.natDegree := by
    rw [hnu]
    exact Nat.zero_le _
  have h2 :
      ((1 / 8 : k) • (A * degreeZeroKappaQuartic810 l beta gamma delta
            epsilon zeta eta theta A B C D E F G)).natDegree ≤
        A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul :
        (A * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
              eta theta A B C D E F G).natDegree ≤
          A.natDegree +
            (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
                eta theta A B C D E F G).natDegree :=
      natDegree_mul_le
    rw [hkap, add_zero] at hmul
    exact hmul
  exact (natDegree_add_le _ _).trans (max_le h1 h2)


end QuarticN2_810
end Max11DegreeRoutes
end
