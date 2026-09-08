import Grok610ScaleZeroCubicADominantPart18Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicN1_610

variable {k : Type*} [Field k] [CharZero k]

theorem degreeZeroN1Cubic610_natDegree_le
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree ≤
      A.natDegree := by
  rw [degreeZeroN1Cubic610_eq_mu_add_A_kappa]
  have h1 : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E).natDegree ≤ A.natDegree := by
    rw [hmu]
    exact Nat.zero_le _
  have h2 :
      ((1 / 6 : k) • (A * degreeZeroKappaCubic610 l alpha beta delta
            epsilon zeta eta theta A B C D E)).natDegree ≤
        A.natDegree := by
    refine (natDegree_smul_le610 _ _).trans ?_
    have hmul :
        (A * degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta
              theta A B C D E).natDegree ≤
          A.natDegree +
            (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta
                theta A B C D E).natDegree :=
      natDegree_mul_le
    rw [hkap, add_zero] at hmul
    exact hmul
  exact (natDegree_add_le _ _).trans (max_le h1 h2)

end CubicN1_610

end Max11DegreeRoutes
