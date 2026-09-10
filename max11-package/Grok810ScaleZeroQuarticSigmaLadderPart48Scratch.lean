import Grok810ScaleZeroQuarticSigmaLadderPart47Scratch

/-! Part 48 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticKappaLadder810


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoL810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL810 l beta gamma delta epsilon zeta eta
        theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  have h1 :=
    degreeZeroKappaQuarticNoL1810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h2 :=
    degreeZeroKappaQuarticNoL2810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h3 :=
    degreeZeroKappaQuarticNoL3810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h4 :=
    degreeZeroKappaQuarticNoL4810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h12 := natDegree_add_lt810 h1 h2
  have h123 := natDegree_add_lt810 h12 h3
  have h1234 := natDegree_add_lt810 h123 h4
  simp only [degreeZeroKappaQuarticNoL810]
  exact h1234


/-- κ kills `l` when `2s > 1 a`, expanded per letter. -/
def QuarticKappaLoadTopL810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    (B = 0 ∨ 4 * B.natDegree < 5 * A.natDegree) ∧
    (C = 0 ∨ 4 * C.natDegree < 7 * A.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < 9 * A.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 11 * A.natDegree) ∧
    (F = 0 ∨ 4 * F.natDegree < 13 * A.natDegree) ∧
    (G = 0 ∨ 4 * G.natDegree < 15 * A.natDegree)


end QuarticKappaLadder810
end Max11DegreeRoutes
end
