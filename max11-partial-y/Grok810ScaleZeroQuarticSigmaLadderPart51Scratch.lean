import Grok810ScaleZeroQuarticSigmaLadderPart01Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart50Scratch

/-! Part 51 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


theorem quarticSigma_l_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticKappaLoadTopL810 A B C D E F G)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree = 0) :
    l = 0 := by
  by_contra hl
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG, hBt, hCt, hDt, hEt, hFt, hGt⟩ :=
    quarticKappaLoadTopL810_bounds htop
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (63 / 262144 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead : (kappaQuarticLFace810 l A).natDegree = 5 * A.natDegree := by
    simp only [kappaQuarticLFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroKappaQuarticNoL810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  rw [degreeZeroKappaQuartic810_eq_l_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hkap
  omega


/-- `N₂` kills `l` on the k=3 cone `B`: `7s ≥ 2 a`. -/
def QuarticN2LoadTopL_B810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeB810' A B C D E F G ∧ 14 * B.natDegree ≤ 19 * A.natDegree


end QuarticKappaLadder810
end Max11DegreeRoutes
end
