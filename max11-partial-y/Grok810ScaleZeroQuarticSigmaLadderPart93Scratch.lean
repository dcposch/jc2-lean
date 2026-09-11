import Grok810ScaleZeroQuarticSigmaLadderPart48Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart49Scratch

/-! Part 93 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaBands810


theorem quarticSigma_l_band_disjunction
    {l : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaLoadTopL810 A B C D E F G → l = 0) :
    l = 0 ∨
      5 * A.natDegree ≤ 4 * B.natDegree ∨
      7 * A.natDegree ≤ 4 * C.natDegree ∨
      9 * A.natDegree ≤ 4 * D.natDegree ∨
      11 * A.natDegree ≤ 4 * E.natDegree ∨
      13 * A.natDegree ≤ 4 * F.natDegree ∨
      15 * A.natDegree ≤ 4 * G.natDegree := by
  by_cases hB : 4 * B.natDegree < 5 * A.natDegree
  · by_cases hC : 4 * C.natDegree < 7 * A.natDegree
    · by_cases hD : 4 * D.natDegree < 9 * A.natDegree
      · by_cases hE : 4 * E.natDegree < 11 * A.natDegree
        · by_cases hF : 4 * F.natDegree < 13 * A.natDegree
          · by_cases hG : 4 * G.natDegree < 15 * A.natDegree
            · exact Or.inl (hkill ⟨hA, Or.inr hB, Or.inr hC, Or.inr hD,
                Or.inr hE, Or.inr hF, Or.inr hG⟩)
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega


theorem quarticSigma_beta_band_disjunction
    {beta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaLoadTopBeta810 A B C D E F G → beta = 0) :
    beta = 0 ∨
      3 * A.natDegree ≤ 4 * B.natDegree ∨
      5 * A.natDegree ≤ 4 * C.natDegree ∨
      7 * A.natDegree ≤ 4 * D.natDegree ∨
      9 * A.natDegree ≤ 4 * E.natDegree ∨
      11 * A.natDegree ≤ 4 * F.natDegree ∨
      13 * A.natDegree ≤ 4 * G.natDegree := by
  by_cases hB : 4 * B.natDegree < 3 * A.natDegree
  · by_cases hC : 4 * C.natDegree < 5 * A.natDegree
    · by_cases hD : 4 * D.natDegree < 7 * A.natDegree
      · by_cases hE : 4 * E.natDegree < 9 * A.natDegree
        · by_cases hF : 4 * F.natDegree < 11 * A.natDegree
          · by_cases hG : 4 * G.natDegree < 13 * A.natDegree
            · exact Or.inl (hkill ⟨hA, Or.inr hB, Or.inr hC, Or.inr hD,
                Or.inr hE, Or.inr hF, Or.inr hG⟩)
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega


end QuarticSigmaBands810
end Max11DegreeRoutes
end
