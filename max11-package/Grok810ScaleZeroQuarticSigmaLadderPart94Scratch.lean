import Grok810ScaleZeroQuarticSigmaLadderPart49Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart50Scratch

/-! Part 94 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


theorem quarticSigma_delta_band_disjunction
    {delta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaLoadTopDelta810 A B C D E F G → delta = 0) :
    delta = 0 ∨
      A.natDegree ≤ 4 * B.natDegree ∨
      3 * A.natDegree ≤ 4 * C.natDegree ∨
      5 * A.natDegree ≤ 4 * D.natDegree ∨
      7 * A.natDegree ≤ 4 * E.natDegree ∨
      9 * A.natDegree ≤ 4 * F.natDegree ∨
      11 * A.natDegree ≤ 4 * G.natDegree := by
  by_cases hB : 4 * B.natDegree < A.natDegree
  · by_cases hC : 4 * C.natDegree < 3 * A.natDegree
    · by_cases hD : 4 * D.natDegree < 5 * A.natDegree
      · by_cases hE : 4 * E.natDegree < 7 * A.natDegree
        · by_cases hF : 4 * F.natDegree < 9 * A.natDegree
          · by_cases hG : 4 * G.natDegree < 11 * A.natDegree
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


theorem quarticSigma_zeta_band_disjunction
    {zeta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaLoadTopZeta810 A B C D E F G → zeta = 0) :
    zeta = 0 ∨
      A.natDegree + 4 * B.natDegree ≥ 0 ∨
      A.natDegree ≤ 4 * C.natDegree ∨
      3 * A.natDegree ≤ 4 * D.natDegree ∨
      5 * A.natDegree ≤ 4 * E.natDegree ∨
      7 * A.natDegree ≤ 4 * F.natDegree ∨
      9 * A.natDegree ≤ 4 * G.natDegree := by
  by_cases hB : B = 0
  · by_cases hC : 4 * C.natDegree < A.natDegree
    · by_cases hD : 4 * D.natDegree < 3 * A.natDegree
      · by_cases hE : 4 * E.natDegree < 5 * A.natDegree
        · by_cases hF : 4 * F.natDegree < 7 * A.natDegree
          · by_cases hG : 4 * G.natDegree < 9 * A.natDegree
            · exact Or.inl (hkill ⟨hA, hB, Or.inr hC, Or.inr hD, Or.inr hE,
                Or.inr hF, Or.inr hG⟩)
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
    exact Nat.zero_le _


end QuarticSigmaBands810
end Max11DegreeRoutes
end
