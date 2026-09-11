import Grok810ScaleZeroQuarticDefsScratch

/-! Part 33 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaSupportCones810


/-- Residual chamber of the σ-defect taxonomy: `B` wins the
singleton-face race (`3σ_B ≤ k_Z σ_Z` for every live `Z`) yet the mixed
monomial `B·G` is strictly cheaper than `B³` (`σ_G < 2σ_B`), so the
cost minimum is the single monomial `BG`, which is not the face of any of
the 63 `QuarticSigmaSupportCone810` constructors.  See the emitter
`scripts/emit_810_quartic_sigma_exhaust.py`. -/
def QuarticMixedSigmaConeBG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * B.natDegree < G.natDegree ∧
    4 * G.natDegree ≤ 7 * A.natDegree + 6 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree ≤ A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree ≤ A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree ≤ 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 4 * F.natDegree ≤ 5 * A.natDegree + 6 * B.natDegree)


/-- Residual chamber of the σ-defect taxonomy: `C` wins the
singleton-face race (`3σ_C ≤ k_Z σ_Z` for every live `Z`) yet the mixed
monomial `C·F` is strictly cheaper than `C³` (`σ_F < 2σ_C`), so the
cost minimum is the single monomial `CF`, which is not the face of any of
the 63 `QuarticSigmaSupportCone810` constructors.  See the emitter
`scripts/emit_810_quartic_sigma_exhaust.py`. -/
def QuarticMixedSigmaConeCF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    F ≠ 0 ∧
    4 * C.natDegree < A.natDegree + 2 * F.natDegree ∧
    2 * F.natDegree ≤ A.natDegree + 3 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree ≤ 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree ≤ 3 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree ≤ 3 * C.natDegree) ∧
    (G = 0 ∨ 2 * G.natDegree ≤ 2 * A.natDegree + 3 * C.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
