import Grok810ScaleZeroQuarticSigmaLadderPart31Scratch

/-! Part 32 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBCDEFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree


/-! ### Mixed-monomial residual cones (holes in the 63-cone taxonomy) -/

/-- Residual chamber of the σ-defect taxonomy: `B` wins the
singleton-face race (`3σ_B ≤ k_Z σ_Z` for every live `Z`) yet the mixed
monomial `B·F` is strictly cheaper than `B³` (`σ_F < 2σ_B`), so the
cost minimum is the single monomial `BF`, which is not the face of any of
the 63 `QuarticSigmaSupportCone810` constructors.  See the emitter
`scripts/emit_810_quartic_sigma_exhaust.py`. -/
def QuarticMixedSigmaConeBF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    F ≠ 0 ∧
    A.natDegree + 4 * B.natDegree < 2 * F.natDegree ∧
    4 * F.natDegree ≤ 5 * A.natDegree + 6 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree ≤ A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree ≤ A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree ≤ 3 * A.natDegree + 6 * B.natDegree) ∧
    (G = 0 ∨ 4 * G.natDegree ≤ 7 * A.natDegree + 6 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
