import Grok810ScaleZeroQuarticSigmaLadderPart25Scratch

/-! Part 26 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


def QuarticLoadSigmaConeBEFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree)


def QuarticLoadSigmaConeCDEF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (G = 0 ∨ G.natDegree < 2 * C.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
