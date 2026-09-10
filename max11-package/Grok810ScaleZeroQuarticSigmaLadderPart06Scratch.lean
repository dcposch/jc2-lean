import Grok810ScaleZeroQuarticSigmaLadderPart05Scratch

/-! Part 6 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


def QuarticLoadSigmaConeBG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree)


def QuarticLoadSigmaConeCD810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 4 * C.natDegree) ∧
    (G = 0 ∨ G.natDegree < 2 * C.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
