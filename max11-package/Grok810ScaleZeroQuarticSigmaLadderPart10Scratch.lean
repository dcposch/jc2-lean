import Grok810ScaleZeroQuarticSigmaLadderPart09Scratch

/-! Part 10 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


def QuarticLoadSigmaConeEF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 2 * E.natDegree ∧
    (B = 0 ∨ 3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < 2 * E.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 2 * E.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + E.natDegree)


def QuarticLoadSigmaConeEG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    E ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + E.natDegree ∧
    (B = 0 ∨ 3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < 2 * E.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 2 * E.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 2 * E.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
