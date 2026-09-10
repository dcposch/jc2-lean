import Grok810ScaleZeroQuarticSigmaLadderPart48Scratch

/-! Part 49 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


/-- κ kills `beta` when `2s > 3 a`, expanded per letter. -/
def QuarticKappaLoadTopBeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    (B = 0 ∨ 4 * B.natDegree < 3 * A.natDegree) ∧
    (C = 0 ∨ 4 * C.natDegree < 5 * A.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < 7 * A.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 9 * A.natDegree) ∧
    (F = 0 ∨ 4 * F.natDegree < 11 * A.natDegree) ∧
    (G = 0 ∨ 4 * G.natDegree < 13 * A.natDegree)


/-- κ kills `delta` when `2s > 5 a`, expanded per letter. -/
def QuarticKappaLoadTopDelta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    (B = 0 ∨ 4 * B.natDegree < A.natDegree) ∧
    (C = 0 ∨ 4 * C.natDegree < 3 * A.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < 5 * A.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 7 * A.natDegree) ∧
    (F = 0 ∨ 4 * F.natDegree < 9 * A.natDegree) ∧
    (G = 0 ∨ 4 * G.natDegree < 11 * A.natDegree)


end QuarticKappaLadder810
end Max11DegreeRoutes
end
