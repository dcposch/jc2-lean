import Grok810ScaleZeroQuarticSigmaLadderPart04Scratch

/-! Part 57 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2Kills810


/-- `N₂` kills `beta` on the k=3 cone `BC`: `7s ≥ 6 a`. -/
def QuarticN2LoadTopBeta_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 15 * A.natDegree


/-- `N₂` kills `delta` on the k=3 cone `BC`: `7s ≥ 10 a`. -/
def QuarticN2LoadTopDelta_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 11 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
