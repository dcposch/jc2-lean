import Grok810ScaleZeroQuarticSigmaLadderPart55Scratch

/-! Part 56 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


/-- `N₂` kills `theta` on the k=3 cone `C`: `7s ≥ 18 a`. -/
def QuarticN2LoadTopTheta_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ 7 * C.natDegree ≤ 5 * A.natDegree


/-- `N₂` kills `l` on the k=3 cone `BC`: `7s ≥ 2 a`. -/
def QuarticN2LoadTopL_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 19 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
