import Grok810ScaleZeroQuarticDefsScratch
import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch
import Grok810ScaleZeroQuarticADominantScratch

/-! Part 1 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticSigmaConeB810' (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticSigmaConeC810' (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 4 * C.natDegree) ∧
    (G = 0 ∨ G.natDegree < 2 * C.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 2 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeD810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D ≠ 0 ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (F = 0 ∨ F.natDegree < A.natDegree + D.natDegree) ∧
    (G = 0 ∨ 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeE810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    E ≠ 0 ∧
    (B = 0 ∨ 3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < 2 * E.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 2 * E.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 2 * E.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + E.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 3 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    F ≠ 0 ∧
    (B = 0 ∨ A.natDegree + 4 * B.natDegree < 2 * F.natDegree) ∧
    (C = 0 ∨ 4 * C.natDegree < A.natDegree + 2 * F.natDegree) ∧
    (D = 0 ∨ A.natDegree + D.natDegree < F.natDegree) ∧
    (E = 0 ∨ A.natDegree + 2 * E.natDegree < 2 * F.natDegree) ∧
    (G = 0 ∨ 2 * G.natDegree < A.natDegree + 2 * F.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    G ≠ 0 ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < G.natDegree) ∧
    (C = 0 ∨ 2 * C.natDegree < G.natDegree) ∧
    (D = 0 ∨ 3 * A.natDegree + 2 * D.natDegree < 2 * G.natDegree) ∧
    (E = 0 ∨ A.natDegree + E.natDegree < G.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 2 * G.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 4 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticSigmaConeBC810' (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBD810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    D ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 5 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBE810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    E ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    F ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
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


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree)


set_option maxHeartbeats 64000000 in
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
/-! Part 7 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeCE810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    E ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 4 * C.natDegree) ∧
    (G = 0 ∨ G.natDegree < 2 * C.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeCF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    F ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree) ∧
    (G = 0 ∨ G.natDegree < 2 * C.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 8 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeCG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 4 * C.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeDE810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    2 * E.natDegree = A.natDegree + 2 * D.natDegree ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (F = 0 ∨ F.natDegree < A.natDegree + D.natDegree) ∧
    (G = 0 ∨ 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 9 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeDF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D ≠ 0 ∧
    F ≠ 0 ∧
    F.natDegree = A.natDegree + D.natDegree ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (G = 0 ∨ 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeDG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (F = 0 ∨ F.natDegree < A.natDegree + D.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
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


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeEF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 2 * E.natDegree ∧
    (B = 0 ∨ 3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < 2 * E.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 2 * E.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + E.natDegree)


set_option maxHeartbeats 64000000 in
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
/-! Part 11 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree = A.natDegree + 2 * F.natDegree ∧
    (B = 0 ∨ A.natDegree + 4 * B.natDegree < 2 * F.natDegree) ∧
    (C = 0 ∨ 4 * C.natDegree < A.natDegree + 2 * F.natDegree) ∧
    (D = 0 ∨ A.natDegree + D.natDegree < F.natDegree) ∧
    (E = 0 ∨ A.natDegree + 2 * E.natDegree < 2 * F.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBCD810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 12 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBCE810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    E ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBCF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    F ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 13 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBCG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBDE810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 14 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBDF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    D ≠ 0 ∧
    F ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBDG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    D ≠ 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 15 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBEF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBEG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    E ≠ 0 ∧
    G ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 16 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeCDE810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 4 * C.natDegree) ∧
    (G = 0 ∨ G.natDegree < 2 * C.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 17 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeCDF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    F ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree) ∧
    (G = 0 ∨ G.natDegree < 2 * C.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeCDG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 4 * C.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 18 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeCEF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree) ∧
    (G = 0 ∨ G.natDegree < 2 * C.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeCEG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    E ≠ 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 4 * C.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 19 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeCFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeDEF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    2 * E.natDegree = A.natDegree + 2 * D.natDegree ∧
    F.natDegree = A.natDegree + D.natDegree ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (G = 0 ∨ 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 20 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeDEG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = A.natDegree + 2 * D.natDegree ∧
    2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (F = 0 ∨ F.natDegree < A.natDegree + D.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeDFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    F.natDegree = A.natDegree + D.natDegree ∧
    2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < A.natDegree + 2 * D.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 21 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeEFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * F.natDegree = A.natDegree + 2 * E.natDegree ∧
    G.natDegree = A.natDegree + E.natDegree ∧
    (B = 0 ∨ 3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < 2 * E.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 2 * E.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBCDE810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 22 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBCDF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    F ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBCDG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 23 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBCEF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBCEG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    E ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 24 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBCFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBDEF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 25 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBDEG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBDFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    D ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
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


set_option maxHeartbeats 64000000 in
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


set_option maxHeartbeats 64000000 in
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
/-! Part 27 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeCDEG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 4 * C.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeCDFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 28 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeCEFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeDEFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * E.natDegree = A.natDegree + 2 * D.natDegree ∧
    F.natDegree = A.natDegree + D.natDegree ∧
    2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 29 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBCDEF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBCDEG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 30 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBCDFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeBCEFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 31 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
def QuarticLoadSigmaConeBDEFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    4 * D.natDegree = A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree)


set_option maxHeartbeats 64000000 in
def QuarticLoadSigmaConeCDEFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * D.natDegree = 3 * C.natDegree ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    G.natDegree = 2 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree)


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
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

set_option maxHeartbeats 64000000 in
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


set_option maxHeartbeats 64000000 in
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


set_option maxHeartbeats 64000000 in
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
/-! Part 35 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2_810


set_option maxHeartbeats 64000000 in
/-- `ν + (1/8)·A·κ` : weight 13, level-2 face `(5/16)(DG+EF)`, zero on `S ⊆ {B,C}`. -/
def degreeZeroN2Quartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G +
    (1 / 8 : k) • (A * degreeZeroKappaQuartic810 l beta gamma delta
      epsilon zeta eta theta A B C D E F G)


set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree ≤
      A.natDegree := by
  simp only [degreeZeroN2Quartic810]
  have h1 : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
        theta A B C D E F G).natDegree ≤ A.natDegree := by
    rw [hnu]
    exact Nat.zero_le _
  have h2 :
      ((1 / 8 : k) • (A * degreeZeroKappaQuartic810 l beta gamma delta
            epsilon zeta eta theta A B C D E F G)).natDegree ≤
        A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul :
        (A * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
              eta theta A B C D E F G).natDegree ≤
          A.natDegree +
            (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
                eta theta A B C D E F G).natDegree :=
      natDegree_mul_le
    rw [hkap, add_zero] at hmul
    exact hmul
  exact (natDegree_add_le _ _).trans (max_le h1 h2)


end QuarticN2_810
end Max11DegreeRoutes
end
/-! Part 36 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2_810


set_option maxHeartbeats 64000000 in
def n2QuarticLFace810 (l : k) (A : k[X]) : k[X] :=
  (231 / 4194304 * l : k) • A ^ 6

set_option maxHeartbeats 64000000 in
def n2QuarticBetaFace810 (beta : k) (A : k[X]) : k[X] :=
  (63 / 262144 * beta : k) • A ^ 5

end QuarticN2_810
end Max11DegreeRoutes
end
/-! Part 37 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2_810


set_option maxHeartbeats 64000000 in
def n2QuarticDeltaFace810 (delta : k) (A : k[X]) : k[X] :=
  (35 / 32768 * delta : k) • A ^ 4

set_option maxHeartbeats 64000000 in
def n2QuarticZetaFace810 (zeta : k) (A : k[X]) : k[X] :=
  (5 / 1024 * zeta : k) • A ^ 3

end QuarticN2_810
end Max11DegreeRoutes
end
/-! Part 38 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2_810


set_option maxHeartbeats 64000000 in
def n2QuarticThetaFace810 (theta : k) (A : k[X]) : k[X] :=
  (3 / 128 * theta : k) • A ^ 2


set_option maxHeartbeats 64000000 in
def degreeZeroN2QuarticNoL1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)
  + (315 / 262144 * l : k) • (A ^ 4 * C)
  - (9 / 131072 * l : k) • (A ^ 3 * B ^ 2)
  + (45 / 8192 * l : k) • (A ^ 3 * E)
  - (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 8192 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (27 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 512 * l : k) • (A * B * F)
  + (9 / 512 * l : k) • (A * C * E)
  - (9 / 1024 * l : k) • (A * D ^ 2)


end QuarticN2_810
end Max11DegreeRoutes
end
/-! Part 39 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2_810


set_option maxHeartbeats 64000000 in
def degreeZeroN2QuarticNoL2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(63 / 1024 * l : k)) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2
  + (63 / 262144 * beta : k) • A ^ 5
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 512 * beta : k) • (A * B * D)
  - (7 / 1024 * beta : k) • (A * C ^ 2)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)
  + (7 / 64 * beta : k) • (A * G)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 16 * gamma : k) • (B * E)


set_option maxHeartbeats 64000000 in
def degreeZeroN2QuarticNoL3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (C * D)
  + (35 / 32768 * delta : k) • A ^ 4
  + (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (5 / 64 * delta : k) • (A * E)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (5 / 1024 * zeta : k) • A ^ 3
  + (3 / 64 * zeta : k) • (A * C)
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  + (1 / 4 * eta : k) • D
  + (3 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C


end QuarticN2_810
end Max11DegreeRoutes
end
/-! Part 41 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
def kappaQuarticLFace810 (l : k) (A : k[X]) : k[X] :=
  (63 / 262144 * l : k) • A ^ 5

set_option maxHeartbeats 64000000 in
def kappaQuarticBetaFace810 (beta : k) (A : k[X]) : k[X] :=
  (35 / 32768 * beta : k) • A ^ 4

end QuarticKappaLadder810
end Max11DegreeRoutes
end
/-! Part 42 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
def kappaQuarticDeltaFace810 (delta : k) (A : k[X]) : k[X] :=
  (5 / 1024 * delta : k) • A ^ 3

set_option maxHeartbeats 64000000 in
def kappaQuarticZetaFace810 (zeta : k) (A : k[X]) : k[X] :=
  (3 / 128 * zeta : k) • A ^ 2


end QuarticKappaLadder810
end Max11DegreeRoutes
end
/-! Part 43 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoL1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoL2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 512 * l : k)) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)


end QuarticKappaLadder810
end Max11DegreeRoutes
end
/-! Part 44 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoL3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (5 / 1024 * delta : k) • A ^ 3
  + (5 / 64 * delta : k) • (A * C)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoL4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 * delta : k)) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A


end QuarticKappaLadder810
end Max11DegreeRoutes
end
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


set_option maxHeartbeats 64000000 in
/-- κ kills `beta` when `2s > 3 a`, expanded per letter. -/
def QuarticKappaLoadTopBeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    (B = 0 ∨ 4 * B.natDegree < 3 * A.natDegree) ∧
    (C = 0 ∨ 4 * C.natDegree < 5 * A.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < 7 * A.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 9 * A.natDegree) ∧
    (F = 0 ∨ 4 * F.natDegree < 11 * A.natDegree) ∧
    (G = 0 ∨ 4 * G.natDegree < 13 * A.natDegree)


set_option maxHeartbeats 64000000 in
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
/-! Part 59 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaCorners810


set_option maxHeartbeats 64000000 in
theorem primitiveQuartic_of_lettersZero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta
        theta A 0 0 0 0 0 0 =
      (1575 / 268435456 * l : k) • A ^ 8 +
        (25 / 1048576 * beta : k) • A ^ 7 +
        (25 / 262144 * delta : k) • A ^ 6 +
        (3 / 8192 * zeta : k) • A ^ 5 +
        (5 / 4096 * theta : k) • A ^ 4 := by
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810,
    rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810,
    rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810]
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  simp only [hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    sub_zero, neg_zero, sub_self]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


set_option maxHeartbeats 64000000 in
theorem quarticADominant_allLettersZero_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B = 0) (hC : C = 0) (hD : D = 0)
    (hE : E = 0) (hF : F = 0) (hG : G = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hBn : B.natDegree = 0 := by simp [hB]
  have hCn : C.natDegree = 0 := by simp [hC]
  have hDn : D.natDegree = 0 := by simp [hD]
  have hEn : E.natDegree = 0 := by simp [hE]
  have hFn : F.natDegree = 0 := by simp [hF]
  have hGn : G.natDegree = 0 := by simp [hG]
  by_cases hl0 : l = 0
  · by_cases hb0 : beta = 0
    · by_cases hd0 : delta = 0
      · by_cases hz0 : zeta = 0
        · have hP := primitiveQuartic_of_lettersZero l beta gamma delta
            epsilon zeta eta theta A
          rw [hB, hC, hD, hE, hF, hG, hP] at hder
          by_cases ht0 : theta = 0
          · simp only [hl0, hb0, hd0, hz0, ht0, mul_zero, zero_smul,
              add_zero] at hder
            have : derivative (0 : k[X]) = Polynomial.C (j / t) := hder
            rw [derivative_zero] at this
            exact hjdiv (C_eq_zero.mp this.symm)
          · have hdeg :=
              natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t)
                hjdiv hder
            have hAne : A ≠ 0 := by
              intro h0
              have : A.natDegree = 0 := by simp [h0]
              omega
            have hc : (5 / 4096 * theta : k) ≠ 0 :=
              mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) ht0
            have hlead :
                ((5 / 4096 * theta : k) • A ^ 4).natDegree =
                  4 * A.natDegree := by
              rw [natDegree_smul _ hc, natDegree_pow]
            simp only [hl0, hb0, hd0, hz0, mul_zero, zero_smul,
              add_zero, zero_add] at hdeg
            rw [hlead] at hdeg
            omega
        · exact quarticADominant_constantLetters_impossible_of_zeta
            (j := j) (t := t) gamma epsilon zeta eta theta A B C D E F G
            hApos hBn hCn hDn hEn hFn hGn hz0 hjdiv
            (by simpa [hl0, hb0, hd0] using hder)
      · exact quarticADominant_constantLetters_impossible_of_delta
          (j := j) (t := t) gamma delta epsilon zeta eta theta A B C D E
          F G hApos hBn hCn hDn hEn hFn hGn hd0 hjdiv
          (by simpa [hl0, hb0] using hder)
    · exact quarticADominant_constantLetters_impossible_of_beta
        (j := j) (t := t) beta gamma delta epsilon zeta eta theta A B C D
        E F G hApos hBn hCn hDn hEn hFn hGn hb0 hjdiv
        (by simpa [hl0] using hder)
  · exact quarticADominant_constantLetters_impossible_of_l
      (j := j) (t := t) l beta gamma delta epsilon zeta eta theta A B C D
      E F G hApos hBn hCn hDn hEn hFn hGn hl0 hjdiv hder


end QuarticSigmaCorners810
end Max11DegreeRoutes
end
/-! Part 34 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
/-- Residual chamber of the σ-defect taxonomy: `C` wins the
singleton-face race (`3σ_C ≤ k_Z σ_Z` for every live `Z`) yet the mixed
monomial `C·G` is strictly cheaper than `C³` (`σ_G < 2σ_C`), so the
cost minimum is the single monomial `CG`, which is not the face of any of
the 63 `QuarticSigmaSupportCone810` constructors.  See the emitter
`scripts/emit_810_quartic_sigma_exhaust.py`. -/
def QuarticMixedSigmaConeCG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree < G.natDegree ∧
    2 * G.natDegree ≤ 2 * A.natDegree + 3 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree ≤ 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree ≤ 3 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree ≤ 3 * C.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree ≤ A.natDegree + 3 * C.natDegree)


set_option maxHeartbeats 64000000 in
inductive QuarticSigmaSupportCone810 (A B C D E F G : k[X]) : Prop
  | sigmaB : QuarticSigmaConeB810' A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaC : QuarticSigmaConeC810' A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaD : QuarticLoadSigmaConeD810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaE : QuarticLoadSigmaConeE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaF : QuarticLoadSigmaConeF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaG : QuarticLoadSigmaConeG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBC : QuarticSigmaConeBC810' A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBD : QuarticLoadSigmaConeBD810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBE : QuarticLoadSigmaConeBE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBF : QuarticLoadSigmaConeBF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBG : QuarticLoadSigmaConeBG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCD : QuarticLoadSigmaConeCD810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCE : QuarticLoadSigmaConeCE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCF : QuarticLoadSigmaConeCF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCG : QuarticLoadSigmaConeCG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDE : QuarticLoadSigmaConeDE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDF : QuarticLoadSigmaConeDF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDG : QuarticLoadSigmaConeDG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaEF : QuarticLoadSigmaConeEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaEG : QuarticLoadSigmaConeEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaFG : QuarticLoadSigmaConeFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCD : QuarticLoadSigmaConeBCD810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCE : QuarticLoadSigmaConeBCE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCF : QuarticLoadSigmaConeBCF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCG : QuarticLoadSigmaConeBCG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDE : QuarticLoadSigmaConeBDE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDF : QuarticLoadSigmaConeBDF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDG : QuarticLoadSigmaConeBDG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBEF : QuarticLoadSigmaConeBEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBEG : QuarticLoadSigmaConeBEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBFG : QuarticLoadSigmaConeBFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDE : QuarticLoadSigmaConeCDE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDF : QuarticLoadSigmaConeCDF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDG : QuarticLoadSigmaConeCDG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCEF : QuarticLoadSigmaConeCEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCEG : QuarticLoadSigmaConeCEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCFG : QuarticLoadSigmaConeCFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDEF : QuarticLoadSigmaConeDEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDEG : QuarticLoadSigmaConeDEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDFG : QuarticLoadSigmaConeDFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaEFG : QuarticLoadSigmaConeEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDE : QuarticLoadSigmaConeBCDE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDF : QuarticLoadSigmaConeBCDF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDG : QuarticLoadSigmaConeBCDG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCEF : QuarticLoadSigmaConeBCEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCEG : QuarticLoadSigmaConeBCEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCFG : QuarticLoadSigmaConeBCFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDEF : QuarticLoadSigmaConeBDEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDEG : QuarticLoadSigmaConeBDEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDFG : QuarticLoadSigmaConeBDFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBEFG : QuarticLoadSigmaConeBEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDEF : QuarticLoadSigmaConeCDEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDEG : QuarticLoadSigmaConeCDEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDFG : QuarticLoadSigmaConeCDFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCEFG : QuarticLoadSigmaConeCEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDEFG : QuarticLoadSigmaConeDEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDEF : QuarticLoadSigmaConeBCDEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDEG : QuarticLoadSigmaConeBCDEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDFG : QuarticLoadSigmaConeBCDFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCEFG : QuarticLoadSigmaConeBCEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDEFG : QuarticLoadSigmaConeBDEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDEFG : QuarticLoadSigmaConeCDEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDEFG : QuarticLoadSigmaConeBCDEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | mixedBF : QuarticMixedSigmaConeBF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | mixedBG : QuarticMixedSigmaConeBG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | mixedCF : QuarticMixedSigmaConeCF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | mixedCG : QuarticMixedSigmaConeCG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
/-! Part 40 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2_810


set_option maxHeartbeats 64000000 in
def degreeZeroN2QuarticNoL810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroN2QuarticNoL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroN2QuarticNoL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroN2QuarticNoL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G


set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_l_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      n2QuarticLFace810 l A +
        degreeZeroN2QuarticNoL810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G := by
  simp only [degreeZeroN2Quartic810, degreeZeroNuQuartic810,
    degreeZeroKappaQuartic810, n2QuarticLFace810,
    degreeZeroN2QuarticNoL810, degreeZeroN2QuarticNoL1810, degreeZeroN2QuarticNoL2810, degreeZeroN2QuarticNoL3810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


end QuarticN2_810
end Max11DegreeRoutes
end
/-! Part 45 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoL810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroKappaQuarticNoL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroKappaQuarticNoL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroKappaQuarticNoL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroKappaQuarticNoL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_l_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      kappaQuarticLFace810 l A +
        degreeZeroKappaQuarticNoL810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticLFace810,
    degreeZeroKappaQuarticNoL810, degreeZeroKappaQuarticNoL1810, degreeZeroKappaQuarticNoL2810, degreeZeroKappaQuarticNoL3810, degreeZeroKappaQuarticNoL4810]
  module


end QuarticKappaLadder810
end Max11DegreeRoutes
end
/-! Part 46 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoL1810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL1810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * A.natDegree := by
  have hreflection :
      degreeZeroKappaQuarticNoL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [(5 / 512 : k),
      -((15 / 128 : k)),
      -((15 / 128 : k)),
      (5 / 16 : k),
      (5 / 16 : k),
      (5 / 16 : k),
      (45 / 8192 * l : k),
      -((9 / 16384 * l : k)),
      (27 / 1024 * l : k)]
      [[1, 3, 0, 0, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 1],
      [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0],
      [3, 0, 1, 0, 0, 0, 0],
      [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0]] := by
    unfold Max11ReflectDeg.polyOf
    rw [List.sum_eq_foldl]
    dsimp only [List.zipWith, List.foldl]
    simp only [degreeZeroKappaQuarticNoL1810, Max11ReflectDeg.mono_cons,
      Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
      pow_zero, pow_one, mul_one, one_mul, zero_add, add_zero, mul_assoc,
      sub_eq_add_neg, neg_smul]
  rw [hreflection]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoL2810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL2810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * A.natDegree := by
  have hreflection :
      degreeZeroKappaQuarticNoL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [(-(9 / 512 * l : k)),
      (9 / 1024 * l : k),
      -((63 / 1024 * l : k)),
      (9 / 64 * l : k),
      (9 / 64 * l : k),
      (9 / 64 * l : k),
      (9 / 128 * l : k),
      (35 / 32768 * beta : k),
      (21 / 1024 * beta : k)]
      [[1, 1, 0, 1, 0, 0, 0],
      [1, 0, 2, 0, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1],
      [0, 1, 0, 0, 0, 1, 0],
      [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 0]] := by
    unfold Max11ReflectDeg.polyOf
    rw [List.sum_eq_foldl]
    dsimp only [List.zipWith, List.foldl]
    simp only [degreeZeroKappaQuarticNoL2810, Max11ReflectDeg.mono_cons,
      Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
      pow_zero, pow_one, mul_one, one_mul, zero_add, add_zero, mul_assoc,
      sub_eq_add_neg, neg_smul]
  rw [hreflection]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  repeat' apply And.intro
  all_goals omega


end QuarticKappaLadder810
end Max11DegreeRoutes
end
/-! Part 47 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_000
    {a e f g : ℕ}
    (h0 : 2 * f < a + 2 * e)
    (h1 : a + e < g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_001
    {a e f g : ℕ}
    (h0 : 2 * f = a + 2 * e)
    (h1 : a + e < g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_002
    {a e f g : ℕ}
    (h0 : a + 2 * e < 2 * f)
    (h1 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_003
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f < a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_004
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f = a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_005
    {a d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + d < f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_006
    {a d e g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_007
    {a d e g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_008
    {a d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_009
    {a d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_010
    {a d e f : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_011
    {a d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_012
    {a d e f g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_013
    {a d e f g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_014
    {a d e f g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_015
    {a c g : ℕ}
    (h0 : 2 * g < 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_016
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_017
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_018
    {a c g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_019
    {a c f : ℕ}
    (h0 : 2 * f < a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_020
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_021
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_022
    {a c f : ℕ}
    (h0 : a + 3 * c < 2 * f)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_023
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f < a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_024
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f = a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_025
    {a c f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 3 * c < 2 * f)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_026
    {c e : ℕ}
    (h0 : 2 * e < 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_027
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e < 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_028
    {c e : ℕ}
    (h0 : 2 * e = 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_029
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e = 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_030
    {a c e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_031
    {a c e f : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_032
    {a c e f : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_033
    {a c e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_034
    {a c e f g : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_035
    {a c e f g : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_036
    {a c e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_037
    {a c e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_038
    {a c d : ℕ}
    (h0 : a + 2 * d < 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_039
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d < 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_040
    {a c d : ℕ}
    (h0 : a + 2 * d = 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_041
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d = 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_042
    {a c d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : 3 * c < a + 2 * d)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_043
    {a c d f : ℕ}
    (h0 : a + 2 * d < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_044
    {a c d f : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_045
    {a c d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_046
    {a c d f g : ℕ}
    (h0 : a + 2 * d < 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_047
    {a c d f g : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_048
    {a c d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_049
    {a c d f g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_050
    {a c d e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_051
    {a c d e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_052
    {a c d e : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_053
    {a c d e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_054
    {a c d e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_055
    {a c d e g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_056
    {a c d e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_057
    {a c d e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_058
    {a c d e f : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_059
    {a c d e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_060
    {a c d e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_061
    {a c d e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_062
    {a c d e f g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_063
    {a b g : ℕ}
    (h0 : 4 * g < 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_064
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_065
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_066
    {a b g : ℕ}
    (h0 : 7 * a + 6 * b < 4 * g)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_067
    {a b f : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_068
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 4 * f = 5 * a + 6 * b)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_069
    {a b f : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_070
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_071
    {a b f g : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_072
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_073
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_074
    {a b f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_075
    {a b f g : ℕ}
    (h0 : 5 * a + 6 * b < 4 * f)
    (h1 : a + 2 * f < 2 * g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_076
    {a b e : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_077
    {a b e g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_078
    {a b e : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_079
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_080
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_081
    {a b e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_082
    {a b e f : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_083
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * f = 5 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_084
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_085
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_086
    {a b e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_087
    {a b e f g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_088
    {a b e f g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_089
    {a b e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_090
    {a b e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_091
    {a b d : ℕ}
    (h0 : 4 * d < a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_092
    {a b d g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_093
    {a b d : ℕ}
    (h0 : 4 * d = a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_094
    {a b d g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_095
    {a b d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_096
    {a b d f : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_097
    {a b d f : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_098
    {a b d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_099
    {a b d f g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_100
    {a b d f g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_101
    {a b d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_102
    {a b d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_103
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_104
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_105
    {a b d e : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_106
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_107
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_108
    {a b d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_109
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_110
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_111
    {a b d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 6 * b < 4 * d)
    (h3 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoL3810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL3810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * A.natDegree := by
  have hreflection :
      degreeZeroKappaQuarticNoL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [(7 / 1024 * beta : k),
      (7 / 64 * beta : k),
      -((7 / 64 * beta : k)),
      -((7 / 128 * beta : k)),
      (7 / 8 * beta : k),
      -((3 / 16 * gamma : k)),
      (3 / 4 * gamma : k),
      (5 / 1024 * delta : k),
      (5 / 64 * delta : k)]
      [[1, 2, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 0, 0]] := by
    unfold Max11ReflectDeg.polyOf
    rw [List.sum_eq_foldl]
    dsimp only [List.zipWith, List.foldl]
    simp only [degreeZeroKappaQuarticNoL3810, Max11ReflectDeg.mono_cons,
      Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
      pow_zero, pow_one, mul_one, one_mul, zero_add, add_zero, mul_assoc,
      sub_eq_add_neg, neg_smul]
  rw [hreflection]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoL4810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL4810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * A.natDegree := by
  have hreflection :
      degreeZeroKappaQuarticNoL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [(-(15 / 128 * delta : k)),
      (5 / 8 * delta : k),
      (1 / 2 * epsilon : k),
      (3 / 128 * zeta : k),
      (3 / 8 * zeta : k),
      (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [[0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0],
      [2, 0, 0, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 0]] := by
    unfold Max11ReflectDeg.polyOf
    rw [List.sum_eq_foldl]
    dsimp only [List.zipWith, List.foldl]
    simp only [degreeZeroKappaQuarticNoL4810, Max11ReflectDeg.mono_cons,
      Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
      pow_zero, pow_one, mul_one, one_mul, zero_add, add_zero, mul_assoc,
      sub_eq_add_neg, neg_smul]
  rw [hreflection]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  repeat' apply And.intro
  all_goals omega


end QuarticKappaLadder810
end Max11DegreeRoutes
end
/-! Part 52 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `beta` on the k=3 cone `B`: `7s ≥ 6 a`. -/
def QuarticN2LoadTopBeta_B810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeB810' A B C D E F G ∧ 14 * B.natDegree ≤ 15 * A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `delta` on the k=3 cone `B`: `7s ≥ 10 a`. -/
def QuarticN2LoadTopDelta_B810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeB810' A B C D E F G ∧ 14 * B.natDegree ≤ 11 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 53 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `zeta` on the k=3 cone `B`: `7s ≥ 14 a`. -/
def QuarticN2LoadTopZeta_B810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeB810' A B C D E F G ∧ 2 * B.natDegree ≤ A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `theta` on the k=3 cone `B`: `7s ≥ 18 a`. -/
def QuarticN2LoadTopTheta_B810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeB810' A B C D E F G ∧ 14 * B.natDegree ≤ 3 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 54 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `l` on the k=3 cone `C`: `7s ≥ 2 a`. -/
def QuarticN2LoadTopL_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ 7 * C.natDegree ≤ 13 * A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `beta` on the k=3 cone `C`: `7s ≥ 6 a`. -/
def QuarticN2LoadTopBeta_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ 7 * C.natDegree ≤ 11 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 55 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `delta` on the k=3 cone `C`: `7s ≥ 10 a`. -/
def QuarticN2LoadTopDelta_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ 7 * C.natDegree ≤ 9 * A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `zeta` on the k=3 cone `C`: `7s ≥ 14 a`. -/
def QuarticN2LoadTopZeta_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ C.natDegree ≤ A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
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


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `theta` on the k=3 cone `C`: `7s ≥ 18 a`. -/
def QuarticN2LoadTopTheta_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ 7 * C.natDegree ≤ 5 * A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `l` on the k=3 cone `BC`: `7s ≥ 2 a`. -/
def QuarticN2LoadTopL_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 19 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
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


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `beta` on the k=3 cone `BC`: `7s ≥ 6 a`. -/
def QuarticN2LoadTopBeta_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 15 * A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `delta` on the k=3 cone `BC`: `7s ≥ 10 a`. -/
def QuarticN2LoadTopDelta_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 11 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 58 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `zeta` on the k=3 cone `BC`: `7s ≥ 14 a`. -/
def QuarticN2LoadTopZeta_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 2 * B.natDegree ≤ A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `theta` on the k=3 cone `BC`: `7s ≥ 18 a`. -/
def QuarticN2LoadTopTheta_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 3 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 60 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticParityCorner810


set_option maxHeartbeats 64000000 in
theorem quarticParityCorner_BDF_zero_impossible {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hB : B = 0) (hD : D = 0) (hF : F = 0) (hl : l = 0)
    (hbeta : beta = 0) (hdelta : delta = 0) (hzeta : zeta = 0)
    (htheta : theta = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) : False := by
  subst hB; subst hD; subst hF; subst hl; subst hbeta; subst hdelta
  subst hzeta; subst htheta
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810,
    rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810,
    rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    sub_zero, neg_zero, sub_self, derivative_zero] at hder
  exact hjdiv (by simpa using (Polynomial.C_eq_zero.mp hder.symm))


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_allZero
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t))
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    False := by
  rcases hA with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  exact quarticADominant_allLettersZero_impossible (j := j) (t := t)
    l beta gamma delta epsilon zeta eta theta A B C D E F G
    hApos hBz hCz hDz hEz hFz hGz hjdiv hder


end QuarticParityCorner810
end Max11DegreeRoutes
end
/-! Part 48 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoL810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL810 l beta gamma delta epsilon zeta eta
        theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  have h1 :=
    degreeZeroKappaQuarticNoL1810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h2 :=
    degreeZeroKappaQuarticNoL2810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h3 :=
    degreeZeroKappaQuarticNoL3810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h4 :=
    degreeZeroKappaQuarticNoL4810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h12 := natDegree_add_lt810 h1 h2
  have h123 := natDegree_add_lt810 h12 h3
  have h1234 := natDegree_add_lt810 h123 h4
  simp only [degreeZeroKappaQuarticNoL810]
  exact h1234


set_option maxHeartbeats 64000000 in
/-- κ kills `l` when `2s > 1 a`, expanded per letter. -/
def QuarticKappaLoadTopL810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    (B = 0 ∨ 4 * B.natDegree < 5 * A.natDegree) ∧
    (C = 0 ∨ 4 * C.natDegree < 7 * A.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < 9 * A.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 11 * A.natDegree) ∧
    (F = 0 ∨ 4 * F.natDegree < 13 * A.natDegree) ∧
    (G = 0 ∨ 4 * G.natDegree < 15 * A.natDegree)


end QuarticKappaLadder810
end Max11DegreeRoutes
end
/-! Part 61 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_G
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
    Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_F
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
    Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 62 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_FG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
  · -- F strictly outranks G
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inl hEz, Or.inr hFGlt⟩
  · -- G ties F
    exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
      Or.inl hDz, Or.inl hEz⟩
  · -- G strictly outranks F
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_E
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
    Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 63 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_EG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
  · -- E strictly outranks G
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inl hFz, Or.inr hEGlt⟩
  · -- G ties E
    exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inl hCz,
      Or.inl hDz, Or.inl hFz⟩
  · -- G strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_EF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
  · -- E strictly outranks F
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inr hEFlt, Or.inl hGz⟩
  · -- F ties E
    exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inl hCz,
      Or.inl hDz, Or.inl hGz⟩
  · -- F strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 64 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_EFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
  · -- E strictly outranks F
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
        Or.inr hEFlt, Or.inr hEGlt⟩
    · -- G ties E
      exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inl hCz,
        Or.inl hDz, Or.inr hEFlt⟩
    · -- G strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
        Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
  · -- F ties E
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inl hCz,
        Or.inl hDz, Or.inr hEGlt⟩
    · -- G ties EF
      exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq, Or.inl hBz,
        Or.inl hCz, Or.inl hDz⟩
    · -- G strictly outranks EF
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
        Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
  · -- F strictly outranks E
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
    · -- F strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
        Or.inr hEFgt, Or.inr hFGlt⟩
    · -- G ties F
      exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
        Or.inl hDz, Or.inr hEFgt⟩
    · -- G strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_D
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inl hEz,
    Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 65 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_DG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
  · -- D strictly outranks G
    exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inl hEz,
      Or.inl hFz, Or.inr hDGlt⟩
  · -- G ties D
    exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inl hCz,
      Or.inl hEz, Or.inl hFz⟩
  · -- G strictly outranks D
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
      Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_DF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
  · -- D strictly outranks F
    exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inl hEz,
      Or.inr hDFlt, Or.inl hGz⟩
  · -- F ties D
    exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inl hCz,
      Or.inl hEz, Or.inl hGz⟩
  · -- F strictly outranks D
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
      Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 66 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_DFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
  · -- D strictly outranks F
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inl hEz,
        Or.inr hDFlt, Or.inr hDGlt⟩
    · -- G ties D
      exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inl hCz,
        Or.inl hEz, Or.inr hDFlt⟩
    · -- G strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
  · -- F ties D
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inl hCz,
        Or.inl hEz, Or.inr hDGlt⟩
    · -- G ties DF
      exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq, Or.inl hBz,
        Or.inl hCz, Or.inl hEz⟩
    · -- G strictly outranks DF
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
  · -- F strictly outranks D
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
    · -- F strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
        Or.inl hEz, Or.inr hFGlt⟩
    · -- G ties F
      exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDFgt, Or.inl hEz⟩
    · -- G strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt),
        Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_DE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
  · -- D strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inr hDElt,
      Or.inl hFz, Or.inl hGz⟩
  · -- E ties D
    exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inl hCz,
      Or.inl hFz, Or.inl hGz⟩
  · -- E strictly outranks D
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inr hDEgt,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 67 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_DEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
  · -- D strictly outranks E
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inr hDElt,
        Or.inl hFz, Or.inr hDGlt⟩
    · -- G ties D
      exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDElt, Or.inl hFz⟩
    · -- G strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
        Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inl hFz⟩
  · -- E ties D
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inl hCz,
        Or.inl hFz, Or.inr hDGlt⟩
    · -- G ties DE
      exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq, Or.inl hBz,
        Or.inl hCz, Or.inl hFz⟩
    · -- G strictly outranks DE
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
        Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inl hFz⟩
  · -- E strictly outranks D
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inr hDEgt,
        Or.inl hFz, Or.inr hEGlt⟩
    · -- G ties E
      exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDEgt, Or.inl hFz⟩
    · -- G strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt),
        Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_DEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
  · -- D strictly outranks E
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inr hDElt,
        Or.inr hDFlt, Or.inl hGz⟩
    · -- F ties D
      exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDElt, Or.inl hGz⟩
    · -- F strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
        Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt), Or.inl hGz⟩
  · -- E ties D
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDFlt, Or.inl hGz⟩
    · -- F ties DE
      exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq, Or.inl hBz,
        Or.inl hCz, Or.inl hGz⟩
    · -- F strictly outranks DE
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
        Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt), Or.inl hGz⟩
  · -- E strictly outranks D
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inr hDEgt,
        Or.inr hEFlt, Or.inl hGz⟩
    · -- F ties E
      exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDEgt, Or.inl hGz⟩
    · -- F strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt),
        Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 68 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_DEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
  · -- D strictly outranks E
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inr hDElt,
          Or.inr hDFlt, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDElt, Or.inr hDFlt⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
          Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
    · -- F ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDElt, Or.inr hDGlt⟩
      · -- G ties DF
        exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq, Or.inl hBz,
          Or.inl hCz, Or.inr hDElt⟩
      · -- G strictly outranks DF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
          Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
    · -- F strictly outranks D
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
          Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith102_012 hDElt hFGgt hDFgt), Or.inr hFGgt⟩
  · -- E ties D
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDFlt, Or.inr hDGlt⟩
      · -- G ties DE
        exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq, Or.inl hBz,
          Or.inl hCz, Or.inr hDFlt⟩
      · -- G strictly outranks DE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
          Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
    · -- F ties DE
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq, Or.inl hBz,
          Or.inl hCz, Or.inr hDGlt⟩
      · -- G ties DEF
        exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
          hDGeq, Or.inl hBz, Or.inl hCz⟩
      · -- G strictly outranks DEF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
          Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
    · -- F strictly outranks DE
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
          Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith102_013 hDEeq hFGgt hDFgt), Or.inr hFGgt⟩
  · -- E strictly outranks D
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inr hDEgt,
          Or.inr hEFlt, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDEgt, Or.inr hEFlt⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
    · -- F ties E
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDEgt, Or.inr hEGlt⟩
      · -- G ties EF
        exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq, Or.inl hBz,
          Or.inl hCz, Or.inr hDEgt⟩
      · -- G strictly outranks EF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
    · -- F strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_014 hDEgt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_C
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inl hEz,
    Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 69 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
  · -- C strictly outranks G
    rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
    · -- C³ beats the mixed monomial CG
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inl hEz,
        Or.inl hFz, Or.inr hmCGlt⟩
    · -- G ties C on the mixed monomial CG
      exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz, Or.inl hDz,
        Or.inl hEz, Or.inl hFz⟩
    · -- the mixed monomial CG strictly beats C³ : residual cone
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- G ties C
    exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq), Or.inl hBz,
      Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- G strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC), Or.inl hDz,
      Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
  · -- C strictly outranks F
    rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
    · -- C³ beats the mixed monomial CF
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inl hEz,
        Or.inr hmCFlt, Or.inl hGz⟩
    · -- F ties C on the mixed monomial CF
      exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz, Or.inl hDz,
        Or.inl hEz, Or.inl hGz⟩
    · -- the mixed monomial CF strictly beats C³ : residual cone
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- F ties C
    exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
      Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- F strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz,
      Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 70 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
  · -- C strictly outranks F
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inl hEz,
            Or.inr hmCFlt, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz, Or.inl hDz,
            Or.inl hEz, Or.inr hmCFlt⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
      · -- F ties C on the mixed monomial CF
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz, Or.inl hDz,
            Or.inl hEz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
            Or.inl hBz, Or.inl hDz, Or.inl hEz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
    · -- G ties C
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
    · -- G strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC), Or.inl hDz,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
  · -- F ties C
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
    · -- G ties CF
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
    · -- G strictly outranks CF
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC), Or.inl hDz,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
  · -- F strictly outranks C
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
    · -- F strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz,
        Or.inl hEz, Or.inr hFGlt⟩
    · -- G ties F
      exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
        Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz, Or.inl hEz⟩
    · -- G strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG), Or.inl hDz,
        Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
  · -- C strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inr hCElt,
      Or.inl hFz, Or.inl hGz⟩
  · -- E ties C
    exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inl hDz,
      Or.inl hFz, Or.inl hGz⟩
  · -- E strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt, Or.inl hDz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 71 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
  · -- C strictly outranks E
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inr hCElt,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz, Or.inl hDz,
          Or.inr hCElt, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
    · -- G ties C
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq), Or.inl hBz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
    · -- G strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC), Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inl hFz⟩
  · -- E ties C
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inl hDz,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq, Or.inl hBz,
          Or.inl hDz, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
    · -- G ties CE
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq), Or.inl hBz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
    · -- G strictly outranks CE
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC), Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inl hFz⟩
  · -- E strictly outranks C
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt, Or.inl hDz,
        Or.inl hFz, Or.inr hEGlt⟩
    · -- G ties E
      exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inr hCEgt,
        Or.inl hDz, Or.inl hFz⟩
    · -- G strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG), Or.inl hDz,
        Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
  · -- C strictly outranks E
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inr hCElt,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz, Or.inl hDz,
          Or.inr hCElt, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
    · -- F ties C
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
    · -- F strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inl hGz⟩
  · -- E ties C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inl hDz,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq, Or.inl hBz,
          Or.inl hDz, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
    · -- F ties CE
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
    · -- F strictly outranks CE
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inl hGz⟩
  · -- E strictly outranks C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt, Or.inl hDz,
        Or.inr hEFlt, Or.inl hGz⟩
    · -- F ties E
      exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inr hCEgt,
        Or.inl hDz, Or.inl hGz⟩
    · -- F strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC), Or.inl hDz,
        Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 72 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
  · -- C strictly outranks E
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz,
              Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz,
              Or.inl hDz, Or.inr hCElt, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz,
              Or.inl hDz, Or.inr hCElt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
              Or.inl hBz, Or.inl hDz, Or.inr hCElt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties C
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
    · -- F ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
    · -- F strictly outranks C
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_034 hCElt hFGgt hCFgt), Or.inr hFGgt⟩
  · -- E ties C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz,
              Or.inl hDz, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
              Or.inl hBz, Or.inl hDz, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
              Or.inl hBz, Or.inl hDz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCEFG ⟨hA, hCne, hEne, hFne, hGne, hCEeq, hmCFeq,
              hmCGeq, Or.inl hBz, Or.inl hDz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CE
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
    · -- F ties CE
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CEF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CEF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
    · -- F strictly outranks CE
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_035 hCEeq hFGgt hCFgt), Or.inr hFGgt⟩
  · -- E strictly outranks C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt, Or.inl hDz,
          Or.inr hEFlt, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inr hCEgt,
          Or.inl hDz, Or.inr hEFlt⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
          Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
    · -- F ties E
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inr hCEgt,
          Or.inl hDz, Or.inr hEGlt⟩
      · -- G ties EF
        exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq, Or.inl hBz,
          Or.inr hCEgt, Or.inl hDz⟩
      · -- G strictly outranks EF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
          Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
    · -- F strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC),
          Or.inl hDz, Or.inr hEFgt, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_036 hFGeq hCEgt hEFgt hAG), Or.inl hDz, Or.inr hEFgt⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_037 hCEgt hEFgt hFGgt hAG),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CD
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- D ties C
    exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- D strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 73 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt, Or.inl hEz,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz, Or.inr hCDlt,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inl hFz⟩
    · -- G ties C
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq), Or.inl hBz,
        Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
        Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inl hEz, Or.inl hFz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz, Or.inl hEz,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq, Or.inl hBz,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inl hFz⟩
    · -- G ties CD
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq), Or.inl hBz,
        Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks CD
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
        Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inl hEz, Or.inl hFz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inl hEz,
        Or.inl hFz, Or.inr hDGlt⟩
    · -- G ties D
      exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inr hCDgt,
        Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
        Or.inr hDGgt, Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt, Or.inl hEz,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz, Or.inr hCDlt,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inl hGz⟩
    · -- F ties C
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
        Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inl hEz, Or.inl hGz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz, Or.inl hEz,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq, Or.inl hBz,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inl hGz⟩
    · -- F ties CD
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks CD
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
        Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inl hEz, Or.inl hGz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inl hEz,
        Or.inr hDFlt, Or.inl hGz⟩
    · -- F ties D
      exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inr hCDgt,
        Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
        Or.inr hDFgt, Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 74 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt,
              Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz,
              Or.inr hCDlt, Or.inl hEz, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz,
              Or.inr hCDlt, Or.inl hEz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
              Or.inl hBz, Or.inr hCDlt, Or.inl hEz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties C
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
    · -- F ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
    · -- F strictly outranks C
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_046 hCDlt hFGgt hCFgt), Or.inl hEz, Or.inr hFGgt⟩
  · -- D ties C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz,
              Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
              Or.inl hBz, Or.inl hEz, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
              Or.inl hBz, Or.inl hEz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDFG ⟨hA, hCne, hDne, hFne, hGne, hCDeq, hmCFeq,
              hmCGeq, Or.inl hBz, Or.inl hEz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CD
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
    · -- F ties CD
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CDF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CDF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
    · -- F strictly outranks CD
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_047 hCDeq hFGgt hCFgt), Or.inl hEz, Or.inr hFGgt⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inl hEz,
          Or.inr hDFlt, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inr hCDgt,
          Or.inl hEz, Or.inr hDFlt⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
          Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
    · -- F ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inr hCDgt,
          Or.inl hEz, Or.inr hDGlt⟩
      · -- G ties DF
        exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq, Or.inl hBz,
          Or.inr hCDgt, Or.inl hEz⟩
      · -- G strictly outranks DF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
          Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
    · -- F strictly outranks D
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
          Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_048 hFGeq hCDgt hDFgt hAG), Or.inr hDFgt, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_049 hCDgt hFGgt hDFgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt, Or.inr hCElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties C
      exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inr hCDlt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
        Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inl hFz, Or.inl hGz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz, Or.inr hCElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties CD
      exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq, Or.inl hBz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks CD
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
        Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inl hFz, Or.inl hGz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inr hDElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties D
      exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inr hCDgt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt),
        Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 75 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt,
            Or.inr hCElt, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz,
            Or.inr hCDlt, Or.inr hCElt, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
      · -- G ties C
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inl hFz⟩
    · -- E ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz,
            Or.inr hCDlt, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
            Or.inl hBz, Or.inr hCDlt, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
      · -- G ties CE
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
      · -- G strictly outranks CE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inl hFz⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_053 hCEgt hCDlt hEGgt), Or.inr hEGgt, Or.inl hFz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz,
            Or.inr hCElt, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
            Or.inl hBz, Or.inr hCElt, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
      · -- G ties CD
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
      · -- G strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inl hFz⟩
    · -- E ties CD
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
            Or.inl hBz, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCDEG ⟨hA, hCne, hDne, hEne, hGne, hCDeq, hCEeq,
            hmCGeq, Or.inl hBz, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
      · -- G ties CDE
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
      · -- G strictly outranks CDE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inl hFz⟩
    · -- E strictly outranks CD
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_054 hCEgt hCDeq hEGgt), Or.inr hEGgt, Or.inl hFz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inr hDElt,
          Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inr hCDgt,
          Or.inr hDElt, Or.inl hFz⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
          Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inl hFz⟩
    · -- E ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inr hCDgt,
          Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties DE
        exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq, Or.inl hBz,
          Or.inr hCDgt, Or.inl hFz⟩
      · -- G strictly outranks DE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
          Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inl hFz⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt),
          Or.inr hDEgt, Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt), Or.inr hDEgt, Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_055 hCDgt hDEgt hEGgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt,
            Or.inr hCElt, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz,
            Or.inr hCDlt, Or.inr hCElt, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
      · -- F ties C
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
      · -- F strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inl hGz⟩
    · -- E ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz,
            Or.inr hCDlt, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
            Or.inl hBz, Or.inr hCDlt, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
      · -- F ties CE
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
      · -- F strictly outranks CE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inl hGz⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_056 hCEgt hCDlt hEFgt), Or.inr hEFgt, Or.inl hGz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz,
            Or.inr hCElt, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
            Or.inl hBz, Or.inr hCElt, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
      · -- F ties CD
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
      · -- F strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inl hGz⟩
    · -- E ties CD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
            Or.inl hBz, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCDEF ⟨hA, hCne, hDne, hEne, hFne, hCDeq, hCEeq,
            hmCFeq, Or.inl hBz, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
      · -- F ties CDE
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
      · -- F strictly outranks CDE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inl hGz⟩
    · -- E strictly outranks CD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_057 hCEgt hCDeq hEFgt), Or.inr hEFgt, Or.inl hGz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inr hDElt,
          Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties D
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inr hCDgt,
          Or.inr hDElt, Or.inl hGz⟩
      · -- F strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt), Or.inl hGz⟩
    · -- E ties D
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inr hCDgt,
          Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties DE
        exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq, Or.inl hBz,
          Or.inr hCDgt, Or.inl hGz⟩
      · -- F strictly outranks DE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt), Or.inl hGz⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt),
          Or.inr hDEgt, Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt), Or.inr hDEgt, Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_058 hCDgt hDEgt hEFgt hAE),
          Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 76 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt,
                Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz,
                Or.inr hCDlt, Or.inr hCElt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz,
                Or.inr hCDlt, Or.inr hCElt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
                Or.inl hBz, Or.inr hCDlt, Or.inr hCElt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties C
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
      · -- F ties C
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
      · -- F strictly outranks C
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_046 hCDlt hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith102_034 hCElt hFGgt hCFgt), Or.inr hFGgt⟩
    · -- E ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz,
                Or.inr hCDlt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
                Or.inl hBz, Or.inr hCDlt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
                Or.inl hBz, Or.inr hCDlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEFG ⟨hA, hCne, hEne, hFne, hGne, hCEeq,
                hmCFeq, hmCGeq, Or.inl hBz, Or.inr hCDlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CE
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
      · -- F ties CE
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CEF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
      · -- F strictly outranks CE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_046 hCDlt hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith102_035 hCEeq hFGgt hCFgt), Or.inr hFGgt⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
            Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_053 hCEgt hCDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inl hBz, Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_053 hCEgt hCDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_056 hCEgt hCDlt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_036 hFGeq hCEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith102_056 hCEgt hCDlt hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_037 hCEgt hEFgt hFGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_059 hCEgt hCDlt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- D ties C
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz,
                Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
                Or.inl hBz, Or.inr hCElt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
                Or.inl hBz, Or.inr hCElt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDFG ⟨hA, hCne, hDne, hFne, hGne, hCDeq,
                hmCFeq, hmCGeq, Or.inl hBz, Or.inr hCElt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CD
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
      · -- F ties CD
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CDF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
      · -- F strictly outranks CD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_047 hCDeq hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith102_034 hCElt hFGgt hCFgt), Or.inr hFGgt⟩
    · -- E ties CD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
                Or.inl hBz, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDEG ⟨hA, hCne, hDne, hEne, hGne, hCDeq, hCEeq,
                hmCGeq, Or.inl hBz, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDEF ⟨hA, hCne, hDne, hEne, hFne, hCDeq, hCEeq,
                hmCFeq, Or.inl hBz, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDEFG ⟨hA, hCne, hDne, hEne, hFne, hGne, hCDeq,
                hCEeq, hmCFeq, hmCGeq, Or.inl hBz⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CDE
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
      · -- F ties CDE
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CDEF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CDEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
      · -- F strictly outranks CDE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_047 hCDeq hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith102_035 hCEeq hFGgt hCFgt), Or.inr hFGgt⟩
    · -- E strictly outranks CD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
            Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_054 hCEgt hCDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inl hBz, Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_054 hCEgt hCDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_057 hCEgt hCDeq hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_036 hFGeq hCEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith102_057 hCEgt hCDeq hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_037 hCEgt hEFgt hFGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_060 hCEgt hCDeq hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt,
            Or.inr hDElt, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz,
            Or.inr hCDgt, Or.inr hDElt, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz,
            Or.inr hCDgt, Or.inr hDElt, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inl hBz, Or.inr hCDgt, Or.inr hDElt⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_048 hFGeq hCDgt hDFgt hAG), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_049 hCDgt hFGgt hDFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith102_012 hDElt hFGgt hDFgt), Or.inr hFGgt⟩
    · -- E ties D
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz,
            Or.inr hCDgt, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inl hBz, Or.inr hCDgt, Or.inr hDFlt⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
      · -- F ties DE
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inl hBz, Or.inr hCDgt, Or.inr hDGlt⟩
        · -- G ties DEF
          exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
            hDGeq, Or.inl hBz, Or.inr hCDgt⟩
        · -- G strictly outranks DEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
      · -- F strictly outranks DE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_048 hFGeq hCDgt hDFgt hAG), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_049 hCDgt hFGgt hDFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith102_013 hDEeq hFGgt hDFgt), Or.inr hFGgt⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt),
            Or.inr hDEgt, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt), Or.inr hDEgt, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_055 hCDgt hDEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt), Or.inr hDEgt, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt), Or.inr hDEgt⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_055 hCDgt hDEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_058 hCDgt hDEgt hEFgt hAE),
            Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_061 hFGeq hCDgt hDEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_062 hCDgt hDEgt hEFgt hFGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_014 hDEgt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_B
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
    Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 77 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
  · -- B strictly outranks G
    rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
    · -- B³ beats the mixed monomial BG
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
        Or.inl hFz, Or.inr hmBGlt⟩
    · -- G ties B on the mixed monomial BG
      exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inl hFz⟩
    · -- the mixed monomial BG strictly beats B³ : residual cone
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- G ties B
    exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq), Or.inl hCz,
      Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- G strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz, Or.inl hDz,
      Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
  · -- B strictly outranks F
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
    · -- B³ beats the mixed monomial BF
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
        Or.inr hmBFlt, Or.inl hGz⟩
    · -- F ties B on the mixed monomial BF
      exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inl hGz⟩
    · -- the mixed monomial BF strictly beats B³ : residual cone
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- F ties B
    exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
      Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- F strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz, Or.inl hDz,
      Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 78 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
  · -- B strictly outranks F
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
            Or.inr hmBFlt, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz, Or.inl hDz,
            Or.inl hEz, Or.inr hmBFlt⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
      · -- F ties B on the mixed monomial BF
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz, Or.inl hDz,
            Or.inl hEz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
            Or.inl hCz, Or.inl hDz, Or.inl hEz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
    · -- G ties B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
    · -- G strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_071 hBFlt hBGgt)⟩
  · -- F ties B
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
    · -- G ties BF
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_072 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
    · -- G strictly outranks BF
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_073 hBFeq hBGgt)⟩
  · -- F strictly outranks B
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
    · -- F strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inr hFGlt⟩
    · -- G ties F
      exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_074 hFGeq hBFgt hAG),
        Or.inl hCz, Or.inl hDz, Or.inl hEz⟩
    · -- G strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_075 hBFgt hFGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
  · -- B strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inr hBElt,
      Or.inl hFz, Or.inl hGz⟩
  · -- E ties B
    exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz, Or.inl hDz,
      Or.inl hFz, Or.inl hGz⟩
  · -- E strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz, Or.inl hDz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 79 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
  · -- B strictly outranks E
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inr hBElt,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz, Or.inl hDz,
          Or.inr hBElt, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
    · -- G ties B
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq), Or.inl hCz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
    · -- G strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_077 hBElt hBGgt), Or.inl hFz⟩
  · -- E ties B
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz, Or.inl hDz,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq, Or.inl hCz,
          Or.inl hDz, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
    · -- G ties BE
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_079 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith102_065 hBGeq), Or.inl hCz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
    · -- G strictly outranks BE
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_080 hBEeq hBGgt), Or.inl hFz⟩
  · -- E strictly outranks B
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz, Or.inl hDz,
        Or.inl hFz, Or.inr hEGlt⟩
    · -- G ties E
      exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt, Or.inl hCz,
        Or.inl hDz, Or.inl hFz⟩
    · -- G strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_081 hBEgt hEGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
  · -- B strictly outranks E
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inr hBElt,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz, Or.inl hDz,
          Or.inr hBElt, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
    · -- F ties B
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
    · -- F strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz, Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_082 hBElt hBFgt), Or.inl hGz⟩
  · -- E ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz, Or.inl hDz,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq, Or.inl hCz,
          Or.inl hDz, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
    · -- F ties BE
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_083 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
    · -- F strictly outranks BE
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_084 hBEeq hBFgt hAE), Or.inl hCz, Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_085 hBEeq hBFgt), Or.inl hGz⟩
  · -- E strictly outranks B
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz, Or.inl hDz,
        Or.inr hEFlt, Or.inl hGz⟩
    · -- F ties E
      exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt, Or.inl hCz,
        Or.inl hDz, Or.inl hGz⟩
    · -- F strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_086 hBEgt hEFgt hAE), Or.inl hCz, Or.inl hDz,
        Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 80 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
  · -- B strictly outranks E
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz,
              Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz,
              Or.inl hDz, Or.inr hBElt, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz,
              Or.inl hDz, Or.inr hBElt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
              Or.inl hCz, Or.inl hDz, Or.inr hBElt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties B
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_077 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith102_071 hBFlt hBGgt)⟩
    · -- F ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_072 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_077 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith102_073 hBFeq hBGgt)⟩
    · -- F strictly outranks B
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_082 hBElt hBFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_074 hFGeq hBFgt hAG),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_082 hBElt hBFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_075 hBFgt hFGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_087 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
  · -- E ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz,
              Or.inl hDz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
              Or.inl hCz, Or.inl hDz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
              Or.inl hCz, Or.inl hDz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBEFG ⟨hA, hBne, hEne, hFne, hGne, hBEeq, hmBFeq,
              hmBGeq, Or.inl hCz, Or.inl hDz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BE
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_079 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_079 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_080 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith102_071 hBFlt hBGgt)⟩
    · -- F ties BE
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_083 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BEF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_083 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BEF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_080 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith102_073 hBFeq hBGgt)⟩
    · -- F strictly outranks BE
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_084 hBEeq hBFgt hAE), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_085 hBEeq hBFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_074 hFGeq hBFgt hAG),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_085 hBEeq hBFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_075 hBFgt hFGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_088 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
  · -- E strictly outranks B
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz, Or.inl hDz,
          Or.inr hEFlt, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt, Or.inl hCz,
          Or.inl hDz, Or.inr hEFlt⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_081 hBEgt hEGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
    · -- F ties E
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt, Or.inl hCz,
          Or.inl hDz, Or.inr hEGlt⟩
      · -- G ties EF
        exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
          Or.inr hBEgt, Or.inl hCz, Or.inl hDz⟩
      · -- G strictly outranks EF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_081 hBEgt hEGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
    · -- F strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_086 hBEgt hEFgt hAE), Or.inl hCz,
          Or.inl hDz, Or.inr hEFgt, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_089 hFGeq hBEgt hEFgt hAG),
          Or.inl hCz, Or.inl hDz, Or.inr hEFgt⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_090 hBEgt hEFgt hFGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BD
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- D ties B
    exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- D strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 81 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt, Or.inl hEz,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz, Or.inr hBDlt,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inl hFz⟩
    · -- G ties B
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_092 hBDlt hBGgt), Or.inl hEz, Or.inl hFz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz, Or.inl hEz,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq, Or.inl hCz,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inl hFz⟩
    · -- G ties BD
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks BD
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_094 hBDeq hBGgt), Or.inl hEz, Or.inl hFz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inl hEz,
        Or.inl hFz, Or.inr hDGlt⟩
    · -- G ties D
      exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt, Or.inl hCz,
        Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_095 hDGgt hBDgt hAG), Or.inl hCz,
        Or.inr hDGgt, Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt, Or.inl hEz,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz, Or.inr hBDlt,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inl hGz⟩
    · -- F ties B
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_096 hBDlt hBFgt), Or.inl hEz, Or.inl hGz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz, Or.inl hEz,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq, Or.inl hCz,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inl hGz⟩
    · -- F ties BD
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks BD
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_097 hBDeq hBFgt), Or.inl hEz, Or.inl hGz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inl hEz,
        Or.inr hDFlt, Or.inl hGz⟩
    · -- F ties D
      exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt, Or.inl hCz,
        Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_098 hAF hBDgt hDFgt), Or.inl hCz,
        Or.inr hDFgt, Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 82 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt,
              Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz,
              Or.inr hBDlt, Or.inl hEz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz,
              Or.inr hBDlt, Or.inl hEz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
              Or.inl hCz, Or.inr hBDlt, Or.inl hEz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties B
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_092 hBDlt hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_071 hBFlt hBGgt)⟩
    · -- F ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_072 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_092 hBDlt hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_073 hBFeq hBGgt)⟩
    · -- F strictly outranks B
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_096 hBDlt hBFgt), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_074 hFGeq hBFgt hAG),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_096 hBDlt hBFgt), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_075 hBFgt hFGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_099 hBDlt hBFgt hFGgt), Or.inl hEz, Or.inr hFGgt⟩
  · -- D ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz,
              Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
              Or.inl hCz, Or.inl hEz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
              Or.inl hCz, Or.inl hEz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDFG ⟨hA, hBne, hDne, hFne, hGne, hBDeq, hmBFeq,
              hmBGeq, Or.inl hCz, Or.inl hEz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_094 hBDeq hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_071 hBFlt hBGgt)⟩
    · -- F ties BD
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BDF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_072 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BDF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_094 hBDeq hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_073 hBFeq hBGgt)⟩
    · -- F strictly outranks BD
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_097 hBDeq hBFgt), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_074 hFGeq hBFgt hAG),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_097 hBDeq hBFgt), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_075 hBFgt hFGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_100 hBDeq hBFgt hFGgt), Or.inl hEz, Or.inr hFGgt⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inl hEz,
          Or.inr hDFlt, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt, Or.inl hCz,
          Or.inl hEz, Or.inr hDFlt⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_095 hDGgt hBDgt hAG), Or.inl hCz,
          Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
    · -- F ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt, Or.inl hCz,
          Or.inl hEz, Or.inr hDGlt⟩
      · -- G ties DF
        exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
          Or.inr hBDgt, Or.inl hCz, Or.inl hEz⟩
      · -- G strictly outranks DF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_095 hDGgt hBDgt hAG), Or.inl hCz,
          Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
    · -- F strictly outranks D
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_098 hAF hBDgt hDFgt), Or.inl hCz,
          Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_101 hFGeq hBDgt hDFgt hAG),
          Or.inl hCz, Or.inr hDFgt, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_102 hFGgt hBDgt hDFgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt, Or.inr hBElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties B
      exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz, Or.inr hBDlt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_103 hBEgt hBDlt), Or.inl hFz, Or.inl hGz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz, Or.inr hBElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties BD
      exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq, Or.inl hCz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks BD
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_104 hBEgt hBDeq), Or.inl hFz, Or.inl hGz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inr hDElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties D
      exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt, Or.inl hCz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith102_105 hDEgt hBDgt), Or.inl hCz,
        Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 83 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt,
            Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz,
            Or.inr hBDlt, Or.inr hBElt, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
      · -- G ties B
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_092 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith102_077 hBElt hBGgt), Or.inl hFz⟩
    · -- E ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz,
            Or.inr hBDlt, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
            Or.inl hCz, Or.inr hBDlt, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
      · -- G ties BE
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_079 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
      · -- G strictly outranks BE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_092 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith102_080 hBEeq hBGgt), Or.inl hFz⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_103 hBEgt hBDlt), Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_103 hBEgt hBDlt), Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_081 hBEgt hEGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_106 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inl hFz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz,
            Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
            Or.inl hCz, Or.inr hBElt, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
      · -- G ties BD
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
      · -- G strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_094 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith102_077 hBElt hBGgt), Or.inl hFz⟩
    · -- E ties BD
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
            Or.inl hCz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBDEG ⟨hA, hBne, hDne, hEne, hGne, hBDeq, hBEeq,
            hmBGeq, Or.inl hCz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
      · -- G ties BDE
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_079 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
      · -- G strictly outranks BDE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_094 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith102_080 hBEeq hBGgt), Or.inl hFz⟩
    · -- E strictly outranks BD
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_104 hBEgt hBDeq), Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_104 hBEgt hBDeq), Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_081 hBEgt hEGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_107 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inl hFz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inr hDElt,
          Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt, Or.inl hCz,
          Or.inr hDElt, Or.inl hFz⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_095 hDGgt hBDgt hAG), Or.inl hCz,
          Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inl hFz⟩
    · -- E ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt, Or.inl hCz,
          Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties DE
        exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
          Or.inr hBDgt, Or.inl hCz, Or.inl hFz⟩
      · -- G strictly outranks DE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_095 hDGgt hBDgt hAG), Or.inl hCz,
          Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inl hFz⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith102_105 hDEgt hBDgt), Or.inl hCz,
          Or.inr hDEgt, Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith102_105 hDEgt hBDgt),
          Or.inl hCz, Or.inr hDEgt, Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_108 hDEgt hBDgt hEGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt,
            Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz,
            Or.inr hBDlt, Or.inr hBElt, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
      · -- F ties B
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
      · -- F strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_096 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith102_082 hBElt hBFgt), Or.inl hGz⟩
    · -- E ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz,
            Or.inr hBDlt, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
            Or.inl hCz, Or.inr hBDlt, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
      · -- F ties BE
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_083 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
      · -- F strictly outranks BE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_084 hBEeq hBFgt hAE), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_096 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith102_085 hBEeq hBFgt), Or.inl hGz⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_103 hBEgt hBDlt), Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_103 hBEgt hBDlt), Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_086 hBEgt hEFgt hAE), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_109 hBEgt hBDlt hEFgt), Or.inr hEFgt, Or.inl hGz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz,
            Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
            Or.inl hCz, Or.inr hBElt, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
      · -- F ties BD
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
      · -- F strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_097 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith102_082 hBElt hBFgt), Or.inl hGz⟩
    · -- E ties BD
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
            Or.inl hCz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBDEF ⟨hA, hBne, hDne, hEne, hFne, hBDeq, hBEeq,
            hmBFeq, Or.inl hCz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
      · -- F ties BDE
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_083 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
      · -- F strictly outranks BDE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_084 hBEeq hBFgt hAE), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_097 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith102_085 hBEeq hBFgt), Or.inl hGz⟩
    · -- E strictly outranks BD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_104 hBEgt hBDeq), Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_104 hBEgt hBDeq), Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_086 hBEgt hEFgt hAE), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_110 hBEgt hBDeq hEFgt), Or.inr hEFgt, Or.inl hGz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inr hDElt,
          Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties D
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt, Or.inl hCz,
          Or.inr hDElt, Or.inl hGz⟩
      · -- F strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_098 hAF hBDgt hDFgt), Or.inl hCz,
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt), Or.inl hGz⟩
    · -- E ties D
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt, Or.inl hCz,
          Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties DE
        exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
          Or.inr hBDgt, Or.inl hCz, Or.inl hGz⟩
      · -- F strictly outranks DE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_098 hAF hBDgt hDFgt), Or.inl hCz,
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt), Or.inl hGz⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith102_105 hDEgt hBDgt), Or.inl hCz,
          Or.inr hDEgt, Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith102_105 hDEgt hBDgt),
          Or.inl hCz, Or.inr hDEgt, Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_111 hDEgt hEFgt hBDgt hAE), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 84 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_000
    {a b g : ℕ}
    (h0 : 4 * g < 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_001
    {a b d : ℕ}
    (h0 : 4 * d < a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_002
    {a b e : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_003
    {a b f : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_004
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_005
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_006
    {a b g : ℕ}
    (h0 : 7 * a + 6 * b < 4 * g)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_007
    {a b d g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_008
    {a b e g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_009
    {a b f g : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_010
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 4 * f = 5 * a + 6 * b)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_011
    {a b f : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_012
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_013
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_014
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_015
    {a b d f : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_016
    {a b e f : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_017
    {a b f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_018
    {a b f g : ℕ}
    (h0 : 5 * a + 6 * b < 4 * f)
    (h1 : a + 2 * f < 2 * g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_019
    {a b d f g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_020
    {a b e f g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_021
    {a b e : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_022
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_023
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_024
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * f = 5 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_025
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_026
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_027
    {a b e f g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_028
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_029
    {a b e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_030
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_031
    {a e f g : ℕ}
    (h0 : 2 * f < a + 2 * e)
    (h1 : a + e < g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_032
    {a e f g : ℕ}
    (h0 : 2 * f = a + 2 * e)
    (h1 : a + e < g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_033
    {a b e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_034
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_035
    {a b e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_036
    {a b e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_037
    {a b d e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_038
    {a e f g : ℕ}
    (h0 : a + 2 * e < 2 * f)
    (h1 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_039
    {a b d : ℕ}
    (h0 : 4 * d = a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_040
    {a b d g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_041
    {a b d f : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_042
    {a b d f g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_043
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_044
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_045
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_046
    {a b d e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_047
    {a b d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_048
    {a d e g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_049
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f < a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_050
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f = a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_051
    {a b d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_052
    {a d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_053
    {a b d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_054
    {a b d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_055
    {a d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + d < f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_056
    {a d e f g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_057
    {a d e g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_058
    {a d e f : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_059
    {a d e f g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_060
    {a b d e : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_061
    {a b d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_062
    {a d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_063
    {a b d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 6 * b < 4 * d)
    (h3 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_064
    {a d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_065
    {a b d e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 6 * b < 4 * d)
    (h4 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_066
    {a b d e f g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : a + 6 * b < 4 * d)
    (h4 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_067
    {a d e f g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_068
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : 2 * c ≤ a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_069
    {a b c g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_070
    {a b c : ℕ}
    (h0 : 2 * c = a + 2 * b)
    : 2 * c ≤ a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_071
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_072
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_073
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_074
    {a c g : ℕ}
    (h0 : 2 * g < 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_075
    {a b c : ℕ}
    (h0 : a + 2 * b < 2 * c)
    : a + 2 * b ≤ 2 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_076
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_077
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_078
    {a b c g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * b < 2 * c)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_079
    {a c g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_080
    {a b c f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_081
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 4 * f = 5 * a + 6 * b)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_082
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_083
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_084
    {a c f : ℕ}
    (h0 : 2 * f < a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_085
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_086
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_087
    {a b c f : ℕ}
    (h0 : a + 2 * b < 2 * c)
    (h1 : a + 3 * c < 2 * f)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_088
    {a c f : ℕ}
    (h0 : a + 3 * c < 2 * f)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_089
    {a b c f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : 5 * a + 6 * b < 4 * f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_090
    {a b c f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_091
    {a b c f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_092
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f < a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_093
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f = a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_094
    {a b c f g : ℕ}
    (h0 : a + 2 * b < 2 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_095
    {a c f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 3 * c < 2 * f)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_096
    {a b c e : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_097
    {a b c e : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_098
    {a b c e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_099
    {a b c e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_100
    {a b c e g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_101
    {c e : ℕ}
    (h0 : 2 * e < 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_102
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e < 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_103
    {c e : ℕ}
    (h0 : 2 * e = 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_104
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e = 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_105
    {a b c e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_106
    {a c e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_107
    {a b c e f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a + 6 * b < 4 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_108
    {a b c e f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_109
    {a b c e f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_110
    {a b c e f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_111
    {a c e f : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_112
    {a c e f : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_113
    {a b c e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_114
    {a c e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_115
    {a b c e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : 3 * a + 6 * b < 4 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_116
    {a b c e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_117
    {a b c e f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : 3 * a + 6 * b < 4 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_118
    {a b c e f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_119
    {a c e f g : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_120
    {a c e f g : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_121
    {a b c e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < 2 * e)
    (h2 : a + 2 * b < 2 * c)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_122
    {a c e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_123
    {a b c e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_124
    {a c e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_125
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 6 * b < 4 * d)
    : 3 * c < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_126
    {a b c d : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 6 * b < 4 * d)
    : 3 * c < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_127
    {a b c d : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    : a + 6 * b < 4 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_128
    {a b c d g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 2 * d < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_129
    {a b c d g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 2 * d < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_130
    {a c d : ℕ}
    (h0 : a + 2 * d < 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_131
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d < 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_132
    {a c d : ℕ}
    (h0 : a + 2 * d = 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_133
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d = 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_134
    {a b c d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_135
    {a c d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : 3 * c < a + 2 * d)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_136
    {a b c d f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_137
    {a b c d f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_138
    {a c d f : ℕ}
    (h0 : a + 2 * d < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_139
    {a c d f : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_140
    {a b c d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : a + d < f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_141
    {a c d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt,
                Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz,
                Or.inr hBDlt, Or.inr hBElt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz,
                Or.inr hBDlt, Or.inr hBElt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
                Or.inl hCz, Or.inr hBDlt, Or.inr hBElt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties B
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties B
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_012 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks B
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_019 hBDlt hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_020 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz,
                Or.inr hBDlt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
                Or.inl hCz, Or.inr hBDlt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
                Or.inl hCz, Or.inr hBDlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEFG ⟨hA, hBne, hEne, hFne, hGne, hBEeq,
                hmBFeq, hmBGeq, Or.inl hCz, Or.inr hBDlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BE
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BE
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BEF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_025 hBEeq hBFgt hAE), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_019 hBDlt hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_027 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_028 hBEgt hBDlt), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_028 hBEgt hBDlt), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_030 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_028 hBEgt hBDlt), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr hBEgt, Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_028 hBEgt hBDlt)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_030 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_033 hBEgt hEFgt hAE), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_034 hBEgt hBDlt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_035 hFGeq hBEgt hEFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_034 hBEgt hBDlt hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_036 hBEgt hEFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_037 hBEgt hBDlt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- D ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz,
                Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
                Or.inl hCz, Or.inr hBElt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
                Or.inl hCz, Or.inr hBElt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDFG ⟨hA, hBne, hDne, hFne, hGne, hBDeq,
                hmBFeq, hmBGeq, Or.inl hCz, Or.inr hBElt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BD
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BDF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_012 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_042 hBDeq hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_020 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E ties BD
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
                Or.inl hCz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDEG ⟨hA, hBne, hDne, hEne, hGne, hBDeq, hBEeq,
                hmBGeq, Or.inl hCz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDEF ⟨hA, hBne, hDne, hEne, hFne, hBDeq, hBEeq,
                hmBFeq, Or.inl hCz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDEFG ⟨hA, hBne, hDne, hEne, hFne, hGne, hBDeq,
                hBEeq, hmBFeq, hmBGeq, Or.inl hCz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BDE
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BDE
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BDEF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BDEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BDE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_025 hBEeq hBFgt hAE), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_042 hBDeq hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_027 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E strictly outranks BD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_043 hBEgt hBDeq), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_043 hBEgt hBDeq), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_044 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_043 hBEgt hBDeq), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr hBEgt, Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_043 hBEgt hBDeq)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_044 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_033 hBEgt hEFgt hAE), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_045 hBEgt hBDeq hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_035 hFGeq hBEgt hEFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_045 hBEgt hBDeq hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_036 hBEgt hEFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_046 hBEgt hBDeq hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz,
            Or.inr hDElt, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inl hCz, Or.inr hDElt, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith103_048 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith103_049 hDGgt hDFlt)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inl hCz, Or.inr hDElt, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inr hBDgt, Or.inl hCz, Or.inr hDElt⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith103_048 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith103_050 hDGgt hDFeq)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_051 hAF hBDgt hDFgt), Or.inl hCz,
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith103_052 hDElt hDFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_053 hFGeq hBDgt hDFgt hAG),
            Or.inl hCz, Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith103_052 hDElt hDFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_054 hFGgt hBDgt hDFgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_055 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith103_056 hDElt hFGgt hDFgt), Or.inr hFGgt⟩
    · -- E ties D
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inl hCz, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inr hBDgt, Or.inl hCz, Or.inr hDFlt⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith103_057 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith103_049 hDGgt hDFlt)⟩
      · -- F ties DE
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inr hBDgt, Or.inl hCz, Or.inr hDGlt⟩
        · -- G ties DEF
          exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
            hDGeq, Or.inr hBDgt, Or.inl hCz⟩
        · -- G strictly outranks DEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith103_057 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith103_050 hDGgt hDFeq)⟩
      · -- F strictly outranks DE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_051 hAF hBDgt hDFgt), Or.inl hCz,
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith103_058 hDEeq hDFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_053 hFGeq hBDgt hDFgt hAG),
            Or.inl hCz, Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith103_058 hDEeq hDFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_054 hFGgt hBDgt hDFgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_055 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith103_059 hDEeq hFGgt hDFgt), Or.inr hFGgt⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith103_060 hDEgt hBDgt), Or.inl hCz,
            Or.inr hDEgt, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith103_060 hDEgt hBDgt),
            Or.inl hCz, Or.inr hDEgt, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_061 hDEgt hBDgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_062 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith103_060 hDEgt hBDgt),
            Or.inl hCz, Or.inr hDEgt, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr (by exact sigmaSpeedTArith103_060 hDEgt hBDgt), Or.inl hCz, Or.inr hDEgt⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_061 hDEgt hBDgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_062 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_063 hDEgt hEFgt hBDgt hAE), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_064 hDEgt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_065 hFGeq hDEgt hEFgt hBDgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_064 hDEgt hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_066 hDEgt hEFgt hFGgt hBDgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_067 hDEgt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BC
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- C ties B
    exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- C strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 85 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz, Or.inl hEz,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt, Or.inl hDz,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G ties B
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
        Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz, Or.inl hEz,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq, Or.inl hDz,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G ties BC
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
        Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks BC
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz, Or.inl hEz,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt, Or.inl hDz,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G ties C
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
        Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz, Or.inl hEz,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt, Or.inl hDz,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F ties B
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
        Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz, Or.inl hEz,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq, Or.inl hDz,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F ties BC
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
        Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks BC
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz, Or.inl hEz,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt, Or.inl hDz,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F ties C
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
        Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 86 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz,
              Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
              Or.inl hDz, Or.inl hEz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
              Or.inl hDz, Or.inl hEz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
              Or.inr hBClt, Or.inl hDz, Or.inl hEz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
      · -- G ties B
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
    · -- F ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
      · -- G ties BF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_012 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
      · -- G strictly outranks BF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
    · -- F strictly outranks B
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
          Or.inr (by exact sigmaSpeedTArith103_089 hBClt hFGeq hBFgt hAG), Or.inl hDz, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_090 hBClt hBFgt hFGgt hAG),
          Or.inl hDz, Or.inl hEz, Or.inr hFGgt⟩
  · -- C ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz,
              Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
              Or.inl hDz, Or.inl hEz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
              Or.inl hDz, Or.inl hEz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCFG ⟨hA, hBne, hCne, hFne, hGne, hBCeq, hmBFeq,
              hmBGeq, Or.inl hDz, Or.inl hEz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
      · -- G ties BC
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
      · -- G strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
    · -- F ties BC
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
      · -- G ties BCF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
      · -- G strictly outranks BCF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
    · -- F strictly outranks BC
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC), Or.inl hDz, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_091 hBCeq hBFgt hFGgt hAG),
          Or.inl hDz, Or.inl hEz, Or.inr hFGgt⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz,
              Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
              Or.inl hDz, Or.inl hEz, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
              Or.inl hDz, Or.inl hEz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
              Or.inr hBCgt, Or.inl hDz, Or.inl hEz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
      · -- G ties C
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_092 hCGgt hCFlt)⟩
    · -- F ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
      · -- G ties CF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
      · -- G strictly outranks CF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_093 hCGgt hCFeq)⟩
    · -- F strictly outranks C
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC), Or.inl hDz, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_094 hBCgt hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith103_095 hFGgt hCFgt hAG),
          Or.inl hDz, Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz, Or.inr hBElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties B
      exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt, Or.inl hDz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt),
        Or.inl hDz, Or.inl hFz, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz, Or.inr hBElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties BC
      exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq, Or.inl hDz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks BC
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt),
        Or.inl hDz, Or.inl hFz, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz, Or.inr hCElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties C
      exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt, Or.inl hDz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt), Or.inr hCEgt,
        Or.inl hDz, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 87 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz,
            Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
            Or.inl hDz, Or.inr hBElt, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hFz⟩
      · -- G ties B
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hFz⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inl hFz⟩
    · -- E ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
            Or.inl hDz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
            Or.inr hBClt, Or.inl hDz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hFz⟩
      · -- G ties BE
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hFz⟩
      · -- G strictly outranks BE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inl hFz⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt),
          Or.inl hDz, Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
          Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt), Or.inl hDz, Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_099 hBClt hBEgt hEGgt hAG),
          Or.inl hDz, Or.inr hEGgt, Or.inl hFz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz,
            Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
            Or.inl hDz, Or.inr hBElt, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hFz⟩
      · -- G ties BC
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hFz⟩
      · -- G strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inl hFz⟩
    · -- E ties BC
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
            Or.inl hDz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCEG ⟨hA, hBne, hCne, hEne, hGne, hBCeq, hBEeq,
            hmBGeq, Or.inl hDz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hFz⟩
      · -- G ties BCE
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hFz⟩
      · -- G strictly outranks BCE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inl hFz⟩
    · -- E strictly outranks BC
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt),
          Or.inl hDz, Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
          Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt), Or.inl hDz, Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_100 hBCeq hBEgt hEGgt hAG),
          Or.inl hDz, Or.inr hEGgt, Or.inl hFz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz,
            Or.inr hCElt, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
            Or.inl hDz, Or.inr hCElt, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inl hFz⟩
      · -- G ties C
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inl hFz⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_102 hCGgt hCElt), Or.inl hFz⟩
    · -- E ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
            Or.inl hDz, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
            Or.inr hBCgt, Or.inl hDz, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inl hFz⟩
      · -- G ties CE
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inl hFz⟩
      · -- G strictly outranks CE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_104 hCGgt hCEeq), Or.inl hFz⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt), Or.inr hCEgt,
          Or.inl hDz, Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt),
          Or.inr hCEgt, Or.inl hDz, Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_105 hCEgt hBCgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_106 hCEgt hEGgt hAG),
          Or.inl hDz, Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz,
            Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
            Or.inl hDz, Or.inr hBElt, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hGz⟩
      · -- F ties B
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hGz⟩
      · -- F strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inl hGz⟩
    · -- E ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
            Or.inl hDz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
            Or.inr hBClt, Or.inl hDz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hGz⟩
      · -- F ties BE
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hGz⟩
      · -- F strictly outranks BE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_025 hBEeq hBFgt hAE), Or.inr (by exact sigmaSpeedTArith103_107 hBClt hBEeq hBFgt hAE),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inl hGz⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt),
          Or.inl hDz, Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
          Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt), Or.inl hDz, Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_033 hBEgt hEFgt hAE), Or.inr (by exact sigmaSpeedTArith103_108 hBClt hBEgt hEFgt hAE),
          Or.inl hDz, Or.inr hEFgt, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz,
            Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
            Or.inl hDz, Or.inr hBElt, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hGz⟩
      · -- F ties BC
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hGz⟩
      · -- F strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inl hGz⟩
    · -- E ties BC
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
            Or.inl hDz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCEF ⟨hA, hBne, hCne, hEne, hFne, hBCeq, hBEeq,
            hmBFeq, Or.inl hDz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hGz⟩
      · -- F ties BCE
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hGz⟩
      · -- F strictly outranks BCE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inl hGz⟩
    · -- E strictly outranks BC
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt),
          Or.inl hDz, Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
          Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt), Or.inl hDz, Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_109 hBCeq hBEgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith103_110 hBCeq hBEgt hEFgt hAC),
          Or.inl hDz, Or.inr hEFgt, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz,
            Or.inr hCElt, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
            Or.inl hDz, Or.inr hCElt, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inl hGz⟩
      · -- F ties C
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inl hGz⟩
      · -- F strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_111 hCElt hCFgt), Or.inl hGz⟩
    · -- E ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
            Or.inl hDz, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
            Or.inr hBCgt, Or.inl hDz, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inl hGz⟩
      · -- F ties CE
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inl hGz⟩
      · -- F strictly outranks CE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_112 hCEeq hCFgt), Or.inl hGz⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt), Or.inr hCEgt,
          Or.inl hDz, Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt),
          Or.inr hCEgt, Or.inl hDz, Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_113 hCEgt hBCgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith103_114 hCEgt hEFgt hAC),
          Or.inl hDz, Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 88 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz,
                Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
                Or.inl hDz, Or.inr hBElt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
                Or.inl hDz, Or.inr hBElt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
                Or.inr hBClt, Or.inl hDz, Or.inr hBElt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties B
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties B
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_012 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks B
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inr (by exact sigmaSpeedTArith103_089 hBClt hFGeq hBFgt hAG), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_090 hBClt hBFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_020 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
                Or.inl hDz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
                Or.inr hBClt, Or.inl hDz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
                Or.inr hBClt, Or.inl hDz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEFG ⟨hA, hBne, hEne, hFne, hGne, hBEeq,
                hmBFeq, hmBGeq, Or.inr hBClt, Or.inl hDz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BE
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BE
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BEF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_025 hBEeq hBFgt hAE), Or.inr (by exact sigmaSpeedTArith103_107 hBClt hBEeq hBFgt hAE),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inr (by exact sigmaSpeedTArith103_089 hBClt hFGeq hBFgt hAG), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_090 hBClt hBFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_027 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt),
            Or.inl hDz, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt), Or.inl hDz, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_099 hBClt hBEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt), Or.inl hDz, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt), Or.inl hDz⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_099 hBClt hBEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_033 hBEgt hEFgt hAE), Or.inr (by exact sigmaSpeedTArith103_108 hBClt hBEgt hEFgt hAE),
            Or.inl hDz, Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_035 hFGeq hBEgt hEFgt hAG),
            Or.inr (by exact sigmaSpeedTArith103_115 hBClt hFGeq hBEgt hEFgt hAG), Or.inl hDz, Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_036 hBEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_116 hBClt hBEgt hEFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- C ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz,
                Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
                Or.inl hDz, Or.inr hBElt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
                Or.inl hDz, Or.inr hBElt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCFG ⟨hA, hBne, hCne, hFne, hGne, hBCeq,
                hmBFeq, hmBGeq, Or.inl hDz, Or.inr hBElt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BC
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BC
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BC
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BCF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BCF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BC
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_091 hBCeq hBFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_020 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E ties BC
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
                Or.inl hDz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCEG ⟨hA, hBne, hCne, hEne, hGne, hBCeq, hBEeq,
                hmBGeq, Or.inl hDz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCEF ⟨hA, hBne, hCne, hEne, hFne, hBCeq, hBEeq,
                hmBFeq, Or.inl hDz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCEFG ⟨hA, hBne, hCne, hEne, hFne, hGne, hBCeq,
                hBEeq, hmBFeq, hmBGeq, Or.inl hDz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BCE
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BCE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BCE
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BCEF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BCEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BCE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_091 hBCeq hBFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_027 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E strictly outranks BC
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt),
            Or.inl hDz, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt), Or.inl hDz, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_100 hBCeq hBEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt), Or.inl hDz, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt), Or.inl hDz⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_100 hBCeq hBEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_109 hBCeq hBEgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith103_110 hBCeq hBEgt hEFgt hAC),
            Or.inl hDz, Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_035 hFGeq hBEgt hEFgt hAG),
            Or.inr (by exact sigmaSpeedTArith103_117 hBCeq hFGeq hBEgt hEFgt hAG), Or.inl hDz, Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_036 hBEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_118 hBCeq hBEgt hEFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz,
                Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
                Or.inl hDz, Or.inr hCElt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
                Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
                Or.inl hDz, Or.inr hCElt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
                Or.inr hBCgt, Or.inl hDz, Or.inr hCElt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
                Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
        · -- G ties C
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
        · -- G strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_102 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith103_092 hCGgt hCFlt)⟩
      · -- F ties C
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
        · -- G ties CF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
        · -- G strictly outranks CF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_102 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith103_093 hCGgt hCFeq)⟩
      · -- F strictly outranks C
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_111 hCElt hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_111 hCElt hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_094 hBCgt hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith103_095 hFGgt hCFgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_119 hCElt hFGgt hCFgt), Or.inr hFGgt⟩
    · -- E ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
                Or.inl hDz, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
                Or.inr hBCgt, Or.inl hDz, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
                Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
                Or.inr hBCgt, Or.inl hDz, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEFG ⟨hA, hCne, hEne, hFne, hGne, hCEeq,
                hmCFeq, hmCGeq, Or.inr hBCgt, Or.inl hDz⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
                Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
        · -- G ties CE
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
        · -- G strictly outranks CE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_104 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith103_092 hCGgt hCFlt)⟩
      · -- F ties CE
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
        · -- G ties CEF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
        · -- G strictly outranks CEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_104 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith103_093 hCGgt hCFeq)⟩
      · -- F strictly outranks CE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_112 hCEeq hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_112 hCEeq hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_094 hBCgt hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith103_095 hFGgt hCFgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_120 hCEeq hFGgt hCFgt), Or.inr hFGgt⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt), Or.inr hCEgt,
            Or.inl hDz, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt),
            Or.inr hCEgt, Or.inl hDz, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_105 hCEgt hBCgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_106 hCEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt),
            Or.inr hCEgt, Or.inl hDz, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt), Or.inr hCEgt, Or.inl hDz⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_105 hCEgt hBCgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_106 hCEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_113 hCEgt hBCgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith103_114 hCEgt hEFgt hAC),
            Or.inl hDz, Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_121 hFGeq hCEgt hBCgt hEFgt hAG),
            Or.inr (by exact sigmaSpeedTArith103_122 hFGeq hCEgt hEFgt hAG), Or.inl hDz, Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_123 hCEgt hBCgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_124 hCEgt hEFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCD
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D ties B
      exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_125 hBClt hBDgt),
        Or.inl hEz, Or.inl hFz, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D ties BC
      exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks BC
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_126 hBCeq hBDgt),
        Or.inl hEz, Or.inl hFz, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D ties C
      exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith103_127 hCDgt hBCgt), Or.inr hCDgt,
        Or.inl hEz, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 89 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCDG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
            Or.inl hEz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
            Or.inr hBDlt, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G ties B
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inl hEz, Or.inl hFz⟩
    · -- D ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
            Or.inl hEz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
            Or.inr hBClt, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G ties BD
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inl hEz, Or.inl hFz⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_125 hBClt hBDgt),
          Or.inl hEz, Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
          Or.inr (by exact sigmaSpeedTArith103_125 hBClt hBDgt), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith103_128 hBClt hDGgt hBDgt hAG),
          Or.inr hDGgt, Or.inl hEz, Or.inl hFz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
            Or.inl hEz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
            Or.inr hBDlt, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G ties BC
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inl hEz, Or.inl hFz⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
            Or.inl hEz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCDG ⟨hA, hBne, hCne, hDne, hGne, hBCeq, hBDeq,
            hmBGeq, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G ties BCD
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks BCD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inl hEz, Or.inl hFz⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_126 hBCeq hBDgt),
          Or.inl hEz, Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
          Or.inr (by exact sigmaSpeedTArith103_126 hBCeq hBDgt), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith103_129 hBCeq hDGgt hBDgt hAG),
          Or.inr hDGgt, Or.inl hEz, Or.inl hFz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
            Or.inl hEz, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
            Or.inr hCDlt, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_130 hCDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G ties C
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_130 hCDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_131 hCGgt hCDlt), Or.inl hEz, Or.inl hFz⟩
    · -- D ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
            Or.inl hEz, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
            Or.inr hBCgt, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_132 hCDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G ties CD
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_132 hCDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_133 hCGgt hCDeq), Or.inl hEz, Or.inl hFz⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith103_127 hCDgt hBCgt), Or.inr hCDgt,
          Or.inl hEz, Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr (by exact sigmaSpeedTArith103_127 hCDgt hBCgt),
          Or.inr hCDgt, Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_134 hDGgt hCDgt hBCgt hAG), Or.inr (by exact sigmaSpeedTArith103_135 hDGgt hCDgt hAG),
          Or.inr hDGgt, Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCDF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
            Or.inl hEz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
            Or.inr hBDlt, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F ties B
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
            Or.inl hEz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
            Or.inr hBClt, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F ties BD
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_125 hBClt hBDgt),
          Or.inl hEz, Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties D
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
          Or.inr (by exact sigmaSpeedTArith103_125 hBClt hBDgt), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_051 hAF hBDgt hDFgt), Or.inr (by exact sigmaSpeedTArith103_136 hBClt hAF hBDgt hDFgt),
          Or.inr hDFgt, Or.inl hEz, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
            Or.inl hEz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
            Or.inr hBDlt, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F ties BC
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
            Or.inl hEz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCDF ⟨hA, hBne, hCne, hDne, hFne, hBCeq, hBDeq,
            hmBFeq, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F ties BCD
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks BCD
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_126 hBCeq hBDgt),
          Or.inl hEz, Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties D
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
          Or.inr (by exact sigmaSpeedTArith103_126 hBCeq hBDgt), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_051 hAF hBDgt hDFgt), Or.inr (by exact sigmaSpeedTArith103_137 hBCeq hAF hBDgt hDFgt),
          Or.inr hDFgt, Or.inl hEz, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
            Or.inl hEz, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
            Or.inr hCDlt, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_130 hCDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F ties C
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_130 hCDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_138 hCDlt hCFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
            Or.inl hEz, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
            Or.inr hBCgt, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_132 hCDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F ties CD
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_132 hCDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_139 hCDeq hCFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith103_127 hCDgt hBCgt), Or.inr hCDgt,
          Or.inl hEz, Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties D
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr (by exact sigmaSpeedTArith103_127 hCDgt hBCgt),
          Or.inr hCDgt, Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_140 hAF hCDgt hBCgt hDFgt), Or.inr (by exact sigmaSpeedTArith103_141 hAF hCDgt hDFgt),
          Or.inr hDFgt, Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
