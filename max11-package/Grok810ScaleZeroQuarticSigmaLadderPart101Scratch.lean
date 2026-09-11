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


def QuarticSigmaConeB810' (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


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


def QuarticLoadSigmaConeD810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D ≠ 0 ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (F = 0 ∨ F.natDegree < A.natDegree + D.natDegree) ∧
    (G = 0 ∨ 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree)


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


def QuarticLoadSigmaConeF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    F ≠ 0 ∧
    (B = 0 ∨ A.natDegree + 4 * B.natDegree < 2 * F.natDegree) ∧
    (C = 0 ∨ 4 * C.natDegree < A.natDegree + 2 * F.natDegree) ∧
    (D = 0 ∨ A.natDegree + D.natDegree < F.natDegree) ∧
    (E = 0 ∨ A.natDegree + 2 * E.natDegree < 2 * F.natDegree) ∧
    (G = 0 ∨ 2 * G.natDegree < A.natDegree + 2 * F.natDegree)


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


def QuarticSigmaConeBC810' (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


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


def QuarticLoadSigmaConeBE810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    E ≠ 0 ∧
    4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree < A.natDegree + 4 * B.natDegree) ∧
    (G = 0 ∨ G.natDegree < A.natDegree + 2 * B.natDegree)


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


def QuarticLoadSigmaConeCE810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    E ≠ 0 ∧
    2 * E.natDegree = 3 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 4 * C.natDegree) ∧
    (G = 0 ∨ G.natDegree < 2 * C.natDegree)


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


def QuarticLoadSigmaConeCG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    G ≠ 0 ∧
    G.natDegree = 2 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree) ∧
    (F = 0 ∨ A.natDegree + 2 * F.natDegree < 4 * C.natDegree)


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


def QuarticLoadSigmaConeDF810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D ≠ 0 ∧
    F ≠ 0 ∧
    F.natDegree = A.natDegree + D.natDegree ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (G = 0 ∨ 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree)


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


def QuarticLoadSigmaConeFG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    2 * G.natDegree = A.natDegree + 2 * F.natDegree ∧
    (B = 0 ∨ A.natDegree + 4 * B.natDegree < 2 * F.natDegree) ∧
    (C = 0 ∨ 4 * C.natDegree < A.natDegree + 2 * F.natDegree) ∧
    (D = 0 ∨ A.natDegree + D.natDegree < F.natDegree) ∧
    (E = 0 ∨ A.natDegree + 2 * E.natDegree < 2 * F.natDegree)


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


/-- `ν + (1/8)·A·κ` : weight 13, level-2 face `(5/16)(DG+EF)`, zero on `S ⊆ {B,C}`. -/
def degreeZeroN2Quartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G +
    (1 / 8 : k) • (A * degreeZeroKappaQuartic810 l beta gamma delta
      epsilon zeta eta theta A B C D E F G)


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


def n2QuarticLFace810 (l : k) (A : k[X]) : k[X] :=
  (231 / 4194304 * l : k) • A ^ 6

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


def n2QuarticDeltaFace810 (delta : k) (A : k[X]) : k[X] :=
  (35 / 32768 * delta : k) • A ^ 4

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


def kappaQuarticLFace810 (l : k) (A : k[X]) : k[X] :=
  (63 / 262144 * l : k) • A ^ 5

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


def kappaQuarticDeltaFace810 (delta : k) (A : k[X]) : k[X] :=
  (5 / 1024 * delta : k) • A ^ 3

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
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  simp only [hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    sub_zero, neg_zero, sub_self]
  ring


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
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hAF
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hAG
  have hBt1 : 4 * B.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hBt
  have hCt1 : 4 * C.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hCt
  have hDt1 : 4 * D.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hDt
  have hEt1 : 4 * E.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hEt
  have hFt1 : 4 * F.natDegree + 1 ≤ 13 * A.natDegree := Nat.succ_le_of_lt hFt
  have hGt1 : 4 * G.natDegree + 1 ≤ 15 * A.natDegree := Nat.succ_le_of_lt hGt
  simp only [degreeZeroKappaQuarticNoL1810]
  compute_degree
  omega


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
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hAF
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hAG
  have hBt1 : 4 * B.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hBt
  have hCt1 : 4 * C.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hCt
  have hDt1 : 4 * D.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hDt
  have hEt1 : 4 * E.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hEt
  have hFt1 : 4 * F.natDegree + 1 ≤ 13 * A.natDegree := Nat.succ_le_of_lt hFt
  have hGt1 : 4 * G.natDegree + 1 ≤ 15 * A.natDegree := Nat.succ_le_of_lt hGt
  simp only [degreeZeroKappaQuarticNoL2810]
  compute_degree
  omega


end QuarticKappaLadder810
end Max11DegreeRoutes
end
