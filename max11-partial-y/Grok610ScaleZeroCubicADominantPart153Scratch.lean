import Grok610ScaleZeroCubicConesScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeB610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    ∧ 4 * D.natDegree < A.natDegree + 6 * B.natDegree
    ∧ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeC610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < C.natDegree
    ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree
    ∧ A.natDegree + 2 * D.natDegree < 3 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree
    ∧ 11 * A.natDegree < 6 * C.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < D.natDegree
    ∧ A.natDegree + 6 * B.natDegree < 4 * D.natDegree
    ∧ 3 * C.natDegree < A.natDegree + 2 * D.natDegree
    ∧ 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    ∧ 9 * A.natDegree < 4 * D.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < E.natDegree
    ∧ 3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree
    ∧ 3 * C.natDegree < 2 * E.natDegree
    ∧ A.natDegree + 2 * D.natDegree < 2 * E.natDegree
    ∧ 11 * A.natDegree < 4 * E.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeBC610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree
    ∧ 4 * D.natDegree < A.natDegree + 6 * B.natDegree
    ∧ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeBD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree
    ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    ∧ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeBE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ 12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree
    ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    ∧ 4 * D.natDegree < A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeCE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 6 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * E.natDegree
    ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree
    ∧ A.natDegree + 2 * D.natDegree < 3 * C.natDegree
    ∧ 11 * A.natDegree < 6 * C.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 6 * A.natDegree + 2 * D.natDegree = 5 * A.natDegree + 2 * E.natDegree
    ∧ A.natDegree + 6 * B.natDegree < 4 * D.natDegree
    ∧ 3 * C.natDegree < A.natDegree + 2 * D.natDegree
    ∧ 9 * A.natDegree < 4 * D.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeBCD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree
    ∧ 10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree
    ∧ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeBCE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree
    ∧ 12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree
    ∧ 4 * D.natDegree < A.natDegree + 6 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeBDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree
    ∧ 12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree
    ∧ 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeCDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 5 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * D.natDegree
    ∧ 6 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * E.natDegree
    ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree
    ∧ 11 * A.natDegree < 6 * C.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeCD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 5 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * D.natDegree
    ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree
    ∧ 11 * A.natDegree < 6 * C.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeBCDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree
    ∧ 10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree
    ∧ 12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree
    ∧ 4 * A.natDegree < 3 * B.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def cubicLoadCompetes610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 3 * B.natDegree ∧
    11 * A.natDegree ≥ 6 * C.natDegree ∧
    9 * A.natDegree ≥ 4 * D.natDegree ∧
    11 * A.natDegree ≥ 4 * E.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicN1_610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroN1Cubic610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)
  + (77 / 248832 * l : k) • A ^ 6
  + (35 / 6912 * l : k) • (A ^ 4 * C)
  - (1 / 1152 * l : k) • (A ^ 3 * B ^ 2)
  + (5 / 288 * l : k) • (A ^ 3 * E)
  - (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 64 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 32 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  + (1 / 8 * l : k) • (A * C * E)
  - (1 / 16 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 6912 * beta : k) • A ^ 5
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

end CubicN1_610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicN1_610

variable {k : Type*} [Field k] [CharZero k]

def n1CubicSigma7Face610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (C ^ 2 * D)

end CubicN1_610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicN1_610

variable {k : Type*} [Field k] [CharZero k]

def n1CubicLFace610 (l : k) (A : k[X]) : k[X] :=
  (77 / 248832 * l : k) • A ^ 6

end CubicN1_610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicN1_610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoL610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)
  + (35 / 6912 * l : k) • (A ^ 4 * C)
  - (1 / 1152 * l : k) • (A ^ 3 * B ^ 2)
  + (5 / 288 * l : k) • (A ^ 3 * E)
  - (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 64 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 32 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  + (1 / 8 * l : k) • (A * C * E)
  - (1 / 16 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 6912 * beta : k) • A ^ 5
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

end CubicN1_610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone B -/

def kappaCubicSigmaFaceB610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaB610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone C -/

def lambdaCubicSigmaFaceC610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • C ^ 3

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  + (5 / 9 : k) • E ^ 2
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone D -/

def lambdaCubicSigmaFaceD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D ^ 2)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone E -/

def lambdaCubicSigmaFaceE610 (A B C D E : k[X]) : k[X] :=
  (5 / 9 : k) • E ^ 2

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 81 : k) • C ^ 3
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone BC -/

def kappaCubicSigmaInnerBC610 (a b c : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b * c ^ 2

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

def lambdaCubicSigmaInnerBC610 (a b c : k) : k :=
  5 * a * b ^ 2 * c + (-5 : k) * c ^ 3

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

def kappaCubicSigmaFaceBC610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaBC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

def lambdaCubicSigmaFaceBC610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 81 : k) • C ^ 3

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaBC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  + (5 / 9 : k) • E ^ 2
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone BD -/

def kappaCubicSigmaFaceBD610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaBD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone BE -/

def kappaCubicSigmaFaceBE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaBE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone CE -/

def omicronCubicSigmaFaceCE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * E)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (5 / 81 : k) • (A * B ^ 2 * E)
  + (10 / 81 : k) • (A * B * C * D)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone DE -/

def kappaCubicSigmaFaceDE610 (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone BCD -/

def omicronCubicSigmaFaceBCD610 (A B C D E : k[X]) : k[X] :=
  (10 / 81 : k) • (A * B * C * D)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (5 / 81 : k) • (A * B ^ 2 * E)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C ^ 2 * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone BCE -/

def kappaCubicSigmaInnerBCE610 (a b c e : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b * c ^ 2

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

def lambdaCubicSigmaInnerBCE610 (a b c e : k) : k :=
  5 * a * b ^ 2 * c + (-5 : k) * c ^ 3 + 45 * e ^ 2

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

def omicronCubicSigmaInnerBCE610 (a b c e : k) : k :=
  5 * a * b ^ 2 * e + (-15 : k) * c ^ 2 * e

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

def kappaCubicSigmaFaceBCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

def lambdaCubicSigmaFaceBCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

def omicronCubicSigmaFaceBCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * E)
  - (5 / 27 : k) • (C ^ 2 * E)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (10 / 81 : k) • (A * B * C * D)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone BDE -/

def omicronCubicSigmaFaceBDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * E)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaBDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (10 / 81 : k) • (A * B * C * D)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C ^ 2 * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone CDE -/

def kappaCubicSigmaFaceCDE610 (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

def lambdaCubicSigmaFaceCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D ^ 2)
  - (5 / 81 : k) • C ^ 3

end CubicSigmaCD610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  + (5 / 9 : k) • E ^ 2
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

end CubicSigmaCD610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

def n1CubicSigmaFaceCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * D)

end CubicSigmaCD610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoSigmaCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  + (77 / 248832 * l : k) • A ^ 6
  + (35 / 6912 * l : k) • (A ^ 4 * C)
  - (1 / 1152 * l : k) • (A ^ 3 * B ^ 2)
  + (5 / 288 * l : k) • (A ^ 3 * E)
  - (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 64 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 32 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  + (1 / 8 * l : k) • (A * C * E)
  - (1 / 16 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 6912 * beta : k) • A ^ 5
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

end CubicSigmaCD610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

def kappaCubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)

end CubicBalanced610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

end CubicBalanced610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

def lambdaCubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2

end CubicBalanced610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

end CubicBalanced610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

def omicronCubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * E)
  + (10 / 81 : k) • (A * B * C * D)
  - (5 / 27 : k) • (C ^ 2 * E)

end CubicBalanced610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

end CubicBalanced610

end Max11DegreeRoutes
