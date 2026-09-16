import Grok610ScaleZeroCubicLoadMultiScratch
import Max11SpeedReflectDegLibScratch

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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

def n2CubicBetaFace610 (beta : k) (A : k[X]) : k[X] :=
  (35 / 41472 * beta : k) • A ^ 6

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

def n2CubicDeltaFace610 (delta : k) (A : k[X]) : k[X] :=
  (7 / 2592 * delta : k) • A ^ 5

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

def n2CubicZetaFace610 (zeta : k) (A : k[X]) : k[X] :=
  (5 / 576 * zeta : k) • A ^ 4

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

def n2CubicThetaFace610 (theta : k) (A : k[X]) : k[X] :=
  (1 / 36 * theta : k) • A ^ 3

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

def omicronCubicSigmaInnerCD610 (c d : k) : k :=
  c * d ^ 2

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

def omicronCubicSigmaFaceCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C * D ^ 2)

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

theorem n1CubicBetaFace610_coeff_top (beta : k) (A : k[X]) :
    (n1CubicBetaFace610 beta A).coeff (5 * A.natDegree) =
      (7 / 6912 * beta : k) * A.leadingCoeff ^ 5 := by
  simp only [n1CubicBetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 5).natDegree = 5 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

theorem n1CubicDeltaFace610_coeff_top (delta : k) (A : k[X]) :
    (n1CubicDeltaFace610 delta A).coeff (4 * A.natDegree) =
      (35 / 10368 * delta : k) * A.leadingCoeff ^ 4 := by
  simp only [n1CubicDeltaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 4).natDegree = 4 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

theorem n1CubicZetaFace610_coeff_top (zeta : k) (A : k[X]) :
    (n1CubicZetaFace610 zeta A).coeff (3 * A.natDegree) =
      (5 / 432 * zeta : k) * A.leadingCoeff ^ 3 := by
  simp only [n1CubicZetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 3).natDegree = 3 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

theorem n1CubicThetaFace610_coeff_top (theta : k) (A : k[X]) :
    (n1CubicThetaFace610 theta A).coeff (2 * A.natDegree) =
      (1 / 24 * theta : k) * A.leadingCoeff ^ 2 := by
  simp only [n1CubicThetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 2).natDegree = 2 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallBetaRest610_chunk0 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  + (-(10 / 27 : k)) • (B * C * E)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  + (-(7 / 5184 * beta : k)) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  + (-(7 / 216 * beta : k)) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  + (-(35 / 432 * beta : k)) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallBetaRest610_chunk1 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  + (-(5 / 36 * delta : k)) • (B * D)
  + (-(5 / 72 * delta : k)) • C ^ 2
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  + (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallDeltaRest610_chunk0 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  + (-(10 / 27 : k)) • (B * C * E)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  + (-(5 / 36 * delta : k)) • (B * D)
  + (-(5 / 72 * delta : k)) • C ^ 2
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallDeltaRest610_chunk1 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallZetaRest610 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  + (-(10 / 27 : k)) • (B * C * E)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (1 / 12 * zeta : k) • (A * C)
  + (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicCDWallThetaRest610 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  + (-(10 / 27 : k)) • (B * C * E)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (1 / 3 * eta : k) • D
  + (1 / 6 * theta : k) • C

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallBetaRest610_chunk0 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  + (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallBetaRest610_chunk1 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)
  + (35 / 2592 * beta : k) • (A ^ 4 * C)
  + (-(7 / 1296 * beta : k)) • (A ^ 3 * B ^ 2)
  + (7 / 216 * beta : k) • (A ^ 3 * E)
  + (-(7 / 432 * beta : k)) • (A ^ 2 * B * D)
  + (49 / 864 * beta : k) • (A ^ 2 * C ^ 2)
  + (35 / 432 * beta : k) • (A * B ^ 2 * C)
  + (35 / 1728 * beta : k) • B ^ 4
  + (7 / 36 * beta : k) • (A * C * E)
  + (-(7 / 36 * beta : k)) • (A * D ^ 2)
  + (-(7 / 72 * beta : k)) • (B ^ 2 * E)
  + (-(7 / 18 * beta : k)) • (B * C * D)
  + (-(7 / 108 * beta : k)) • C ^ 3
  + (7 / 12 * beta : k) • E ^ 2
  + (7 / 2592 * delta : k) • A ^ 5

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallBetaRest610_chunk2 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 144 * delta : k) • (A ^ 3 * C)
  + (-(25 / 864 * delta : k)) • (A ^ 2 * B ^ 2)
  + (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  + (-(5 / 12 * delta : k)) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallBetaRest610_chunk3 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallDeltaRest610_chunk0 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  + (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallDeltaRest610_chunk1 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)
  + (5 / 144 * delta : k) • (A ^ 3 * C)
  + (-(25 / 864 * delta : k)) • (A ^ 2 * B ^ 2)
  + (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  + (-(5 / 12 * delta : k)) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallDeltaRest610_chunk2 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallZetaRest610_chunk0 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  + (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallZetaRest610_chunk1 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallThetaRest610_chunk0 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • (A ^ 2 * B ^ 2 * D)
  + (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicCDWallThetaRest610_chunk1 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallBetaRest610_chunk0 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  + (-(7 / 5184 * beta : k)) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  + (-(7 / 216 * beta : k)) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  + (-(35 / 432 * beta : k)) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallBetaRest610_chunk1 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  + (-(5 / 36 * delta : k)) • (B * D)
  + (-(5 / 72 * delta : k)) • C ^ 2
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  + (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallDeltaRest610_chunk0 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  + (-(5 / 36 * delta : k)) • (B * D)
  + (-(5 / 72 * delta : k)) • C ^ 2
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  + (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallDeltaRest610_chunk1 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallZetaRest610 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (1 / 12 * zeta : k) • (A * C)
  + (-(1 / 8 * zeta : k)) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallThetaRest610 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (1 / 3 * eta : k) • D
  + (1 / 6 * theta : k) • C

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallBetaRest610_chunk0 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)
  + (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallBetaRest610_chunk1 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (35 / 2592 * beta : k) • (A ^ 4 * C)
  + (-(7 / 1296 * beta : k)) • (A ^ 3 * B ^ 2)
  + (7 / 216 * beta : k) • (A ^ 3 * E)
  + (-(7 / 432 * beta : k)) • (A ^ 2 * B * D)
  + (49 / 864 * beta : k) • (A ^ 2 * C ^ 2)
  + (35 / 432 * beta : k) • (A * B ^ 2 * C)
  + (35 / 1728 * beta : k) • B ^ 4
  + (7 / 36 * beta : k) • (A * C * E)
  + (-(7 / 36 * beta : k)) • (A * D ^ 2)
  + (-(7 / 72 * beta : k)) • (B ^ 2 * E)
  + (-(7 / 18 * beta : k)) • (B * C * D)
  + (-(7 / 108 * beta : k)) • C ^ 3
  + (7 / 12 * beta : k) • E ^ 2
  + (7 / 2592 * delta : k) • A ^ 5
  + (5 / 144 * delta : k) • (A ^ 3 * C)
  + (-(25 / 864 * delta : k)) • (A ^ 2 * B ^ 2)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallBetaRest610_chunk2 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  + (-(5 / 12 * delta : k)) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallBetaRest610_chunk3 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallDeltaRest610_chunk0 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)
  + (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallDeltaRest610_chunk1 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 144 * delta : k) • (A ^ 3 * C)
  + (-(25 / 864 * delta : k)) • (A ^ 2 * B ^ 2)
  + (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  + (-(5 / 12 * delta : k)) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallDeltaRest610_chunk2 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallZetaRest610_chunk0 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)
  + (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallZetaRest610_chunk1 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallThetaRest610_chunk0 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)
  + (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN2CubicBCDEWallThetaRest610_chunk1 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallSplits610

variable {k : Type*} [Field k] [CharZero k]

theorem n2CubicSigmaFaceBCDE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (n2CubicSigmaFaceBCDE610 A B C D E).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      (-(5 / 81 : k)) *
        n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
          C.leadingCoeff D.leadingCoeff E.leadingCoeff *
        A.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, _, heq1, heq2, heq3⟩
  simp only [n2CubicSigmaFaceBCDE610, n1CubicSigmaInnerBCDE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hA2B2 : A ^ 2 * B ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hA2B2 hDne,
      natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne),
      natDegree_pow, natDegree_pow]
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_pow]
  have hABC : A * B * C ≠ 0 :=
    mul_ne_zero (mul_ne_zero hAne hBne) hCne
  have hdeg_ABCE : ((A * B * C * E)).natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hABC hEne,
      natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCE : ((A * B * C * E)).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff *
        E.leadingCoeff := by
    rw [← hdeg_ABCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_mul]
  have hAC2 : A * C ^ 2 ≠ 0 := mul_ne_zero hAne (pow_ne_zero 2 hCne)
  have hdeg_AC2D : ((A * C ^ 2 * D)).natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hAC2 hDne, natDegree_mul hAne (pow_ne_zero 2 hCne),
      natDegree_pow]
    omega
  have hcf_AC2D : ((A * C ^ 2 * D)).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  rw [hcf_A2B2D, hcf_ABCE, hcf_AC2D]
  ring

end CubicLoadWallSplits610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeCD610_n1BetaTop_of_deltaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have h7c : 7 * C.natDegree = 9 * A.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeCD610_n1BetaTop_of_zetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 12 * A.natDegree = 6 * A.natDegree + 6 * C.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeCD610_n1DeltaTop_of_zetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 12 * A.natDegree = 6 * A.natDegree + 6 * C.natDegree) :
    cubicN1DeltaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeCD610_n1BetaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeCD610_n1DeltaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    cubicN1DeltaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeCD610_n1ZetaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    cubicN1ZetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeBCDE610_n1BetaTop_of_deltaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeBCDE610_n1BetaTop_of_zetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeBCDE610_n1DeltaTop_of_zetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree) :
    cubicN1DeltaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeBCDE610_n1BetaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeBCDE610_n1DeltaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree) :
    cubicN1DeltaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeBCDE610_n1ZetaTop_of_thetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree) :
    cubicN1ZetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallDets610

variable {k : Type*} [Field k] [CharZero k]

theorem n1n2_beta_column_det610 (a x beta : k) (ha : a ≠ 0)
    (hz1 : x + (7 / 6912 * beta : k) * a ^ 5 = 0)
    (hz2 : -a * x + (35 / 41472 * beta : k) * a ^ 6 = 0) :
    beta = 0 := by
  have hcomb :
      a * (x + (7 / 6912 * beta : k) * a ^ 5) +
        (-a * x + (35 / 41472 * beta : k) * a ^ 6) = 0 := by
    rw [hz1, hz2, mul_zero, add_zero]
  have hlin : (77 / 41472 * beta : k) * a ^ 6 = 0 := by
    convert hcomb using 1
    ring
  have hden : (77 / 41472 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha6 : a ^ 6 ≠ 0 := pow_ne_zero _ ha
  rcases mul_eq_zero.mp hlin with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hden h).elim
    · exact h
  · exact (ha6 h).elim

end CubicLoadWallDets610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallDets610

variable {k : Type*} [Field k] [CharZero k]

theorem n1n2_delta_column_det610 (a x delta : k) (ha : a ≠ 0)
    (hz1 : x + (35 / 10368 * delta : k) * a ^ 4 = 0)
    (hz2 : -a * x + (7 / 2592 * delta : k) * a ^ 5 = 0) :
    delta = 0 := by
  have hcomb :
      a * (x + (35 / 10368 * delta : k) * a ^ 4) +
        (-a * x + (7 / 2592 * delta : k) * a ^ 5) = 0 := by
    rw [hz1, hz2, mul_zero, add_zero]
  have hlin : (7 / 1152 * delta : k) * a ^ 5 = 0 := by
    convert hcomb using 1
    ring
  have hden : (7 / 1152 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha5 : a ^ 5 ≠ 0 := pow_ne_zero _ ha
  rcases mul_eq_zero.mp hlin with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hden h).elim
    · exact h
  · exact (ha5 h).elim

end CubicLoadWallDets610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallDets610

variable {k : Type*} [Field k] [CharZero k]

theorem n1n2_zeta_column_det610 (a x zeta : k) (ha : a ≠ 0)
    (hz1 : x + (5 / 432 * zeta : k) * a ^ 3 = 0)
    (hz2 : -a * x + (5 / 576 * zeta : k) * a ^ 4 = 0) :
    zeta = 0 := by
  have hcomb :
      a * (x + (5 / 432 * zeta : k) * a ^ 3) +
        (-a * x + (5 / 576 * zeta : k) * a ^ 4) = 0 := by
    rw [hz1, hz2, mul_zero, add_zero]
  have hlin : (35 / 1728 * zeta : k) * a ^ 4 = 0 := by
    convert hcomb using 1
    ring
  have hden : (35 / 1728 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha4 : a ^ 4 ≠ 0 := pow_ne_zero _ ha
  rcases mul_eq_zero.mp hlin with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hden h).elim
    · exact h
  · exact (ha4 h).elim

end CubicLoadWallDets610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallDets610

variable {k : Type*} [Field k] [CharZero k]

theorem n1n2_theta_column_det610 (a x theta : k) (ha : a ≠ 0)
    (hz1 : x + (1 / 24 * theta : k) * a ^ 2 = 0)
    (hz2 : -a * x + (1 / 36 * theta : k) * a ^ 3 = 0) :
    theta = 0 := by
  have hcomb :
      a * (x + (1 / 24 * theta : k) * a ^ 2) +
        (-a * x + (1 / 36 * theta : k) * a ^ 3) = 0 := by
    rw [hz1, hz2, mul_zero, add_zero]
  have hlin : (5 / 72 * theta : k) * a ^ 3 = 0 := by
    convert hcomb using 1
    ring
  have hden : (5 / 72 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ha3 : a ^ 3 ≠ 0 := pow_ne_zero _ ha
  rcases mul_eq_zero.mp hlin with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hden h).elim
    · exact h
  · exact (ha3 h).elim

end CubicLoadWallDets610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDWallKills610

variable {k : Type*} [Field k] [CharZero k]

theorem CubicLoadSigmaConeCD610_A_ne
    {A B C D E : k[X]} (hcone : CubicLoadSigmaConeCD610 A B C D E) :
    A ≠ 0 := by
  intro h0
  have : A.natDegree = 0 := by simp [h0]
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
  omega

end CubicLoadCDWallKills610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadBCDEWallKills610

variable {k : Type*} [Field k] [CharZero k]

theorem CubicLoadSigmaConeBCDE610_A_ne
    {A B C D E : k[X]} (hcone : CubicLoadSigmaConeBCDE610 A B C D E) :
    A ≠ 0 := by
  intro h0
  have : A.natDegree = 0 := by simp [h0]
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
  omega

end CubicLoadBCDEWallKills610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem degreeZeroLambdaCubicNoSigmaCD610_eq_chamberRest
    (alpha epsilon eta : k) (A C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaCD610 0 alpha 0 0 epsilon 0 eta 0 A 0 C D E =
      lambdaChamberRestCD610 alpha epsilon eta A C D E := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  simp only [degreeZeroLambdaCubicNoSigmaCD610, lambdaChamberRestCD610,
    hpow2, hpow3, hpow4, zero_mul, mul_zero, zero_smul, smul_zero,
    add_zero, zero_add, sub_zero, neg_zero]
  all_goals module

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

def kappaChamberCD610 (alpha epsilon : k) (C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (2 / 3 * epsilon : k) • D

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

def omicronChamberCD610 (alpha epsilon eta : k) (A C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * E)
  + (-(5 / 27 : k)) • (C * D ^ 2)
  + (-(2 / 27 * alpha : k)) • (A * D ^ 2)
  + (-(4 / 81 * alpha : k)) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  + (-(1 / 9 * epsilon : k)) • C ^ 2
  + (1 / 3 * eta : k) • E

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem omicronC2Block_of_natDegree_E_eq_zero
    (epsilon : k) (C E : k[X])
    (he0 : E.natDegree = 0) :
    (-(5 / 27 : k)) • (C ^ 2 * E) + (-(1 / 9 * epsilon : k)) • C ^ 2 =
      ((-(5 / 27 : k)) * E.leadingCoeff +
        (-(1 / 9 * epsilon : k))) • C ^ 2 := by
  have hE : E = Polynomial.C E.leadingCoeff := by
    have hcoeff : E.coeff 0 = E.leadingCoeff := by
      rw [← coeff_natDegree, he0]
    rw [← hcoeff]
    exact eq_C_of_natDegree_eq_zero he0
  conv_lhs => rw [hE]
  rw [mul_comm (C ^ 2) (Polynomial.C _), smul_eq_C_mul, smul_eq_C_mul,
    ← mul_assoc, ← C_mul, ← add_mul, ← C_add, ← smul_eq_C_mul]

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

/-- On `e = c`, the ο top after the κ relation `e = -(2/5) α c` is
`(4/81) α c³` plus a multiple of the λ inner `3ad² + c³`. -/
theorem cubicChamber_ec_scalar_identity (a c d alpha e : k)
    (hrel : e = -((2 / 5 : k) * alpha * c)) :
    (-(5 / 27 : k)) * c ^ 2 * e
      + (-(2 / 27 * alpha : k)) * a * d ^ 2
      + (-(4 / 81 * alpha : k)) * c ^ 3
    = ((4 / 81 : k) * alpha) * c ^ 3
      + (-(2 / 81 : k) * alpha) * (3 * a * d ^ 2 + c ^ 3) := by
  rw [hrel]
  ring

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `lambdaChamberRestCD610` (5 monomials, 4 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_lambdaChamberRestCD610_eq_polyOf_dupfix
    (alpha epsilon eta : k) (A C D E : k[X]) :
    lambdaChamberRestCD610 alpha epsilon eta A C D E =
      Max11ReflectDeg.polyOf [A, C, D, E]
      [
      (5 / 9 : k), (4 / 9 * alpha : k), (2 / 9 * alpha : k),
      (2 / 3 * epsilon : k), (1 / 3 * eta : k)]
      [
      [0, 0, 0, 2], [0, 1, 0, 1], [0, 0, 2, 0], [0, 0, 0, 1],
      [0, 1, 0, 0]] := by
  simp only [lambdaChamberRestCD610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

/-- Two-face certificate on the CD chamber (CAS: `{3ad²+c³, cd²}`
saturates to `(1)` at `a,c,d ≠ 0`). -/
theorem cubicSigmaInner_CD_chamber_identity (a c d : k) :
    c * lambdaCubicSigmaInnerCD610 a c d
      - (3 * a) * omicronCubicSigmaInnerCD610 c d = c ^ 4 := by
  simp only [lambdaCubicSigmaInnerCD610, omicronCubicSigmaInnerCD610]
  ring

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

theorem n2CubicBetaFace610_coeff_top (beta : k) (A : k[X]) :
    (n2CubicBetaFace610 beta A).coeff (6 * A.natDegree) =
      (35 / 41472 * beta : k) * A.leadingCoeff ^ 6 := by
  simp only [n2CubicBetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

theorem n2CubicDeltaFace610_coeff_top (delta : k) (A : k[X]) :
    (n2CubicDeltaFace610 delta A).coeff (5 * A.natDegree) =
      (7 / 2592 * delta : k) * A.leadingCoeff ^ 5 := by
  simp only [n2CubicDeltaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 5).natDegree = 5 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

theorem n2CubicZetaFace610_coeff_top (zeta : k) (A : k[X]) :
    (n2CubicZetaFace610 zeta A).coeff (4 * A.natDegree) =
      (5 / 576 * zeta : k) * A.leadingCoeff ^ 4 := by
  simp only [n2CubicZetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 4).natDegree = 4 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

theorem n2CubicThetaFace610_coeff_top (theta : k) (A : k[X]) :
    (n2CubicThetaFace610 theta A).coeff (3 * A.natDegree) =
      (1 / 36 * theta : k) * A.leadingCoeff ^ 3 := by
  simp only [n2CubicThetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 3).natDegree = 3 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN1CubicCDWallBetaRest610 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN1CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN1CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicCDWallBetaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicCDWallBetaRest610_chunk0_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (20 / 243 : k), (-(10 / 27) : k),
      (-(5 / 27) : k), (4 / 243 * alpha : k), (-(4 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (35 / 2592 * beta : k),
      (-(7 / 5184 * beta) : k), (7 / 144 * beta : k), (-(7 / 216 * beta) : k),
      (7 / 432 * beta : k), (-(35 / 432 * beta) : k), (7 / 36 * beta : k),
      (7 / 72 * beta : k)]
      [
      [1, 2, 0, 1, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0]] := by
  simp only [degreeZeroN1CubicCDWallBetaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicCDWallBetaRest610_chunk1` (14 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicCDWallBetaRest610_chunk1_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (35 / 10368 * delta : k), (5 / 144 * delta : k), (5 / 432 * delta : k),
      (5 / 36 * delta : k), (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k),
      (-(2 / 9 * epsilon) : k), (5 / 432 * zeta : k), (1 / 12 * zeta : k),
      (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 24 * theta : k), (1 / 6 * theta : k)]
      [
      [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1],
      [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0],
      [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0],
      [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicCDWallBetaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN1CubicCDWallDeltaRest610 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN1CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN1CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicCDWallDeltaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicCDWallDeltaRest610_chunk0_eq_polyOf
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (20 / 243 : k), (-(10 / 27) : k),
      (-(5 / 27) : k), (4 / 243 * alpha : k), (-(4 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (5 / 144 * delta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 36 * delta) : k),
      (-(5 / 72 * delta) : k), (-(2 / 9 * epsilon) : k), (5 / 432 * zeta : k),
      (1 / 12 * zeta : k)]
      [
      [1, 2, 0, 1, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicCDWallDeltaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicCDWallDeltaRest610_chunk1` (5 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicCDWallDeltaRest610_chunk1_eq_polyOf
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 24 * theta : k), (1 / 6 * theta : k)]
      [
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicCDWallDeltaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
