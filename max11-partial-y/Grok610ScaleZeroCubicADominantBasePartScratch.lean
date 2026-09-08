import Grok610ScaleZeroCubicConesScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch
import Max11SpeedReflectDegLibScratch

/-! # Scale-zero cubic A-dominant Stage B+C, for normalized `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicConesScratch`.  That file ends at
`normalized610ScaleZero_cubicADominantResidual`: the source loads the
cubic letters `A,B,C,D,E` on the single cone `R = {A}`.

CAS jobs `scripts/derive_610_scale_zero_cubic_adominant.py` and
`scripts/derive_610_scale_zero_cubic_balanced.py` analyse the σ-grading
inside `R = {A}`.  Thirteen argmin cones are empty, `{C,D}` closes by
the σ-7 part of `N₁ = μ + (A/6) κ`, and the balanced cell dies by
`⟨G1,G2,G3,G4⟩`.  Odd loads vanish on the competing-load wall by the
pure-`A` column of `N₁`.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.  Untracked working note.
-/

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

/-! ## σ-argmin cones inside `R = {A}` -/

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
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



set_option maxHeartbeats 64000000 in
def cubicLoadCompetes610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 3 * B.natDegree ∧
    11 * A.natDegree ≥ 6 * C.natDegree ∧
    9 * A.natDegree ≥ 4 * D.natDegree ∧
    11 * A.natDegree ≥ 4 * E.natDegree


end CubicSigmaCones610

/-! ## The combination `N₁ = μ + (A/6) κ` -/

section CubicN1_610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
def degreeZeroN1Cubic610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 81 : k), (20 / 243 : k), (-(10 / 27) : k),
      (-(5 / 27) : k), (-(5 / 27) : k), (77 / 248832 * l : k),
      (35 / 6912 * l : k), (-(1 / 1152 * l) : k), (5 / 288 * l : k),
      (-(1 / 96 * l) : k), (1 / 64 * l : k), (1 / 32 * l : k),
      (3 / 128 * l : k), (1 / 8 * l : k), (-(1 / 16 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 8 * l) : k), (-(1 / 16 * l) : k),
      (3 / 8 * l : k), (4 / 243 * alpha : k), (-(4 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (7 / 6912 * beta : k),
      (35 / 2592 * beta : k), (-(7 / 5184 * beta) : k), (7 / 144 * beta : k),
      (-(7 / 216 * beta) : k), (7 / 432 * beta : k), (-(35 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 72 * beta : k), (35 / 10368 * delta : k),
      (5 / 144 * delta : k), (5 / 432 * delta : k), (5 / 36 * delta : k),
      (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(2 / 9 * epsilon) : k),
      (5 / 432 * zeta : k), (1 / 12 * zeta : k), (-(1 / 8 * zeta) : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 24 * theta : k),
      (1 / 6 * theta : k)]
    [
      [1, 2, 0, 1, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [0, 0, 2, 1, 0], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0],
      [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0],
      [0, 4, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [1, 3, 0, 0, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1],
      [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0],
      [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0],
      [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]]




set_option maxHeartbeats 64000000 in
def n1CubicSigma7Face610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (C ^ 2 * D)


set_option maxHeartbeats 64000000 in
def n1CubicLFace610 (l : k) (A : k[X]) : k[X] :=
  (77 / 248832 * l : k) • A ^ 6


set_option maxHeartbeats 64000000 in
def degreeZeroN1CubicNoL610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 81 : k), (20 / 243 : k), (-(10 / 27) : k),
      (-(5 / 27) : k), (-(5 / 27) : k), (35 / 6912 * l : k),
      (-(1 / 1152 * l) : k), (5 / 288 * l : k), (-(1 / 96 * l) : k),
      (1 / 64 * l : k), (1 / 32 * l : k), (3 / 128 * l : k),
      (1 / 8 * l : k), (-(1 / 16 * l) : k), (-(3 / 16 * l) : k),
      (-(3 / 8 * l) : k), (-(1 / 16 * l) : k), (3 / 8 * l : k),
      (4 / 243 * alpha : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
      (4 / 9 * alpha : k), (7 / 6912 * beta : k), (35 / 2592 * beta : k),
      (-(7 / 5184 * beta) : k), (7 / 144 * beta : k), (-(7 / 216 * beta) : k),
      (7 / 432 * beta : k), (-(35 / 432 * beta) : k), (7 / 36 * beta : k),
      (7 / 72 * beta : k), (35 / 10368 * delta : k), (5 / 144 * delta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 36 * delta) : k),
      (-(5 / 72 * delta) : k), (-(2 / 9 * epsilon) : k), (5 / 432 * zeta : k),
      (1 / 12 * zeta : k), (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 24 * theta : k), (1 / 6 * theta : k)]
    [
      [1, 2, 0, 1, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [0, 0, 2, 1, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
      [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [1, 3, 0, 0, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0]]



end CubicN1_610

/-! ## The 13 empty σ-argmin cones -/

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

/- σ-cone B -/

set_option maxHeartbeats 64000000 in
def kappaCubicSigmaFaceB610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaCubicNoSigmaB610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 27) : k), (-(5 / 27) : k), (10 / 9 : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l) : k),
      (1 / 16 * l : k), (-(1 / 8 * l) : k), (1 / 16 * l : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha) : k), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta) : k),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]





/- σ-cone C -/

set_option maxHeartbeats 64000000 in
def lambdaCubicSigmaFaceC610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • C ^ 3


set_option maxHeartbeats 64000000 in
def degreeZeroLambdaCubicNoSigmaC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
      (-(5 / 27) : k), (-(10 / 27) : k), (5 / 9 : k),
      (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k), (-(1 / 96 * l) : k),
      (1 / 32 * l : k), (-(1 / 8 * l) : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 16 * l) : k), (3 / 4 * l : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k),
      (-(7 / 216 * beta) : k), (-(35 / 1296 * beta) : k), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k),
      (-(5 / 36 * delta) : k), (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta) : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
    [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]





/- σ-cone D -/

set_option maxHeartbeats 64000000 in
def lambdaCubicSigmaFaceD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D ^ 2)


set_option maxHeartbeats 64000000 in
def degreeZeroLambdaCubicNoSigmaD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
      (-(10 / 27) : k), (-(5 / 81) : k), (5 / 9 : k),
      (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k), (-(1 / 96 * l) : k),
      (1 / 32 * l : k), (-(1 / 8 * l) : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 16 * l) : k), (3 / 4 * l : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k),
      (-(7 / 216 * beta) : k), (-(35 / 1296 * beta) : k), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k),
      (-(5 / 36 * delta) : k), (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta) : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
    [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]





/- σ-cone E -/

set_option maxHeartbeats 64000000 in
def lambdaCubicSigmaFaceE610 (A B C D E : k[X]) : k[X] :=
  (5 / 9 : k) • E ^ 2


set_option maxHeartbeats 64000000 in
def degreeZeroLambdaCubicNoSigmaE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
      (-(5 / 27) : k), (-(10 / 27) : k), (-(5 / 81) : k),
      (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k), (-(1 / 96 * l) : k),
      (1 / 32 * l : k), (-(1 / 8 * l) : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 16 * l) : k), (3 / 4 * l : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k),
      (-(7 / 216 * beta) : k), (-(35 / 1296 * beta) : k), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k),
      (-(5 / 36 * delta) : k), (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta) : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
    [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]





/- σ-cone BC -/

set_option maxHeartbeats 64000000 in
def kappaCubicSigmaInnerBC610 (a b c : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b * c ^ 2


set_option maxHeartbeats 64000000 in
def lambdaCubicSigmaInnerBC610 (a b c : k) : k :=
  5 * a * b ^ 2 * c + (-5 : k) * c ^ 3



set_option maxHeartbeats 64000000 in
def kappaCubicSigmaFaceBC610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaCubicNoSigmaBC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 27) : k), (10 / 9 : k), (7 / 6912 * l : k),
      (5 / 288 * l : k), (-(1 / 192 * l) : k), (1 / 16 * l : k),
      (-(1 / 8 * l) : k), (1 / 16 * l : k), (-(3 / 16 * l) : k),
      (3 / 4 * l : k), (3 / 8 * l : k), (-(4 / 81 * alpha) : k),
      (4 / 9 * alpha : k), (4 / 9 * alpha : k), (35 / 10368 * beta : k),
      (7 / 144 * beta : k), (-(7 / 432 * beta) : k), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (7 / 72 * beta : k), (5 / 432 * delta : k),
      (5 / 36 * delta : k), (-(5 / 72 * delta) : k), (5 / 6 * delta : k),
      (2 / 3 * epsilon : k), (1 / 24 * zeta : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [0, 2, 0, 1, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0],
      [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0],
      [1, 0, 0, 0, 0]]





set_option maxHeartbeats 64000000 in
def lambdaCubicSigmaFaceBC610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 81 : k) • C ^ 3


set_option maxHeartbeats 64000000 in
def degreeZeroLambdaCubicNoSigmaBC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k),
      (-(10 / 27) : k), (5 / 9 : k), (-(5 / 6912 * l) : k),
      (-(1 / 288 * l) : k), (-(1 / 96 * l) : k), (1 / 32 * l : k),
      (-(1 / 8 * l) : k), (-(1 / 8 * l) : k), (-(3 / 16 * l) : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (-(4 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (2 / 9 * alpha : k),
      (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k), (-(7 / 216 * beta) : k),
      (-(35 / 1296 * beta) : k), (7 / 36 * beta : k), (7 / 36 * beta : k),
      (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k), (-(5 / 36 * delta) : k),
      (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k), (-(1 / 12 * zeta) : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0],
      [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0],
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0],
      [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0]]






/- σ-cone BD -/

set_option maxHeartbeats 64000000 in
def kappaCubicSigmaFaceBD610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaCubicNoSigmaBD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 27) : k), (-(5 / 27) : k), (10 / 9 : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l) : k),
      (1 / 16 * l : k), (-(1 / 8 * l) : k), (1 / 16 * l : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha) : k), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta) : k),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]





/- σ-cone BE -/

set_option maxHeartbeats 64000000 in
def kappaCubicSigmaFaceBE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaCubicNoSigmaBE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 27) : k), (-(5 / 27) : k), (10 / 9 : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l) : k),
      (1 / 16 * l : k), (-(1 / 8 * l) : k), (1 / 16 * l : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha) : k), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta) : k),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]





/- σ-cone CE -/

set_option maxHeartbeats 64000000 in
def omicronCubicSigmaFaceCE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * E)


set_option maxHeartbeats 64000000 in
def degreeZeroOmicronCubicNoSigmaCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 486) : k), (5 / 81 : k), (10 / 81 : k),
      (25 / 486 : k), (5 / 54 : k), (-(5 / 27) : k),
      (-(5 / 27) : k), (-(5 / 6912 * l) : k), (1 / 864 * l : k),
      (-(1 / 288 * l) : k), (-(1 / 96 * l) : k), (7 / 96 * l : k),
      (1 / 24 * l : k), (1 / 16 * l : k), (-(1 / 8 * l) : k),
      (-(1 / 4 * l) : k), (-(1 / 8 * l) : k), (-(3 / 16 * l) : k),
      (4 / 81 * alpha : k), (1 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
      (-(2 / 27 * alpha) : k), (-(2 / 9 * alpha) : k), (-(4 / 81 * alpha) : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (7 / 1296 * beta : k),
      (7 / 648 * beta : k), (-(7 / 216 * beta) : k), (-(7 / 144 * beta) : k),
      (-(7 / 108 * beta) : k), (7 / 36 * beta : k), (-(5 / 432 * delta) : k),
      (5 / 108 * delta : k), (5 / 324 * delta : k), (-(5 / 36 * delta) : k),
      (1 / 27 * epsilon : k), (-(1 / 9 * epsilon) : k), (-(1 / 9 * epsilon) : k),
      (-(1 / 12 * zeta) : k), (-(1 / 6 * zeta) : k), (-(1 / 18 * eta) : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [1, 4, 0, 0, 0], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [0, 3, 0, 1, 0],
      [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 1, 2, 0], [4, 0, 0, 1, 0],
      [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]]





/- σ-cone DE -/

set_option maxHeartbeats 64000000 in
def kappaCubicSigmaFaceDE610 (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaCubicNoSigmaDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l) : k),
      (1 / 16 * l : k), (-(1 / 8 * l) : k), (1 / 16 * l : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha) : k), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta) : k),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]





/- σ-cone BCD -/

set_option maxHeartbeats 64000000 in
def omicronCubicSigmaFaceBCD610 (A B C D E : k[X]) : k[X] :=
  (10 / 81 : k) • (A * B * C * D)


set_option maxHeartbeats 64000000 in
def degreeZeroOmicronCubicNoSigmaBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 486) : k), (5 / 81 : k), (25 / 486 : k),
      (5 / 54 : k), (-(5 / 27) : k), (-(5 / 27) : k),
      (-(5 / 27) : k), (-(5 / 6912 * l) : k), (1 / 864 * l : k),
      (-(1 / 288 * l) : k), (-(1 / 96 * l) : k), (7 / 96 * l : k),
      (1 / 24 * l : k), (1 / 16 * l : k), (-(1 / 8 * l) : k),
      (-(1 / 4 * l) : k), (-(1 / 8 * l) : k), (-(3 / 16 * l) : k),
      (4 / 81 * alpha : k), (1 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
      (-(2 / 27 * alpha) : k), (-(2 / 9 * alpha) : k), (-(4 / 81 * alpha) : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (7 / 1296 * beta : k),
      (7 / 648 * beta : k), (-(7 / 216 * beta) : k), (-(7 / 144 * beta) : k),
      (-(7 / 108 * beta) : k), (7 / 36 * beta : k), (-(5 / 432 * delta) : k),
      (5 / 108 * delta : k), (5 / 324 * delta : k), (-(5 / 36 * delta) : k),
      (1 / 27 * epsilon : k), (-(1 / 9 * epsilon) : k), (-(1 / 9 * epsilon) : k),
      (-(1 / 12 * zeta) : k), (-(1 / 6 * zeta) : k), (-(1 / 18 * eta) : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [1, 4, 0, 0, 0], [1, 2, 0, 0, 1], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0],
      [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [4, 0, 0, 1, 0],
      [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]]





/- σ-cone BCE -/

set_option maxHeartbeats 64000000 in
def kappaCubicSigmaInnerBCE610 (a b c e : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b * c ^ 2


set_option maxHeartbeats 64000000 in
def lambdaCubicSigmaInnerBCE610 (a b c e : k) : k :=
  5 * a * b ^ 2 * c + (-5 : k) * c ^ 3 + 45 * e ^ 2


set_option maxHeartbeats 64000000 in
def omicronCubicSigmaInnerBCE610 (a b c e : k) : k :=
  5 * a * b ^ 2 * e + (-15 : k) * c ^ 2 * e



set_option maxHeartbeats 64000000 in
def kappaCubicSigmaFaceBCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaCubicNoSigmaBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 27) : k), (10 / 9 : k), (7 / 6912 * l : k),
      (5 / 288 * l : k), (-(1 / 192 * l) : k), (1 / 16 * l : k),
      (-(1 / 8 * l) : k), (1 / 16 * l : k), (-(3 / 16 * l) : k),
      (3 / 4 * l : k), (3 / 8 * l : k), (-(4 / 81 * alpha) : k),
      (4 / 9 * alpha : k), (4 / 9 * alpha : k), (35 / 10368 * beta : k),
      (7 / 144 * beta : k), (-(7 / 432 * beta) : k), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (7 / 72 * beta : k), (5 / 432 * delta : k),
      (5 / 36 * delta : k), (-(5 / 72 * delta) : k), (5 / 6 * delta : k),
      (2 / 3 * epsilon : k), (1 / 24 * zeta : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [0, 2, 0, 1, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0],
      [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0],
      [1, 0, 0, 0, 0]]





set_option maxHeartbeats 64000000 in
def lambdaCubicSigmaFaceBCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2


set_option maxHeartbeats 64000000 in
def degreeZeroLambdaCubicNoSigmaBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k),
      (-(10 / 27) : k), (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k),
      (-(1 / 96 * l) : k), (1 / 32 * l : k), (-(1 / 8 * l) : k),
      (-(1 / 8 * l) : k), (-(3 / 16 * l) : k), (-(3 / 16 * l) : k),
      (3 / 4 * l : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
      (4 / 9 * alpha : k), (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k),
      (-(7 / 432 * beta) : k), (-(7 / 216 * beta) : k), (-(35 / 1296 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (-(5 / 432 * delta) : k),
      (-(5 / 36 * delta) : k), (-(5 / 36 * delta) : k), (-(1 / 9 * epsilon) : k),
      (2 / 3 * epsilon : k), (-(1 / 12 * zeta) : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
      [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
      [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0],
      [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]





set_option maxHeartbeats 64000000 in
def omicronCubicSigmaFaceBCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * E)
  - (5 / 27 : k) • (C ^ 2 * E)


set_option maxHeartbeats 64000000 in
def degreeZeroOmicronCubicNoSigmaBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 486) : k), (10 / 81 : k), (25 / 486 : k),
      (5 / 54 : k), (-(5 / 27) : k), (-(5 / 27) : k),
      (-(5 / 6912 * l) : k), (1 / 864 * l : k), (-(1 / 288 * l) : k),
      (-(1 / 96 * l) : k), (7 / 96 * l : k), (1 / 24 * l : k),
      (1 / 16 * l : k), (-(1 / 8 * l) : k), (-(1 / 4 * l) : k),
      (-(1 / 8 * l) : k), (-(3 / 16 * l) : k), (4 / 81 * alpha : k),
      (1 / 81 * alpha : k), (-(2 / 27 * alpha) : k), (-(2 / 27 * alpha) : k),
      (-(2 / 9 * alpha) : k), (-(4 / 81 * alpha) : k), (2 / 9 * alpha : k),
      (-(7 / 2592 * beta) : k), (7 / 1296 * beta : k), (7 / 648 * beta : k),
      (-(7 / 216 * beta) : k), (-(7 / 144 * beta) : k), (-(7 / 108 * beta) : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta) : k), (5 / 108 * delta : k),
      (5 / 324 * delta : k), (-(5 / 36 * delta) : k), (1 / 27 * epsilon : k),
      (-(1 / 9 * epsilon) : k), (-(1 / 9 * epsilon) : k), (-(1 / 12 * zeta) : k),
      (-(1 / 6 * zeta) : k), (-(1 / 18 * eta) : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
    [
      [1, 4, 0, 0, 0], [1, 1, 1, 1, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0],
      [0, 1, 0, 1, 1], [0, 0, 1, 2, 0], [4, 0, 0, 1, 0], [3, 1, 1, 0, 0],
      [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0],
      [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0],
      [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
      [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [2, 0, 0, 1, 0],
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [1, 2, 0, 0, 0],
      [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]]






/- σ-cone BDE -/

set_option maxHeartbeats 64000000 in
def omicronCubicSigmaFaceBDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * E)


set_option maxHeartbeats 64000000 in
def degreeZeroOmicronCubicNoSigmaBDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 486) : k), (10 / 81 : k), (25 / 486 : k),
      (5 / 54 : k), (-(5 / 27) : k), (-(5 / 27) : k),
      (-(5 / 27) : k), (-(5 / 6912 * l) : k), (1 / 864 * l : k),
      (-(1 / 288 * l) : k), (-(1 / 96 * l) : k), (7 / 96 * l : k),
      (1 / 24 * l : k), (1 / 16 * l : k), (-(1 / 8 * l) : k),
      (-(1 / 4 * l) : k), (-(1 / 8 * l) : k), (-(3 / 16 * l) : k),
      (4 / 81 * alpha : k), (1 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
      (-(2 / 27 * alpha) : k), (-(2 / 9 * alpha) : k), (-(4 / 81 * alpha) : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (7 / 1296 * beta : k),
      (7 / 648 * beta : k), (-(7 / 216 * beta) : k), (-(7 / 144 * beta) : k),
      (-(7 / 108 * beta) : k), (7 / 36 * beta : k), (-(5 / 432 * delta) : k),
      (5 / 108 * delta : k), (5 / 324 * delta : k), (-(5 / 36 * delta) : k),
      (1 / 27 * epsilon : k), (-(1 / 9 * epsilon) : k), (-(1 / 9 * epsilon) : k),
      (-(1 / 12 * zeta) : k), (-(1 / 6 * zeta) : k), (-(1 / 18 * eta) : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [1, 4, 0, 0, 0], [1, 1, 1, 1, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0],
      [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [4, 0, 0, 1, 0],
      [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]]





/- σ-cone CDE -/

set_option maxHeartbeats 64000000 in
def kappaCubicSigmaFaceCDE610 (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaCubicNoSigmaCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l) : k),
      (1 / 16 * l : k), (-(1 / 8 * l) : k), (1 / 16 * l : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha) : k), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta) : k),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]





end CubicSigmaKills610

/-! ## The `{C,D}` residual, closed by `N₁` -/

section CubicSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
def lambdaCubicSigmaFaceCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D ^ 2)
  - (5 / 81 : k) • C ^ 3


set_option maxHeartbeats 64000000 in
def degreeZeroLambdaCubicNoSigmaCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
      (-(10 / 27) : k), (5 / 9 : k), (-(5 / 6912 * l) : k),
      (-(1 / 288 * l) : k), (-(1 / 96 * l) : k), (1 / 32 * l : k),
      (-(1 / 8 * l) : k), (-(1 / 8 * l) : k), (-(3 / 16 * l) : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (-(4 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (2 / 9 * alpha : k),
      (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k), (-(7 / 216 * beta) : k),
      (-(35 / 1296 * beta) : k), (7 / 36 * beta : k), (7 / 36 * beta : k),
      (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k), (-(5 / 36 * delta) : k),
      (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k), (-(1 / 12 * zeta) : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0],
      [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0],
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0],
      [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0]]




set_option maxHeartbeats 64000000 in
def n1CubicSigmaFaceCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
def degreeZeroN1CubicNoSigmaCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 81 : k), (20 / 243 : k), (-(10 / 27) : k),
      (-(5 / 27) : k), (77 / 248832 * l : k), (35 / 6912 * l : k),
      (-(1 / 1152 * l) : k), (5 / 288 * l : k), (-(1 / 96 * l) : k),
      (1 / 64 * l : k), (1 / 32 * l : k), (3 / 128 * l : k),
      (1 / 8 * l : k), (-(1 / 16 * l) : k), (-(3 / 16 * l) : k),
      (-(3 / 8 * l) : k), (-(1 / 16 * l) : k), (3 / 8 * l : k),
      (4 / 243 * alpha : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
      (4 / 9 * alpha : k), (7 / 6912 * beta : k), (35 / 2592 * beta : k),
      (-(7 / 5184 * beta) : k), (7 / 144 * beta : k), (-(7 / 216 * beta) : k),
      (7 / 432 * beta : k), (-(35 / 432 * beta) : k), (7 / 36 * beta : k),
      (7 / 72 * beta : k), (35 / 10368 * delta : k), (5 / 144 * delta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 36 * delta) : k),
      (-(5 / 72 * delta) : k), (-(2 / 9 * epsilon) : k), (5 / 432 * zeta : k),
      (1 / 12 * zeta : k), (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 24 * theta : k), (1 / 6 * theta : k)]
    [
      [1, 2, 0, 1, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
      [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [1, 3, 0, 0, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0]]


end CubicSigmaCD610

/-! ## The balanced cell -/

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
def kappaCubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaCubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 27) : k), (7 / 6912 * l : k), (5 / 288 * l : k),
      (-(1 / 192 * l) : k), (1 / 16 * l : k), (-(1 / 8 * l) : k),
      (1 / 16 * l : k), (-(3 / 16 * l) : k), (3 / 4 * l : k),
      (3 / 8 * l : k), (-(4 / 81 * alpha) : k), (4 / 9 * alpha : k),
      (4 / 9 * alpha : k), (35 / 10368 * beta : k), (7 / 144 * beta : k),
      (-(7 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 36 * beta : k),
      (7 / 72 * beta : k), (5 / 432 * delta : k), (5 / 36 * delta : k),
      (-(5 / 72 * delta) : k), (5 / 6 * delta : k), (2 / 3 * epsilon : k),
      (1 / 24 * zeta : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
    [
      [0, 2, 0, 1, 0], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
      [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
      [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [3, 0, 0, 0, 0],
      [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0],
      [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]




set_option maxHeartbeats 64000000 in
def lambdaCubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2


set_option maxHeartbeats 64000000 in
def degreeZeroLambdaCubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (5 / 243 : k), (-(5 / 27) : k), (-(10 / 27) : k),
      (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k), (-(1 / 96 * l) : k),
      (1 / 32 * l : k), (-(1 / 8 * l) : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 16 * l) : k), (3 / 4 * l : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k),
      (-(7 / 216 * beta) : k), (-(35 / 1296 * beta) : k), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k),
      (-(5 / 36 * delta) : k), (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta) : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
    [
      [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [4, 1, 0, 0, 0],
      [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1],
      [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
      [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0],
      [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]




set_option maxHeartbeats 64000000 in
def omicronCubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * E)
  + (10 / 81 : k) • (A * B * C * D)
  - (5 / 27 : k) • (C ^ 2 * E)


set_option maxHeartbeats 64000000 in
def degreeZeroOmicronCubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (-(5 / 486) : k), (25 / 486 : k), (5 / 54 : k),
      (-(5 / 27) : k), (-(5 / 27) : k), (-(5 / 6912 * l) : k),
      (1 / 864 * l : k), (-(1 / 288 * l) : k), (-(1 / 96 * l) : k),
      (7 / 96 * l : k), (1 / 24 * l : k), (1 / 16 * l : k),
      (-(1 / 8 * l) : k), (-(1 / 4 * l) : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (4 / 81 * alpha : k), (1 / 81 * alpha : k),
      (-(2 / 27 * alpha) : k), (-(2 / 27 * alpha) : k), (-(2 / 9 * alpha) : k),
      (-(4 / 81 * alpha) : k), (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k),
      (7 / 1296 * beta : k), (7 / 648 * beta : k), (-(7 / 216 * beta) : k),
      (-(7 / 144 * beta) : k), (-(7 / 108 * beta) : k), (7 / 36 * beta : k),
      (-(5 / 432 * delta) : k), (5 / 108 * delta : k), (5 / 324 * delta : k),
      (-(5 / 36 * delta) : k), (1 / 27 * epsilon : k), (-(1 / 9 * epsilon) : k),
      (-(1 / 9 * epsilon) : k), (-(1 / 12 * zeta) : k), (-(1 / 6 * zeta) : k),
      (-(1 / 18 * eta) : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
    [
      [1, 4, 0, 0, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1],
      [0, 0, 1, 2, 0], [4, 0, 0, 1, 0], [3, 1, 1, 0, 0], [2, 3, 0, 0, 0],
      [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
      [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0],
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
      [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]]




set_option maxHeartbeats 64000000 in
def n1CubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
def degreeZeroN1CubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
      (20 / 243 : k), (-(5 / 27) : k), (77 / 248832 * l : k),
      (35 / 6912 * l : k), (-(1 / 1152 * l) : k), (5 / 288 * l : k),
      (-(1 / 96 * l) : k), (1 / 64 * l : k), (1 / 32 * l : k),
      (3 / 128 * l : k), (1 / 8 * l : k), (-(1 / 16 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 8 * l) : k), (-(1 / 16 * l) : k),
      (3 / 8 * l : k), (4 / 243 * alpha : k), (-(4 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (7 / 6912 * beta : k),
      (35 / 2592 * beta : k), (-(7 / 5184 * beta) : k), (7 / 144 * beta : k),
      (-(7 / 216 * beta) : k), (7 / 432 * beta : k), (-(35 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 72 * beta : k), (35 / 10368 * delta : k),
      (5 / 144 * delta : k), (5 / 432 * delta : k), (5 / 36 * delta : k),
      (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(2 / 9 * epsilon) : k),
      (5 / 432 * zeta : k), (1 / 12 * zeta : k), (-(1 / 8 * zeta) : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 24 * theta : k),
      (1 / 6 * theta : k)]
    [
      [0, 3, 1, 0, 0], [0, 1, 0, 2, 0], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0],
      [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0],
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 2, 0],
      [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1],
      [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
      [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
      [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [0, 1, 1, 0, 0],
      [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]]


set_option maxHeartbeats 64000000 in
def kappaCubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 3 + (-9 : k) * b * c ^ 2 + 54 * d * e

set_option maxHeartbeats 64000000 in
def lambdaCubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 2 * c + (-3 : k) * a * d ^ 2 - c ^ 3 + 9 * e ^ 2

set_option maxHeartbeats 64000000 in
def omicronCubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 2 * e + 2 * a * b * c * d + (-3 : k) * c ^ 2 * e

set_option maxHeartbeats 64000000 in
def n1CubicSigmaInnerBCDE610 (a b c d e : k) : k :=
  a * b ^ 2 * d + (-6 : k) * b * c * e + (-3 : k) * c ^ 2 * d


end CubicBalanced610


/-! ## All of `B,C,D,E` vanish -/

section CubicAllLettersZero610

variable {k : Type*} [Field k] [CharZero k]



end CubicAllLettersZero610


/-! ## B0: competing odd loads vanish -/

section CubicLoadB0_610

variable {k : Type*} [Field k] [CharZero k]



set_option maxHeartbeats 64000000 in
/-- β-column of `N₁` is `7/6912 · β · A⁵`.  Competes when `6 Θ ≥ 3 ρ`. -/
def cubicLoadCompetesBeta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 9 * B.natDegree ∧
    11 * A.natDegree ≥ 18 * C.natDegree ∧
    3 * A.natDegree ≥ 4 * D.natDegree ∧
    11 * A.natDegree ≥ 12 * E.natDegree


set_option maxHeartbeats 64000000 in
/-- δ-column of `N₁` is `35/10368 · δ · A⁴`.  Competes when `6 Θ ≥ 5 ρ`. -/
def cubicLoadCompetesDelta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 15 * B.natDegree ∧
    11 * A.natDegree ≥ 30 * C.natDegree ∧
    9 * A.natDegree ≥ 20 * D.natDegree ∧
    11 * A.natDegree ≥ 20 * E.natDegree


set_option maxHeartbeats 64000000 in
/-- ζ-column of `N₁` is `5/432 · ζ · A³`.  Competes when `6 Θ ≥ 7 ρ`. -/
def cubicLoadCompetesZeta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 21 * B.natDegree ∧
    11 * A.natDegree ≥ 42 * C.natDegree ∧
    9 * A.natDegree ≥ 28 * D.natDegree ∧
    11 * A.natDegree ≥ 28 * E.natDegree


set_option maxHeartbeats 64000000 in
/-- θ-column of `N₁` is `1/24 · θ · A²`.  Competes when `6 Θ ≥ 9 ρ`. -/
def cubicLoadCompetesTheta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 27 * B.natDegree ∧
    11 * A.natDegree ≥ 54 * C.natDegree ∧
    9 * A.natDegree ≥ 36 * D.natDegree ∧
    11 * A.natDegree ≥ 36 * E.natDegree


end CubicLoadB0_610



/-! ## Stage B residual: A-dominant minus the killed σ-cones -/

section CubicAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]


end CubicAssembly610


end Max11DegreeRoutes
