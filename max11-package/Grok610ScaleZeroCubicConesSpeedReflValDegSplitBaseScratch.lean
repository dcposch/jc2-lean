import Grok610ScaleZeroConeKappaMuScratch
import Max11SpeedReflectDegLibScratch

/-! # Scale-zero cubic coordinates, Stage A, for normalized `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroConeKappaMuScratch` on the constant core
`H = (C t)²`.  That file supplies `t ≠ 0`, `j/t ≠ 0`, `H = (C t)²`,
`derivative (degreeZeroPrimitivePolynomial610 …) = C (j/t)` and
`natDegree = 0` for `λ, κ, μ, ο` as
`normalized610ScaleZero_coneKappaMuResidual`.  Its leftover cone
conjuncts are not used.

CAS jobs `scripts/derive_610_scale_zero_cubic_coordinates.py` and
`scripts/derive_610_scale_zero_cubic_cones.py` transcribe the five
isobaric pullbacks, substitute the graded triangular automorphism
`C0 = C + A^2/3`, `D0 = D + AB/3`, `E0 = E + AC/3 + A^3/27`, and test
every nonempty argmax cone `R ⊆ {A,B,C,D,E}` by saturated Gröbner.
Thirty cones are empty; the survivor is the single cone `R = {A}`.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut, no closure overclaim.  Untracked
working note.  No tracked file was edited.
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


/-! ## Cubic coordinates -/

section CubicCoordinates610

variable {k : Type*} [Field k] [CharZero k]

def cubicC610 (A C0 : k[X]) : k[X] :=
  C0 - (1 / 3 : k) • A ^ 2

def cubicD610 (A B D0 : k[X]) : k[X] :=
  D0 - (1 / 3 : k) • (A * B)

def cubicE610 (A C0 E0 : k[X]) : k[X] :=
  E0 - (1 / 3 : k) • (A * C0) + (2 / 27 : k) • A ^ 3

end CubicCoordinates610


/-! ## Cubic first integrals -/

section CubicIntegrals610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubic610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)
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


set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubic610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
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


set_option maxHeartbeats 32000000 in
def degreeZeroMuCubic610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 54 : k) • (A * B ^ 2 * D)
  + (5 / 162 : k) • (A * B * C ^ 2)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (5 / 27 : k) • (A * D * E)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)
  + (35 / 248832 * l : k) • A ^ 6
  + (5 / 2304 * l : k) • (A ^ 4 * C)
  + (1 / 144 * l : k) • (A ^ 3 * E)
  + (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 192 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 16 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  - (1 / 8 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (2 / 81 * alpha : k) • (A * B ^ 3)
  - (2 / 27 * alpha : k) • (A * B * E)
  - (2 / 27 * alpha : k) • (A * C * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 15552 * beta : k) • A ^ 5
  + (7 / 1296 * beta : k) • (A ^ 3 * C)
  + (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 432 * beta : k) • (A ^ 2 * E)
  - (7 / 108 * beta : k) • (A * B * D)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (5 / 3456 * delta : k) • A ^ 4
  + (5 / 432 * delta : k) • (A ^ 2 * C)
  + (5 / 216 * delta : k) • (A * B ^ 2)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (1 / 9 * epsilon : k) • (A * D)
  - (2 / 9 * epsilon : k) • (B * C)
  + (1 / 216 * zeta : k) • A ^ 3
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  - (1 / 18 * eta : k) • (A * B)
  + (1 / 3 * eta : k) • D
  + (1 / 72 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C


set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubic610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (5 / 81 : k) • (A * B ^ 2 * E)
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


set_option maxHeartbeats 32000000 in
def degreeZeroRawFourthTailCubic610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 243) : k), (-(5 / 243) : k), (5 / 81 : k),
    (10 / 81 : k), (20 / 81 : k), (5 / 243 : k),
    (20 / 243 : k), (10 / 81 : k), (-(5 / 27) : k),
    (-(10 / 27) : k), (-(5 / 27) : k), (-(5 / 27) : k),
    (1 / 13824 * l : k), (1 / 2304 * l : k), (1 / 576 * l : k),
    (-(5 / 384 * l) : k), (1 / 32 * l : k), (1 / 32 * l : k),
    (5 / 32 * l : k), (3 / 32 * l : k), (3 / 32 * l : k),
    (-(3 / 8 * l) : k), (-(3 / 8 * l) : k), (-(3 / 16 * l) : k),
    (-(3 / 16 * l) : k), (4 / 81 * alpha : k), (8 / 81 * alpha : k),
    (5 / 243 * alpha : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
    (-(4 / 27 * alpha) : k), (-(8 / 27 * alpha) : k), (-(4 / 81 * alpha) : k),
    (2 / 9 * alpha : k), (7 / 20736 * beta : k), (7 / 2592 * beta : k),
    (7 / 864 * beta : k), (175 / 7776 * beta : k), (-(7 / 72 * beta) : k),
    (-(7 / 72 * beta) : k), (-(35 / 432 * beta) : k), (-(35 / 432 * beta) : k),
    (7 / 36 * beta : k), (5 / 2592 * delta : k), (5 / 144 * delta : k),
    (5 / 72 * delta : k), (35 / 1296 * delta : k), (-(5 / 36 * delta) : k),
    (-(5 / 36 * delta) : k), (2 / 27 * epsilon : k), (-(2 / 9 * epsilon) : k),
    (-(2 / 9 * epsilon) : k), (-(1 / 9 * epsilon) : k), (1 / 48 * zeta : k),
    (-(1 / 4 * zeta) : k), (-(1 / 4 * zeta) : k), (-(1 / 9 * eta) : k),
    (-(1 / 9 * eta) : k), (1 / 3 * eta : k), (-(1 / 12 * theta) : k),
    (1 / 6 * theta : k)]
    [
    [2, 2, 1, 0, 0], [1, 4, 0, 0, 0], [2, 0, 0, 2, 0], [1, 2, 0, 0, 1],
    [1, 1, 1, 1, 0], [1, 0, 3, 0, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0],
    [1, 0, 0, 0, 2], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0],
    [5, 1, 0, 0, 0], [4, 0, 0, 1, 0], [3, 1, 1, 0, 0], [2, 3, 0, 0, 0],
    [2, 1, 0, 0, 1], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0],
    [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
    [0, 0, 2, 1, 0], [2, 1, 0, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
    [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
    [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
    [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
    [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [3, 1, 0, 0, 0],
    [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
    [0, 0, 1, 1, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
    [0, 0, 2, 0, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
    [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0],
    [0, 0, 0, 1, 0]]


set_option maxHeartbeats 16000000 in
def degreeZeroAlphaGroupCubic610
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(1 / 81) : k), (-(1 / 27) : k), (-(1 / 27) : k),
    (4 / 27 : k), (4 / 27 : k), (4 / 27 : k),
    (-(4 / 9) : k), (-(4 / 9) : k), (-(4 / 9) : k),
    (-(4 / 9) : k)]
    [
    [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
    [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
    [0, 1, 0, 2, 0], [0, 0, 2, 1, 0]]


set_option maxHeartbeats 16000000 in
def degreeZeroBaseGroupCubic610
    (l : k) (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 2916) : k), (-(5 / 108) : k), (5 / 324 : k),
    (-(25 / 243) : k), (-(4 / 243) : k), (-(5 / 54) : k),
    (10 / 27 : k), (5 / 27 : k), (5 / 27 : k),
    (10 / 81 : k), (5 / 9 : k), (5 / 27 : k),
    (-(10 / 9) : k), (-(10 / 27) : k), (5 / 27648 * l : k),
    (25 / 6912 * l : k), (-(17 / 13824 * l) : k), (1 / 128 * l : k),
    (1 / 288 * l : k), (13 / 576 * l : k), (-(5 / 192 * l) : k),
    (-(1 / 32 * l) : k), (1 / 16 * l : k), (1 / 8 * l : k),
    (3 / 8 * l : k), (1 / 16 * l : k), (3 / 16 * l : k),
    (9 / 32 * l : k), (-(3 / 4 * l) : k), (-(3 / 8 * l) : k),
    (-(3 / 4 * l) : k)]
    [
    [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0],
    [0, 5, 0, 0, 0], [2, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0],
    [1, 0, 2, 1, 0], [0, 3, 0, 0, 1], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
    [0, 0, 1, 1, 1], [0, 0, 0, 3, 0], [7, 0, 0, 0, 0], [5, 0, 1, 0, 0],
    [4, 2, 0, 0, 0], [4, 0, 0, 0, 1], [3, 1, 0, 1, 0], [3, 0, 2, 0, 0],
    [2, 2, 1, 0, 0], [1, 4, 0, 0, 0], [2, 0, 1, 0, 1], [1, 2, 0, 0, 1],
    [1, 1, 1, 1, 0], [1, 0, 3, 0, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0],
    [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0]]


set_option maxHeartbeats 16000000 in
def degreeZeroBetaGroupCubic610
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (35 / 62208 : k), (49 / 5184 : k), (-(7 / 1728) : k),
    (7 / 432 : k), (-(7 / 216) : k), (7 / 144 : k),
    (35 / 432 : k), (35 / 1728 : k), (7 / 36 : k),
    (-(7 / 36) : k), (-(7 / 72) : k), (-(7 / 18) : k),
    (-(7 / 108) : k), (7 / 12 : k)]
    [
    [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
    [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
    [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
    [0, 0, 3, 0, 0], [0, 0, 0, 0, 2]]


set_option maxHeartbeats 16000000 in
def degreeZeroDeltaGroupCubic610
    (A B C D : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D]
    [
    (1 / 576 : k), (5 / 216 : k), (-(5 / 216) : k),
    (5 / 36 : k), (5 / 36 : k), (-(5 / 12) : k)]
    [
    [5, 0, 0, 0], [3, 0, 1, 0], [2, 2, 0, 0], [1, 0, 2, 0],
    [0, 2, 1, 0], [0, 0, 0, 2]]


set_option maxHeartbeats 16000000 in
def degreeZeroEpsilonGroupCubic610
    (A B C D : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D]
    [
    (-(1 / 18) : k), (2 / 9 : k), (2 / 27 : k),
    (-(2 / 3) : k)]
    [
    [2, 0, 0, 1], [1, 1, 1, 0], [0, 3, 0, 0], [0, 0, 1, 1]]


set_option maxHeartbeats 16000000 in
def degreeZeroEtaGroupCubic610
    (A B C D : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D]
    [
    (-(1 / 36) : k), (-(1 / 3) : k), (-(1 / 3) : k)]
    [
    [2, 1, 0, 0], [1, 0, 0, 1], [0, 1, 1, 0]]


set_option maxHeartbeats 16000000 in
def degreeZeroThetaGroupCubic610
    (A B C E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, E]
    [
    (1 / 72 : k), (1 / 6 : k), (-(1 / 12) : k),
    (1 : k)]
    [
    [3, 0, 0, 0], [1, 0, 1, 0], [0, 2, 0, 0], [0, 0, 0, 1]]


set_option maxHeartbeats 16000000 in
def degreeZeroZetaGroupCubic610
    (A B C D : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D]
    [
    (1 / 192 : k), (1 / 24 : k), (1 / 12 : k),
    (-(1 / 2) : k), (-(1 / 4) : k)]
    [
    [4, 0, 0, 0], [2, 0, 1, 0], [1, 2, 0, 0], [0, 1, 0, 1],
    [0, 0, 2, 0]]


def degreeZeroPrimitiveCubic610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  degreeZeroBaseGroupCubic610 l A B C D E +
    alpha • degreeZeroAlphaGroupCubic610 A B C D E +
    beta • degreeZeroBetaGroupCubic610 A B C D E +
    delta • degreeZeroDeltaGroupCubic610 A B C D +
    epsilon • degreeZeroEpsilonGroupCubic610 A B C D +
    zeta • degreeZeroZetaGroupCubic610 A B C D +
    eta • degreeZeroEtaGroupCubic610 A B C D +
    theta • degreeZeroThetaGroupCubic610 A B C E


set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicFlat610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 2916 : k)) • (A ^ 3 * B ^ 3)
  - (5 / 108 : k) • (A ^ 2 * B ^ 2 * D)
  + (5 / 324 : k) • (A ^ 2 * B * C ^ 2)
  - (25 / 243 : k) • (A * B ^ 3 * C)
  - (4 / 243 : k) • B ^ 5
  - (5 / 54 : k) • (A ^ 2 * D * E)
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (5 / 27 : k) • (A * C ^ 2 * D)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  - (10 / 9 : k) • (C * D * E)
  - (10 / 27 : k) • D ^ 3
  + (5 / 27648 * l : k) • A ^ 7
  + (25 / 6912 * l : k) • (A ^ 5 * C)
  - (17 / 13824 * l : k) • (A ^ 4 * B ^ 2)
  + (1 / 128 * l : k) • (A ^ 4 * E)
  + (1 / 288 * l : k) • (A ^ 3 * B * D)
  + (13 / 576 * l : k) • (A ^ 3 * C ^ 2)
  - (5 / 192 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (1 / 32 * l : k) • (A * B ^ 4)
  + (1 / 16 * l : k) • (A ^ 2 * C * E)
  + (1 / 8 * l : k) • (A * B ^ 2 * E)
  + (3 / 8 * l : k) • (A * B * C * D)
  + (1 / 16 * l : k) • (A * C ^ 3)
  + (3 / 16 * l : k) • (B ^ 3 * D)
  + (9 / 32 * l : k) • (B ^ 2 * C ^ 2)
  - (3 / 4 * l : k) • (B * D * E)
  - (3 / 8 * l : k) • (C ^ 2 * E)
  - (3 / 4 * l : k) • (C * D ^ 2)
  - (1 / 81 * alpha : k) • (A ^ 2 * B ^ 3)
  - (1 / 27 * alpha : k) • (A ^ 2 * B * E)
  - (1 / 27 * alpha : k) • (A ^ 2 * C * D)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  - (4 / 9 * alpha : k) • (A * D * E)
  - (4 / 9 * alpha : k) • (B * C * E)
  - (4 / 9 * alpha : k) • (B * D ^ 2)
  - (4 / 9 * alpha : k) • (C ^ 2 * D)
  + (35 / 62208 * beta : k) • A ^ 6
  + (49 / 5184 * beta : k) • (A ^ 4 * C)
  - (7 / 1728 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 432 * beta : k) • (A ^ 3 * E)
  - (7 / 216 * beta : k) • (A ^ 2 * B * D)
  + (7 / 144 * beta : k) • (A ^ 2 * C ^ 2)
  + (35 / 432 * beta : k) • (A * B ^ 2 * C)
  + (35 / 1728 * beta : k) • B ^ 4
  + (7 / 36 * beta : k) • (A * C * E)
  - (7 / 36 * beta : k) • (A * D ^ 2)
  - (7 / 72 * beta : k) • (B ^ 2 * E)
  - (7 / 18 * beta : k) • (B * C * D)
  - (7 / 108 * beta : k) • C ^ 3
  + (7 / 12 * beta : k) • E ^ 2
  + (1 / 576 * delta : k) • A ^ 5
  + (5 / 216 * delta : k) • (A ^ 3 * C)
  - (5 / 216 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  - (5 / 12 * delta : k) • D ^ 2
  - (1 / 18 * epsilon : k) • (A ^ 2 * D)
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  - (2 / 3 * epsilon : k) • (C * D)
  + (1 / 192 * zeta : k) • A ^ 4
  + (1 / 24 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  - (1 / 2 * zeta : k) • (B * D)
  - (1 / 4 * zeta : k) • C ^ 2
  - (1 / 36 * eta : k) • (A ^ 2 * B)
  - (1 / 3 * eta : k) • (A * D)
  - (1 / 3 * eta : k) • (B * C)
  + (1 / 72 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)
  - (1 / 12 * theta : k) • B ^ 2
  + (1 * theta : k) • E

end CubicIntegrals610


/-! ## Transport identities -/

section CubicTransport610

variable {k : Type*} [Field k] [CharZero k]

end CubicTransport610


/-! ## Residual in cubic letters -/

section CubicResidual610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

end CubicResidual610


/-! ## Degree helpers -/

section CubicDegreeHelpers610

variable {k : Type*} [Field k] [CharZero k]

end CubicDegreeHelpers610


/-! ## The 31 argmax cones -/

section CubicCones610

variable {k : Type*} [Field k] [CharZero k]


def CubicRatioConeA610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 3 * A.natDegree > 2 * B.natDegree
    ∧ 2 * A.natDegree > C.natDegree
    ∧ 5 * A.natDegree > 2 * D.natDegree
    ∧ 3 * A.natDegree > E.natDegree


def CubicRatioConeB610 (A B C D E : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree


def CubicRatioConeC610 (A B C D E : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * D.natDegree < 5 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree


def CubicRatioConeD610 (A B C D E : k[X]) : Prop :=
  0 < D.natDegree
    ∧ 5 * A.natDegree < 2 * D.natDegree
    ∧ 5 * B.natDegree < 3 * D.natDegree
    ∧ 5 * C.natDegree < 4 * D.natDegree
    ∧ 5 * E.natDegree < 6 * D.natDegree


def CubicRatioConeE610 (A B C D E : k[X]) : Prop :=
  0 < E.natDegree
    ∧ 3 * A.natDegree < E.natDegree
    ∧ 2 * B.natDegree < E.natDegree
    ∧ 3 * C.natDegree < 2 * E.natDegree
    ∧ 6 * D.natDegree < 5 * E.natDegree


def CubicRatioConeAB610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def CubicRatioConeAC610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def CubicRatioConeAD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < D.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def CubicRatioConeAE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < E.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree


def CubicRatioConeBC610 (A B C D E : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree


def CubicRatioConeBD610 (A B C D E : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree


def CubicRatioConeBE610 (A B C D E : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree


def CubicRatioConeCD610 (A B C D E : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 4 * D.natDegree = 5 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree


def CubicRatioConeCE610 (A B C D E : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * E.natDegree = 3 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * D.natDegree < 5 * C.natDegree


def CubicRatioConeDE610 (A B C D E : k[X]) : Prop :=
  0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 5 * E.natDegree = 6 * D.natDegree
    ∧ 5 * A.natDegree < 2 * D.natDegree
    ∧ 5 * B.natDegree < 3 * D.natDegree
    ∧ 5 * C.natDegree < 4 * D.natDegree


def CubicRatioConeABC610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def CubicRatioConeABD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def CubicRatioConeABE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree


def CubicRatioConeACD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def CubicRatioConeACE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree


def CubicRatioConeADE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree


def CubicRatioConeBCD610 (A B C D E : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree


def CubicRatioConeBCE610 (A B C D E : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree


def CubicRatioConeBDE610 (A B C D E : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree


def CubicRatioConeCDE610 (A B C D E : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 4 * D.natDegree = 5 * C.natDegree
    ∧ 2 * E.natDegree = 3 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree


def CubicRatioConeABCD610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def CubicRatioConeABCE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree


def CubicRatioConeABDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree


def CubicRatioConeACDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree


def CubicRatioConeBCDE610 (A B C D E : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree


def CubicRatioConeABCDE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree


end CubicCones610


/-! ## Split lemmas, rest bounds, and cone kills -/

section CubicKills610

variable {k : Type*} [Field k] [CharZero k]


def lambdaCubicFaceB610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k)]
    [
    [0, 4, 0, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoB610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (-(5 / 27) : k), (-(5 / 27) : k),
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
    [1, 2, 1, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
    [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
    [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
    [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
    [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
    [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
    [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
    [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]

def lambdaCubicFaceC610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 81) : k)]
    [
    [0, 0, 3, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoC610
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

def primitiveCubicFaceD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(10 / 27) : k)]
    [
    [0, 0, 0, 3, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 2916) : k), (-(5 / 108) : k), (5 / 324 : k),
    (-(25 / 243) : k), (-(4 / 243) : k), (-(5 / 54) : k),
    (10 / 27 : k), (5 / 27 : k), (5 / 27 : k),
    (10 / 81 : k), (5 / 9 : k), (5 / 27 : k),
    (-(10 / 9) : k), (5 / 27648 * l : k), (25 / 6912 * l : k),
    (-(17 / 13824 * l) : k), (1 / 128 * l : k), (1 / 288 * l : k),
    (13 / 576 * l : k), (-(5 / 192 * l) : k), (-(1 / 32 * l) : k),
    (1 / 16 * l : k), (1 / 8 * l : k), (3 / 8 * l : k),
    (1 / 16 * l : k), (3 / 16 * l : k), (9 / 32 * l : k),
    (-(3 / 4 * l) : k), (-(3 / 8 * l) : k), (-(3 / 4 * l) : k),
    (-(1 / 81 * alpha) : k), (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k),
    (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
    (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
    (-(4 / 9 * alpha) : k), (35 / 62208 * beta : k), (49 / 5184 * beta : k),
    (-(7 / 1728 * beta) : k), (7 / 432 * beta : k), (-(7 / 216 * beta) : k),
    (7 / 144 * beta : k), (35 / 432 * beta : k), (35 / 1728 * beta : k),
    (7 / 36 * beta : k), (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k),
    (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k), (7 / 12 * beta : k),
    (1 / 576 * delta : k), (5 / 216 * delta : k), (-(5 / 216 * delta) : k),
    (5 / 36 * delta : k), (5 / 36 * delta : k), (-(5 / 12 * delta) : k),
    (-(1 / 18 * epsilon) : k), (2 / 9 * epsilon : k), (2 / 27 * epsilon : k),
    (-(2 / 3 * epsilon) : k), (1 / 192 * zeta : k), (1 / 24 * zeta : k),
    (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k),
    (-(1 / 36 * eta) : k), (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k),
    (1 / 72 * theta : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
    (1 * theta : k)]
    [
    [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0],
    [0, 5, 0, 0, 0], [2, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0],
    [1, 0, 2, 1, 0], [0, 3, 0, 0, 1], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
    [0, 0, 1, 1, 1], [7, 0, 0, 0, 0], [5, 0, 1, 0, 0], [4, 2, 0, 0, 0],
    [4, 0, 0, 0, 1], [3, 1, 0, 1, 0], [3, 0, 2, 0, 0], [2, 2, 1, 0, 0],
    [1, 4, 0, 0, 0], [2, 0, 1, 0, 1], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0],
    [1, 0, 3, 0, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1],
    [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [2, 3, 0, 0, 0], [2, 1, 0, 0, 1],
    [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
    [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0],
    [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
    [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
    [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
    [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
    [2, 2, 0, 0, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0],
    [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
    [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0],
    [0, 0, 2, 0, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
    [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]]

def lambdaCubicFaceE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 9 : k)]
    [
    [0, 0, 0, 0, 2]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoE610
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

def kappaCubicFaceAB610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k)]
    [
    [1, 3, 0, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoAB610
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

def lambdaCubicFaceAC610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 81) : k)]
    [
    [0, 0, 3, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoAC610
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

def lambdaCubicFaceAD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k)]
    [
    [1, 0, 0, 2, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoAD610
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

def lambdaCubicFaceAE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 9 : k)]
    [
    [0, 0, 0, 0, 2]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoAE610
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

def kappaCubicFaceBC610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k)]
    [
    [0, 1, 2, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoBC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k), (10 / 9 : k),
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
    [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
    [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
    [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
    [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
    [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
    [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
    [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
    [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]

def kappaCubicFaceBD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k)]
    [
    [0, 2, 0, 1, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoBD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k), (10 / 9 : k),
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
    [1, 3, 0, 0, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
    [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
    [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
    [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
    [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
    [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
    [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
    [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]

def lambdaCubicFaceCD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 81) : k)]
    [
    [0, 0, 3, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoCD610
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

def omicronCubicFaceCE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k)]
    [
    [0, 0, 2, 0, 1]]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoCE610
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

def kappaCubicFaceDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (10 / 9 : k)]
    [
    [0, 0, 0, 1, 1]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoDE610
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

def kappaCubicFaceABE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k)]
    [
    [1, 3, 0, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABE610
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

def muCubicFaceACD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k)]
    [
    [0, 0, 2, 1, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoACD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 1458) : k), (5 / 54 : k), (5 / 162 : k),
    (20 / 243 : k), (-(5 / 27) : k), (-(10 / 27) : k),
    (-(5 / 27) : k), (35 / 248832 * l : k), (5 / 2304 * l : k),
    (1 / 144 * l : k), (1 / 96 * l : k), (1 / 192 * l : k),
    (1 / 16 * l : k), (3 / 128 * l : k), (-(1 / 8 * l) : k),
    (-(3 / 16 * l) : k), (-(3 / 8 * l) : k), (-(1 / 16 * l) : k),
    (3 / 8 * l : k), (2 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
    (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
    (4 / 9 * alpha : k), (7 / 15552 * beta : k), (7 / 1296 * beta : k),
    (7 / 5184 * beta : k), (7 / 432 * beta : k), (-(7 / 108 * beta) : k),
    (-(35 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
    (5 / 3456 * delta : k), (5 / 432 * delta : k), (5 / 216 * delta : k),
    (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(1 / 9 * epsilon) : k),
    (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k), (-(1 / 8 * zeta) : k),
    (1 / 2 * zeta : k), (-(1 / 18 * eta) : k), (1 / 3 * eta : k),
    (1 / 72 * theta : k), (1 / 6 * theta : k)]
    [
    [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
    [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [6, 0, 0, 0, 0],
    [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0],
    [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
    [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [1, 3, 0, 0, 0],
    [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
    [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
    [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
    [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
    [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
    [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0],
    [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]]

def omicronCubicFaceACE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k)]
    [
    [0, 0, 2, 0, 1]]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoACE610
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

def kappaCubicFaceADE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (10 / 9 : k)]
    [
    [0, 0, 0, 1, 1]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoADE610
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

def kappaCubicFaceBCE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k)]
    [
    [0, 1, 2, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k), (10 / 9 : k),
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
    [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
    [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
    [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
    [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
    [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
    [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
    [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
    [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]

def muCubicFaceBDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k)]
    [
    [0, 1, 0, 2, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoBDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 1458) : k), (5 / 54 : k), (5 / 162 : k),
    (20 / 243 : k), (-(5 / 27) : k), (-(10 / 27) : k),
    (-(5 / 27) : k), (35 / 248832 * l : k), (5 / 2304 * l : k),
    (1 / 144 * l : k), (1 / 96 * l : k), (1 / 192 * l : k),
    (1 / 16 * l : k), (3 / 128 * l : k), (-(1 / 8 * l) : k),
    (-(3 / 16 * l) : k), (-(3 / 8 * l) : k), (-(1 / 16 * l) : k),
    (3 / 8 * l : k), (2 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
    (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
    (4 / 9 * alpha : k), (7 / 15552 * beta : k), (7 / 1296 * beta : k),
    (7 / 5184 * beta : k), (7 / 432 * beta : k), (-(7 / 108 * beta) : k),
    (-(35 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
    (5 / 3456 * delta : k), (5 / 432 * delta : k), (5 / 216 * delta : k),
    (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(1 / 9 * epsilon) : k),
    (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k), (-(1 / 8 * zeta) : k),
    (1 / 2 * zeta : k), (-(1 / 18 * eta) : k), (1 / 3 * eta : k),
    (1 / 72 * theta : k), (1 / 6 * theta : k)]
    [
    [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
    [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0],
    [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0],
    [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
    [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [1, 3, 0, 0, 0],
    [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
    [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
    [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
    [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
    [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
    [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0],
    [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]]

def kappaCubicFaceCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (10 / 9 : k)]
    [
    [0, 0, 0, 1, 1]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoCDE610
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

def kappaCubicFaceACDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (10 / 9 : k)]
    [
    [0, 0, 0, 1, 1]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoACDE610
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

def lambdaCubicInnerBE610 (b e : k) : k :=
  5 * b ^ 4 + (-45 : k) * b ^ 2 * e + 135 * e ^ 2

def primitiveCubicInnerBE610 (b e : k) : k :=
  (-4 : k) * b ^ 5 + 30 * b ^ 3 * e

def lambdaCubicFaceBE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k), (5 / 9 : k)]
    [
    [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 0, 0, 0, 2]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoBE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (-(5 / 27) : k), (-(10 / 27) : k),
    (-(5 / 81) : k), (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k),
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
    [1, 2, 1, 0, 0], [1, 0, 0, 2, 0], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
    [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
    [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
    [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
    [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]

def primitiveCubicFaceBE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(4 / 243) : k), (10 / 81 : k)]
    [
    [0, 5, 0, 0, 0], [0, 3, 0, 0, 1]]

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoBE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 2916) : k), (-(5 / 108) : k), (5 / 324 : k),
    (-(25 / 243) : k), (-(5 / 54) : k), (10 / 27 : k),
    (5 / 27 : k), (5 / 27 : k), (5 / 9 : k),
    (5 / 27 : k), (-(10 / 9) : k), (-(10 / 27) : k),
    (5 / 27648 * l : k), (25 / 6912 * l : k), (-(17 / 13824 * l) : k),
    (1 / 128 * l : k), (1 / 288 * l : k), (13 / 576 * l : k),
    (-(5 / 192 * l) : k), (-(1 / 32 * l) : k), (1 / 16 * l : k),
    (1 / 8 * l : k), (3 / 8 * l : k), (1 / 16 * l : k),
    (3 / 16 * l : k), (9 / 32 * l : k), (-(3 / 4 * l) : k),
    (-(3 / 8 * l) : k), (-(3 / 4 * l) : k), (-(1 / 81 * alpha) : k),
    (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k), (4 / 27 * alpha : k),
    (4 / 27 * alpha : k), (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k),
    (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
    (35 / 62208 * beta : k), (49 / 5184 * beta : k), (-(7 / 1728 * beta) : k),
    (7 / 432 * beta : k), (-(7 / 216 * beta) : k), (7 / 144 * beta : k),
    (35 / 432 * beta : k), (35 / 1728 * beta : k), (7 / 36 * beta : k),
    (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k), (-(7 / 18 * beta) : k),
    (-(7 / 108 * beta) : k), (7 / 12 * beta : k), (1 / 576 * delta : k),
    (5 / 216 * delta : k), (-(5 / 216 * delta) : k), (5 / 36 * delta : k),
    (5 / 36 * delta : k), (-(5 / 12 * delta) : k), (-(1 / 18 * epsilon) : k),
    (2 / 9 * epsilon : k), (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k),
    (1 / 192 * zeta : k), (1 / 24 * zeta : k), (1 / 12 * zeta : k),
    (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k), (-(1 / 36 * eta) : k),
    (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k), (1 / 72 * theta : k),
    (1 / 6 * theta : k), (-(1 / 12 * theta) : k), (1 * theta : k)]
    [
    [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0],
    [2, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0], [1, 0, 2, 1, 0],
    [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0],
    [7, 0, 0, 0, 0], [5, 0, 1, 0, 0], [4, 2, 0, 0, 0], [4, 0, 0, 0, 1],
    [3, 1, 0, 1, 0], [3, 0, 2, 0, 0], [2, 2, 1, 0, 0], [1, 4, 0, 0, 0],
    [2, 0, 1, 0, 1], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 0, 3, 0, 0],
    [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1],
    [0, 0, 1, 2, 0], [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0],
    [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1],
    [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0],
    [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
    [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1],
    [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
    [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [2, 0, 0, 1, 0],
    [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
    [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0],
    [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]]

def kappaCubicInnerABC610 (a b c : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b * c ^ 2

def lambdaCubicInnerABC610 (a b c : k) : k :=
  15 * a * b ^ 2 * c + 5 * b ^ 4 + (-15 : k) * c ^ 3

def muCubicInnerABC610 (a b c : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 45 * a * b * c ^ 2 + 120 * b ^ 3 * c

def omicronCubicInnerABC610 (a b c : k) : k :=
  (-5 : k) * a * b ^ 4 + 45 * b ^ 2 * c ^ 2

def primitiveCubicInnerABC610 (a b c : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + 45 * a ^ 2 * b * c ^ 2 + (-300 : k) * a * b ^ 3 * c + (-48 : k) * b ^ 5 + 540 * b * c ^ 3

def kappaCubicFaceABC610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k)]
    [
    [1, 3, 0, 0, 0], [0, 1, 2, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABC610
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

def lambdaCubicFaceABC610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (5 / 243 : k), (-(5 / 81) : k)]
    [
    [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [0, 0, 3, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k), (-(5 / 27) : k), (-(10 / 27) : k),
    (5 / 9 : k), (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k),
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
    [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 0, 0, 2],
    [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
    [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
    [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
    [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
    [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]

def muCubicFaceABC610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 1458) : k), (5 / 162 : k), (20 / 243 : k)]
    [
    [2, 3, 0, 0, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 54 : k), (-(5 / 27) : k), (-(10 / 27) : k),
    (-(5 / 27) : k), (-(5 / 27) : k), (35 / 248832 * l : k),
    (5 / 2304 * l : k), (1 / 144 * l : k), (1 / 96 * l : k),
    (1 / 192 * l : k), (1 / 16 * l : k), (3 / 128 * l : k),
    (-(1 / 8 * l) : k), (-(3 / 16 * l) : k), (-(3 / 8 * l) : k),
    (-(1 / 16 * l) : k), (3 / 8 * l : k), (2 / 81 * alpha : k),
    (-(2 / 27 * alpha) : k), (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
    (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (7 / 15552 * beta : k),
    (7 / 1296 * beta : k), (7 / 5184 * beta : k), (7 / 432 * beta : k),
    (-(7 / 108 * beta) : k), (-(35 / 432 * beta) : k), (7 / 36 * beta : k),
    (7 / 72 * beta : k), (5 / 3456 * delta : k), (5 / 432 * delta : k),
    (5 / 216 * delta : k), (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k),
    (-(1 / 9 * epsilon) : k), (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k),
    (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k), (-(1 / 18 * eta) : k),
    (1 / 3 * eta : k), (1 / 72 * theta : k), (1 / 6 * theta : k)]
    [
    [1, 2, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
    [0, 0, 2, 1, 0], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 0, 0, 0, 1],
    [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
    [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
    [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
    [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
    [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0],
    [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [0, 2, 0, 0, 0],
    [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
    [0, 0, 1, 0, 0]]

def kappaCubicInnerABD610 (a b d : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b ^ 2 * d

def lambdaCubicInnerABD610 (a b d : k) : k :=
  (-45 : k) * a * d ^ 2 + 5 * b ^ 4

def muCubicInnerABD610 (a b d : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 135 * a * b ^ 2 * d + (-270 : k) * b * d ^ 2

def omicronCubicInnerABD610 (a b d : k) : k :=
  (-5 : k) * a * b ^ 4 + 25 * b ^ 3 * d

def primitiveCubicInnerABD610 (a b d : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-135 : k) * a ^ 2 * b ^ 2 * d + 540 * a * b * d ^ 2 + (-48 : k) * b ^ 5 + (-1080 : k) * d ^ 3

def kappaCubicFaceABD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k)]
    [
    [1, 3, 0, 0, 0], [0, 2, 0, 1, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABD610
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
    [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
    [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
    [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0],
    [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
    [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0],
    [1, 0, 0, 0, 0]]

def lambdaCubicFaceABD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k)]
    [
    [0, 4, 0, 0, 0], [1, 0, 0, 2, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (-(5 / 27) : k), (-(10 / 27) : k),
    (-(5 / 81) : k), (5 / 9 : k), (-(5 / 6912 * l) : k),
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
    [1, 2, 1, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0],
    [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
    [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
    [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0],
    [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0],
    [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0],
    [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0],
    [0, 1, 0, 0, 0]]

def muCubicFaceABD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 1458) : k), (5 / 54 : k), (-(5 / 27) : k)]
    [
    [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [0, 1, 0, 2, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 162 : k), (20 / 243 : k), (-(5 / 27) : k),
    (-(10 / 27) : k), (-(5 / 27) : k), (35 / 248832 * l : k),
    (5 / 2304 * l : k), (1 / 144 * l : k), (1 / 96 * l : k),
    (1 / 192 * l : k), (1 / 16 * l : k), (3 / 128 * l : k),
    (-(1 / 8 * l) : k), (-(3 / 16 * l) : k), (-(3 / 8 * l) : k),
    (-(1 / 16 * l) : k), (3 / 8 * l : k), (2 / 81 * alpha : k),
    (-(2 / 27 * alpha) : k), (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
    (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (7 / 15552 * beta : k),
    (7 / 1296 * beta : k), (7 / 5184 * beta : k), (7 / 432 * beta : k),
    (-(7 / 108 * beta) : k), (-(35 / 432 * beta) : k), (7 / 36 * beta : k),
    (7 / 72 * beta : k), (5 / 3456 * delta : k), (5 / 432 * delta : k),
    (5 / 216 * delta : k), (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k),
    (-(1 / 9 * epsilon) : k), (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k),
    (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k), (-(1 / 18 * eta) : k),
    (1 / 3 * eta : k), (1 / 72 * theta : k), (1 / 6 * theta : k)]
    [
    [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
    [0, 0, 2, 1, 0], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 0, 0, 0, 1],
    [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
    [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
    [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
    [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
    [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0],
    [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [0, 2, 0, 0, 0],
    [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
    [0, 0, 1, 0, 0]]

def primitiveCubicFaceABD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 2916) : k), (-(5 / 108) : k), (-(4 / 243) : k),
    (5 / 27 : k), (-(10 / 27) : k)]
    [
    [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [0, 5, 0, 0, 0], [1, 1, 0, 2, 0],
    [0, 0, 0, 3, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoABD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 324 : k), (-(25 / 243) : k), (-(5 / 54) : k),
    (10 / 27 : k), (5 / 27 : k), (10 / 81 : k),
    (5 / 9 : k), (5 / 27 : k), (-(10 / 9) : k),
    (5 / 27648 * l : k), (25 / 6912 * l : k), (-(17 / 13824 * l) : k),
    (1 / 128 * l : k), (1 / 288 * l : k), (13 / 576 * l : k),
    (-(5 / 192 * l) : k), (-(1 / 32 * l) : k), (1 / 16 * l : k),
    (1 / 8 * l : k), (3 / 8 * l : k), (1 / 16 * l : k),
    (3 / 16 * l : k), (9 / 32 * l : k), (-(3 / 4 * l) : k),
    (-(3 / 8 * l) : k), (-(3 / 4 * l) : k), (-(1 / 81 * alpha) : k),
    (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k), (4 / 27 * alpha : k),
    (4 / 27 * alpha : k), (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k),
    (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
    (35 / 62208 * beta : k), (49 / 5184 * beta : k), (-(7 / 1728 * beta) : k),
    (7 / 432 * beta : k), (-(7 / 216 * beta) : k), (7 / 144 * beta : k),
    (35 / 432 * beta : k), (35 / 1728 * beta : k), (7 / 36 * beta : k),
    (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k), (-(7 / 18 * beta) : k),
    (-(7 / 108 * beta) : k), (7 / 12 * beta : k), (1 / 576 * delta : k),
    (5 / 216 * delta : k), (-(5 / 216 * delta) : k), (5 / 36 * delta : k),
    (5 / 36 * delta : k), (-(5 / 12 * delta) : k), (-(1 / 18 * epsilon) : k),
    (2 / 9 * epsilon : k), (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k),
    (1 / 192 * zeta : k), (1 / 24 * zeta : k), (1 / 12 * zeta : k),
    (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k), (-(1 / 36 * eta) : k),
    (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k), (1 / 72 * theta : k),
    (1 / 6 * theta : k), (-(1 / 12 * theta) : k), (1 * theta : k)]
    [
    [2, 1, 2, 0, 0], [1, 3, 1, 0, 0], [2, 0, 0, 1, 1], [1, 1, 1, 0, 1],
    [1, 0, 2, 1, 0], [0, 3, 0, 0, 1], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
    [0, 0, 1, 1, 1], [7, 0, 0, 0, 0], [5, 0, 1, 0, 0], [4, 2, 0, 0, 0],
    [4, 0, 0, 0, 1], [3, 1, 0, 1, 0], [3, 0, 2, 0, 0], [2, 2, 1, 0, 0],
    [1, 4, 0, 0, 0], [2, 0, 1, 0, 1], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0],
    [1, 0, 3, 0, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1],
    [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [2, 3, 0, 0, 0], [2, 1, 0, 0, 1],
    [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
    [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0],
    [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
    [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
    [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
    [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
    [2, 2, 0, 0, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0],
    [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
    [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0],
    [0, 0, 2, 0, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
    [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]]

def kappaCubicInnerBCD610 (b c d : k) : k :=
  (-5 : k) * b ^ 2 * d + (-5 : k) * b * c ^ 2

def lambdaCubicInnerBCD610 (b c d : k) : k :=
  5 * b ^ 4 + (-90 : k) * b * c * d + (-15 : k) * c ^ 3

def muCubicInnerBCD610 (b c d : k) : k :=
  20 * b ^ 3 * c + (-45 : k) * b * d ^ 2 + (-45 : k) * c ^ 2 * d

def omicronCubicInnerBCD610 (b c d : k) : k :=
  25 * b ^ 3 * d + 45 * b ^ 2 * c ^ 2 + (-90 : k) * c * d ^ 2

def primitiveCubicInnerBCD610 (b c d : k) : k :=
  (-4 : k) * b ^ 5 + 135 * b ^ 2 * c * d + 45 * b * c ^ 3 + (-90 : k) * d ^ 3

def kappaCubicFaceBCD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k), (-(5 / 27) : k)]
    [
    [0, 2, 0, 1, 0], [0, 1, 2, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (10 / 9 : k), (7 / 6912 * l : k),
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
    [1, 3, 0, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
    [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
    [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0],
    [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
    [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0],
    [1, 0, 0, 0, 0]]

def lambdaCubicFaceBCD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(10 / 27) : k), (-(5 / 81) : k)]
    [
    [0, 4, 0, 0, 0], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (-(5 / 27) : k), (-(5 / 27) : k),
    (5 / 9 : k), (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k),
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
    [1, 2, 1, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 0, 0, 0, 2],
    [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
    [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
    [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
    [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
    [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]

def muCubicFaceBCD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (20 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k)]
    [
    [0, 3, 1, 0, 0], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 1458) : k), (5 / 54 : k), (5 / 162 : k),
    (-(5 / 27) : k), (-(10 / 27) : k), (35 / 248832 * l : k),
    (5 / 2304 * l : k), (1 / 144 * l : k), (1 / 96 * l : k),
    (1 / 192 * l : k), (1 / 16 * l : k), (3 / 128 * l : k),
    (-(1 / 8 * l) : k), (-(3 / 16 * l) : k), (-(3 / 8 * l) : k),
    (-(1 / 16 * l) : k), (3 / 8 * l : k), (2 / 81 * alpha : k),
    (-(2 / 27 * alpha) : k), (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
    (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (7 / 15552 * beta : k),
    (7 / 1296 * beta : k), (7 / 5184 * beta : k), (7 / 432 * beta : k),
    (-(7 / 108 * beta) : k), (-(35 / 432 * beta) : k), (7 / 36 * beta : k),
    (7 / 72 * beta : k), (5 / 3456 * delta : k), (5 / 432 * delta : k),
    (5 / 216 * delta : k), (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k),
    (-(1 / 9 * epsilon) : k), (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k),
    (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k), (-(1 / 18 * eta) : k),
    (1 / 3 * eta : k), (1 / 72 * theta : k), (1 / 6 * theta : k)]
    [
    [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [1, 0, 0, 1, 1],
    [0, 1, 1, 0, 1], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 0, 0, 0, 1],
    [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
    [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
    [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
    [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
    [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0],
    [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [0, 2, 0, 0, 0],
    [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
    [0, 0, 1, 0, 0]]

def primitiveCubicFaceBCD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(4 / 243) : k), (5 / 9 : k), (5 / 27 : k),
    (-(10 / 27) : k)]
    [
    [0, 5, 0, 0, 0], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 0, 0, 3, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 2916) : k), (-(5 / 108) : k), (5 / 324 : k),
    (-(25 / 243) : k), (-(5 / 54) : k), (10 / 27 : k),
    (5 / 27 : k), (5 / 27 : k), (10 / 81 : k),
    (-(10 / 9) : k), (5 / 27648 * l : k), (25 / 6912 * l : k),
    (-(17 / 13824 * l) : k), (1 / 128 * l : k), (1 / 288 * l : k),
    (13 / 576 * l : k), (-(5 / 192 * l) : k), (-(1 / 32 * l) : k),
    (1 / 16 * l : k), (1 / 8 * l : k), (3 / 8 * l : k),
    (1 / 16 * l : k), (3 / 16 * l : k), (9 / 32 * l : k),
    (-(3 / 4 * l) : k), (-(3 / 8 * l) : k), (-(3 / 4 * l) : k),
    (-(1 / 81 * alpha) : k), (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k),
    (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
    (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
    (-(4 / 9 * alpha) : k), (35 / 62208 * beta : k), (49 / 5184 * beta : k),
    (-(7 / 1728 * beta) : k), (7 / 432 * beta : k), (-(7 / 216 * beta) : k),
    (7 / 144 * beta : k), (35 / 432 * beta : k), (35 / 1728 * beta : k),
    (7 / 36 * beta : k), (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k),
    (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k), (7 / 12 * beta : k),
    (1 / 576 * delta : k), (5 / 216 * delta : k), (-(5 / 216 * delta) : k),
    (5 / 36 * delta : k), (5 / 36 * delta : k), (-(5 / 12 * delta) : k),
    (-(1 / 18 * epsilon) : k), (2 / 9 * epsilon : k), (2 / 27 * epsilon : k),
    (-(2 / 3 * epsilon) : k), (1 / 192 * zeta : k), (1 / 24 * zeta : k),
    (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k),
    (-(1 / 36 * eta) : k), (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k),
    (1 / 72 * theta : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
    (1 * theta : k)]
    [
    [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0],
    [2, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0], [1, 0, 2, 1, 0],
    [0, 3, 0, 0, 1], [0, 0, 1, 1, 1], [7, 0, 0, 0, 0], [5, 0, 1, 0, 0],
    [4, 2, 0, 0, 0], [4, 0, 0, 0, 1], [3, 1, 0, 1, 0], [3, 0, 2, 0, 0],
    [2, 2, 1, 0, 0], [1, 4, 0, 0, 0], [2, 0, 1, 0, 1], [1, 2, 0, 0, 1],
    [1, 1, 1, 1, 0], [1, 0, 3, 0, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0],
    [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [2, 3, 0, 0, 0],
    [2, 1, 0, 0, 1], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0],
    [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
    [0, 0, 2, 1, 0], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0],
    [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0],
    [0, 4, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
    [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [5, 0, 0, 0, 0],
    [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0],
    [0, 0, 0, 2, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
    [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
    [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0],
    [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
    [0, 0, 0, 0, 1]]

def kappaCubicInnerABCD610 (a b c d : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b ^ 2 * d + (-45 : k) * b * c ^ 2

def lambdaCubicInnerABCD610 (a b c d : k) : k :=
  15 * a * b ^ 2 * c + (-45 : k) * a * d ^ 2 + 5 * b ^ 4 + (-90 : k) * b * c * d + (-15 : k) * c ^ 3

def muCubicInnerABCD610 (a b c d : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 135 * a * b ^ 2 * d + 45 * a * b * c ^ 2 + 120 * b ^ 3 * c + (-270 : k) * b * d ^ 2 + (-270 : k) * c ^ 2 * d

def omicronCubicInnerABCD610 (a b c d : k) : k :=
  (-5 : k) * a * b ^ 4 + 60 * a * b * c * d + 25 * b ^ 3 * d + 45 * b ^ 2 * c ^ 2 + (-90 : k) * c * d ^ 2

def primitiveCubicInnerABCD610 (a b c d : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-135 : k) * a ^ 2 * b ^ 2 * d + 45 * a ^ 2 * b * c ^ 2 + (-300 : k) * a * b ^ 3 * c + 540 * a * b * d ^ 2 + 540 * a * c ^ 2 * d + (-48 : k) * b ^ 5 + 1620 * b ^ 2 * c * d + 540 * b * c ^ 3 + (-1080 : k) * d ^ 3

def kappaCubicFaceABCD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k)]
    [
    [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (10 / 9 : k), (7 / 6912 * l : k), (5 / 288 * l : k),
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
    [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
    [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0],
    [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
    [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
    [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [3, 0, 0, 0, 0],
    [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0],
    [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]

def lambdaCubicFaceABCD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
    (-(10 / 27) : k), (-(5 / 81) : k)]
    [
    [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 1, 1, 1, 0],
    [0, 0, 3, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k), (5 / 9 : k), (-(5 / 6912 * l) : k),
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
    [0, 2, 0, 0, 1], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
    [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
    [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
    [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
    [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
    [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
    [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]

def muCubicFaceABCD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 1458) : k), (5 / 54 : k), (5 / 162 : k),
    (20 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k)]
    [
    [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
    [0, 1, 0, 2, 0], [0, 0, 2, 1, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k), (-(10 / 27) : k), (35 / 248832 * l : k),
    (5 / 2304 * l : k), (1 / 144 * l : k), (1 / 96 * l : k),
    (1 / 192 * l : k), (1 / 16 * l : k), (3 / 128 * l : k),
    (-(1 / 8 * l) : k), (-(3 / 16 * l) : k), (-(3 / 8 * l) : k),
    (-(1 / 16 * l) : k), (3 / 8 * l : k), (2 / 81 * alpha : k),
    (-(2 / 27 * alpha) : k), (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
    (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (7 / 15552 * beta : k),
    (7 / 1296 * beta : k), (7 / 5184 * beta : k), (7 / 432 * beta : k),
    (-(7 / 108 * beta) : k), (-(35 / 432 * beta) : k), (7 / 36 * beta : k),
    (7 / 72 * beta : k), (5 / 3456 * delta : k), (5 / 432 * delta : k),
    (5 / 216 * delta : k), (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k),
    (-(1 / 9 * epsilon) : k), (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k),
    (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k), (-(1 / 18 * eta) : k),
    (1 / 3 * eta : k), (1 / 72 * theta : k), (1 / 6 * theta : k)]
    [
    [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0],
    [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0],
    [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
    [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1],
    [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
    [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1],
    [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
    [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0],
    [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0],
    [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
    [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]]

def omicronCubicFaceABCD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 486) : k), (10 / 81 : k), (25 / 486 : k),
    (5 / 54 : k), (-(5 / 27) : k)]
    [
    [1, 4, 0, 0, 0], [1, 1, 1, 1, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0],
    [0, 0, 1, 2, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoABCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (-(5 / 27) : k), (-(5 / 27) : k),
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
    [1, 2, 0, 0, 1], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [4, 0, 0, 1, 0],
    [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
    [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
    [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
    [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
    [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
    [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
    [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
    [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]]

def primitiveCubicFaceABCD610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 2916) : k), (-(5 / 108) : k), (5 / 324 : k),
    (-(25 / 243) : k), (-(4 / 243) : k), (5 / 27 : k),
    (5 / 27 : k), (5 / 9 : k), (5 / 27 : k),
    (-(10 / 27) : k)]
    [
    [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0],
    [0, 5, 0, 0, 0], [1, 1, 0, 2, 0], [1, 0, 2, 1, 0], [0, 2, 1, 1, 0],
    [0, 1, 3, 0, 0], [0, 0, 0, 3, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoABCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 54) : k), (10 / 27 : k), (10 / 81 : k),
    (-(10 / 9) : k), (5 / 27648 * l : k), (25 / 6912 * l : k),
    (-(17 / 13824 * l) : k), (1 / 128 * l : k), (1 / 288 * l : k),
    (13 / 576 * l : k), (-(5 / 192 * l) : k), (-(1 / 32 * l) : k),
    (1 / 16 * l : k), (1 / 8 * l : k), (3 / 8 * l : k),
    (1 / 16 * l : k), (3 / 16 * l : k), (9 / 32 * l : k),
    (-(3 / 4 * l) : k), (-(3 / 8 * l) : k), (-(3 / 4 * l) : k),
    (-(1 / 81 * alpha) : k), (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k),
    (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
    (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
    (-(4 / 9 * alpha) : k), (35 / 62208 * beta : k), (49 / 5184 * beta : k),
    (-(7 / 1728 * beta) : k), (7 / 432 * beta : k), (-(7 / 216 * beta) : k),
    (7 / 144 * beta : k), (35 / 432 * beta : k), (35 / 1728 * beta : k),
    (7 / 36 * beta : k), (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k),
    (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k), (7 / 12 * beta : k),
    (1 / 576 * delta : k), (5 / 216 * delta : k), (-(5 / 216 * delta) : k),
    (5 / 36 * delta : k), (5 / 36 * delta : k), (-(5 / 12 * delta) : k),
    (-(1 / 18 * epsilon) : k), (2 / 9 * epsilon : k), (2 / 27 * epsilon : k),
    (-(2 / 3 * epsilon) : k), (1 / 192 * zeta : k), (1 / 24 * zeta : k),
    (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k),
    (-(1 / 36 * eta) : k), (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k),
    (1 / 72 * theta : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
    (1 * theta : k)]
    [
    [2, 0, 0, 1, 1], [1, 1, 1, 0, 1], [0, 3, 0, 0, 1], [0, 0, 1, 1, 1],
    [7, 0, 0, 0, 0], [5, 0, 1, 0, 0], [4, 2, 0, 0, 0], [4, 0, 0, 0, 1],
    [3, 1, 0, 1, 0], [3, 0, 2, 0, 0], [2, 2, 1, 0, 0], [1, 4, 0, 0, 0],
    [2, 0, 1, 0, 1], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 0, 3, 0, 0],
    [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1],
    [0, 0, 1, 2, 0], [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0],
    [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1],
    [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0],
    [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
    [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1],
    [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
    [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [2, 0, 0, 1, 0],
    [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
    [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0],
    [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]]

def kappaCubicInnerABCE610 (a b c e : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b * c ^ 2

def lambdaCubicInnerABCE610 (a b c e : k) : k :=
  15 * a * b ^ 2 * c + 5 * b ^ 4 + (-45 : k) * b ^ 2 * e + (-15 : k) * c ^ 3 + 135 * e ^ 2

def muCubicInnerABCE610 (a b c e : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 45 * a * b * c ^ 2 + 120 * b ^ 3 * c + (-540 : k) * b * c * e

def omicronCubicInnerABCE610 (a b c e : k) : k :=
  (-5 : k) * a * b ^ 4 + 30 * a * b ^ 2 * e + 45 * b ^ 2 * c ^ 2 + (-90 : k) * c ^ 2 * e

def primitiveCubicInnerABCE610 (a b c e : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + 45 * a ^ 2 * b * c ^ 2 + (-300 : k) * a * b ^ 3 * c + 1080 * a * b * c * e + (-48 : k) * b ^ 5 + 360 * b ^ 3 * e + 540 * b * c ^ 3

def kappaCubicFaceABCE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k)]
    [
    [1, 3, 0, 0, 0], [0, 1, 2, 0, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABCE610
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

def lambdaCubicFaceABCE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
    (-(5 / 81) : k), (5 / 9 : k)]
    [
    [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k), (-(10 / 27) : k), (-(5 / 6912 * l) : k),
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
    [1, 0, 0, 2, 0], [0, 1, 1, 1, 0], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
    [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
    [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
    [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
    [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
    [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
    [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]

def muCubicFaceABCE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 1458) : k), (5 / 162 : k), (20 / 243 : k),
    (-(10 / 27) : k)]
    [
    [2, 3, 0, 0, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1]]

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 54 : k), (-(5 / 27) : k), (-(5 / 27) : k),
    (-(5 / 27) : k), (35 / 248832 * l : k), (5 / 2304 * l : k),
    (1 / 144 * l : k), (1 / 96 * l : k), (1 / 192 * l : k),
    (1 / 16 * l : k), (3 / 128 * l : k), (-(1 / 8 * l) : k),
    (-(3 / 16 * l) : k), (-(3 / 8 * l) : k), (-(1 / 16 * l) : k),
    (3 / 8 * l : k), (2 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
    (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
    (4 / 9 * alpha : k), (7 / 15552 * beta : k), (7 / 1296 * beta : k),
    (7 / 5184 * beta : k), (7 / 432 * beta : k), (-(7 / 108 * beta) : k),
    (-(35 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
    (5 / 3456 * delta : k), (5 / 432 * delta : k), (5 / 216 * delta : k),
    (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(1 / 9 * epsilon) : k),
    (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k), (-(1 / 8 * zeta) : k),
    (1 / 2 * zeta : k), (-(1 / 18 * eta) : k), (1 / 3 * eta : k),
    (1 / 72 * theta : k), (1 / 6 * theta : k)]
    [
    [1, 2, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0],
    [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
    [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0],
    [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
    [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
    [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
    [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
    [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
    [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
    [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]]

def omicronCubicFaceABCE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 486) : k), (5 / 81 : k), (5 / 54 : k),
    (-(5 / 27) : k)]
    [
    [1, 4, 0, 0, 0], [1, 2, 0, 0, 1], [0, 2, 2, 0, 0], [0, 0, 2, 0, 1]]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoABCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (10 / 81 : k), (25 / 486 : k), (-(5 / 27) : k),
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
    [1, 1, 1, 1, 0], [0, 3, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 1, 2, 0],
    [4, 0, 0, 1, 0], [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0],
    [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1],
    [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0],
    [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
    [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0],
    [1, 3, 0, 0, 0], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
    [0, 0, 0, 1, 1], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
    [0, 0, 1, 1, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0]]

def primitiveCubicFaceABCE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 2916) : k), (5 / 324 : k), (-(25 / 243) : k),
    (-(4 / 243) : k), (10 / 27 : k), (10 / 81 : k),
    (5 / 27 : k)]
    [
    [3, 3, 0, 0, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0], [0, 5, 0, 0, 0],
    [1, 1, 1, 0, 1], [0, 3, 0, 0, 1], [0, 1, 3, 0, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoABCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 108) : k), (-(5 / 54) : k), (5 / 27 : k),
    (5 / 27 : k), (5 / 9 : k), (-(10 / 9) : k),
    (-(10 / 27) : k), (5 / 27648 * l : k), (25 / 6912 * l : k),
    (-(17 / 13824 * l) : k), (1 / 128 * l : k), (1 / 288 * l : k),
    (13 / 576 * l : k), (-(5 / 192 * l) : k), (-(1 / 32 * l) : k),
    (1 / 16 * l : k), (1 / 8 * l : k), (3 / 8 * l : k),
    (1 / 16 * l : k), (3 / 16 * l : k), (9 / 32 * l : k),
    (-(3 / 4 * l) : k), (-(3 / 8 * l) : k), (-(3 / 4 * l) : k),
    (-(1 / 81 * alpha) : k), (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k),
    (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
    (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
    (-(4 / 9 * alpha) : k), (35 / 62208 * beta : k), (49 / 5184 * beta : k),
    (-(7 / 1728 * beta) : k), (7 / 432 * beta : k), (-(7 / 216 * beta) : k),
    (7 / 144 * beta : k), (35 / 432 * beta : k), (35 / 1728 * beta : k),
    (7 / 36 * beta : k), (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k),
    (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k), (7 / 12 * beta : k),
    (1 / 576 * delta : k), (5 / 216 * delta : k), (-(5 / 216 * delta) : k),
    (5 / 36 * delta : k), (5 / 36 * delta : k), (-(5 / 12 * delta) : k),
    (-(1 / 18 * epsilon) : k), (2 / 9 * epsilon : k), (2 / 27 * epsilon : k),
    (-(2 / 3 * epsilon) : k), (1 / 192 * zeta : k), (1 / 24 * zeta : k),
    (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k),
    (-(1 / 36 * eta) : k), (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k),
    (1 / 72 * theta : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
    (1 * theta : k)]
    [
    [2, 2, 0, 1, 0], [2, 0, 0, 1, 1], [1, 1, 0, 2, 0], [1, 0, 2, 1, 0],
    [0, 2, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0], [7, 0, 0, 0, 0],
    [5, 0, 1, 0, 0], [4, 2, 0, 0, 0], [4, 0, 0, 0, 1], [3, 1, 0, 1, 0],
    [3, 0, 2, 0, 0], [2, 2, 1, 0, 0], [1, 4, 0, 0, 0], [2, 0, 1, 0, 1],
    [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 0, 3, 0, 0], [0, 3, 0, 1, 0],
    [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0],
    [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
    [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
    [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0],
    [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0],
    [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 2, 0],
    [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
    [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [1, 0, 2, 0, 0],
    [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
    [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
    [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [2, 1, 0, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
    [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]]

def kappaCubicInnerABDE610 (a b d e : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b ^ 2 * d + 270 * d * e

def lambdaCubicInnerABDE610 (a b d e : k) : k :=
  (-45 : k) * a * d ^ 2 + 5 * b ^ 4 + (-45 : k) * b ^ 2 * e + 135 * e ^ 2

def muCubicInnerABDE610 (a b d e : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 135 * a * b ^ 2 * d + (-270 : k) * a * d * e + (-270 : k) * b * d ^ 2

def omicronCubicInnerABDE610 (a b d e : k) : k :=
  (-5 : k) * a * b ^ 4 + 30 * a * b ^ 2 * e + 25 * b ^ 3 * d + (-90 : k) * b * d * e

def primitiveCubicInnerABDE610 (a b d e : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-135 : k) * a ^ 2 * b ^ 2 * d + (-270 : k) * a ^ 2 * d * e + 540 * a * b * d ^ 2 + (-48 : k) * b ^ 5 + 360 * b ^ 3 * e + (-1080 : k) * d ^ 3

def kappaCubicFaceABDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k), (10 / 9 : k)]
    [
    [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 0, 0, 1, 1]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABDE610
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
    [0, 1, 2, 0, 0], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
    [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0],
    [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
    [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
    [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [3, 0, 0, 0, 0],
    [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0],
    [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]

def lambdaCubicFaceABDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k),
    (5 / 9 : k)]
    [
    [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 0, 0, 0, 2]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (-(10 / 27) : k), (-(5 / 81) : k),
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
    [1, 2, 1, 0, 0], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [4, 1, 0, 0, 0],
    [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1],
    [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
    [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
    [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
    [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0],
    [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0],
    [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]

def muCubicFaceABDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 1458) : k), (5 / 54 : k), (-(5 / 27) : k),
    (-(5 / 27) : k)]
    [
    [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 0, 2, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 162 : k), (20 / 243 : k), (-(10 / 27) : k),
    (-(5 / 27) : k), (35 / 248832 * l : k), (5 / 2304 * l : k),
    (1 / 144 * l : k), (1 / 96 * l : k), (1 / 192 * l : k),
    (1 / 16 * l : k), (3 / 128 * l : k), (-(1 / 8 * l) : k),
    (-(3 / 16 * l) : k), (-(3 / 8 * l) : k), (-(1 / 16 * l) : k),
    (3 / 8 * l : k), (2 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
    (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
    (4 / 9 * alpha : k), (7 / 15552 * beta : k), (7 / 1296 * beta : k),
    (7 / 5184 * beta : k), (7 / 432 * beta : k), (-(7 / 108 * beta) : k),
    (-(35 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
    (5 / 3456 * delta : k), (5 / 432 * delta : k), (5 / 216 * delta : k),
    (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(1 / 9 * epsilon) : k),
    (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k), (-(1 / 8 * zeta) : k),
    (1 / 2 * zeta : k), (-(1 / 18 * eta) : k), (1 / 3 * eta : k),
    (1 / 72 * theta : k), (1 / 6 * theta : k)]
    [
    [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 0, 2, 1, 0],
    [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
    [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0],
    [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
    [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
    [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
    [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
    [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
    [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
    [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]]

def omicronCubicFaceABDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 486) : k), (5 / 81 : k), (25 / 486 : k),
    (-(5 / 27) : k)]
    [
    [1, 4, 0, 0, 0], [1, 2, 0, 0, 1], [0, 3, 0, 1, 0], [0, 1, 0, 1, 1]]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoABDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (10 / 81 : k), (5 / 54 : k), (-(5 / 27) : k),
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
    [1, 1, 1, 1, 0], [0, 2, 2, 0, 0], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0],
    [4, 0, 0, 1, 0], [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0],
    [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1],
    [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0],
    [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
    [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0],
    [1, 3, 0, 0, 0], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
    [0, 0, 0, 1, 1], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
    [0, 0, 1, 1, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0]]

def primitiveCubicFaceABDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 2916) : k), (-(5 / 108) : k), (-(4 / 243) : k),
    (-(5 / 54) : k), (5 / 27 : k), (10 / 81 : k),
    (-(10 / 27) : k)]
    [
    [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [0, 5, 0, 0, 0], [2, 0, 0, 1, 1],
    [1, 1, 0, 2, 0], [0, 3, 0, 0, 1], [0, 0, 0, 3, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoABDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 324 : k), (-(25 / 243) : k), (10 / 27 : k),
    (5 / 27 : k), (5 / 9 : k), (5 / 27 : k),
    (-(10 / 9) : k), (5 / 27648 * l : k), (25 / 6912 * l : k),
    (-(17 / 13824 * l) : k), (1 / 128 * l : k), (1 / 288 * l : k),
    (13 / 576 * l : k), (-(5 / 192 * l) : k), (-(1 / 32 * l) : k),
    (1 / 16 * l : k), (1 / 8 * l : k), (3 / 8 * l : k),
    (1 / 16 * l : k), (3 / 16 * l : k), (9 / 32 * l : k),
    (-(3 / 4 * l) : k), (-(3 / 8 * l) : k), (-(3 / 4 * l) : k),
    (-(1 / 81 * alpha) : k), (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k),
    (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
    (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
    (-(4 / 9 * alpha) : k), (35 / 62208 * beta : k), (49 / 5184 * beta : k),
    (-(7 / 1728 * beta) : k), (7 / 432 * beta : k), (-(7 / 216 * beta) : k),
    (7 / 144 * beta : k), (35 / 432 * beta : k), (35 / 1728 * beta : k),
    (7 / 36 * beta : k), (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k),
    (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k), (7 / 12 * beta : k),
    (1 / 576 * delta : k), (5 / 216 * delta : k), (-(5 / 216 * delta) : k),
    (5 / 36 * delta : k), (5 / 36 * delta : k), (-(5 / 12 * delta) : k),
    (-(1 / 18 * epsilon) : k), (2 / 9 * epsilon : k), (2 / 27 * epsilon : k),
    (-(2 / 3 * epsilon) : k), (1 / 192 * zeta : k), (1 / 24 * zeta : k),
    (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k),
    (-(1 / 36 * eta) : k), (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k),
    (1 / 72 * theta : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
    (1 * theta : k)]
    [
    [2, 1, 2, 0, 0], [1, 3, 1, 0, 0], [1, 1, 1, 0, 1], [1, 0, 2, 1, 0],
    [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 0, 1, 1, 1], [7, 0, 0, 0, 0],
    [5, 0, 1, 0, 0], [4, 2, 0, 0, 0], [4, 0, 0, 0, 1], [3, 1, 0, 1, 0],
    [3, 0, 2, 0, 0], [2, 2, 1, 0, 0], [1, 4, 0, 0, 0], [2, 0, 1, 0, 1],
    [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 0, 3, 0, 0], [0, 3, 0, 1, 0],
    [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0],
    [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
    [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
    [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0],
    [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0],
    [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 2, 0],
    [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
    [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [1, 0, 2, 0, 0],
    [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
    [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
    [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [2, 1, 0, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
    [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]]

def kappaCubicInnerBCDE610 (b c d e : k) : k :=
  (-5 : k) * b ^ 2 * d + (-5 : k) * b * c ^ 2 + 30 * d * e

def lambdaCubicInnerBCDE610 (b c d e : k) : k :=
  5 * b ^ 4 + (-45 : k) * b ^ 2 * e + (-90 : k) * b * c * d + (-15 : k) * c ^ 3 + 135 * e ^ 2

def muCubicInnerBCDE610 (b c d e : k) : k :=
  20 * b ^ 3 * c + (-90 : k) * b * c * e + (-45 : k) * b * d ^ 2 + (-45 : k) * c ^ 2 * d

def omicronCubicInnerBCDE610 (b c d e : k) : k :=
  25 * b ^ 3 * d + 45 * b ^ 2 * c ^ 2 + (-90 : k) * b * d * e + (-90 : k) * c ^ 2 * e + (-90 : k) * c * d ^ 2

def primitiveCubicInnerBCDE610 (b c d e : k) : k :=
  (-4 : k) * b ^ 5 + 30 * b ^ 3 * e + 135 * b ^ 2 * c * d + 45 * b * c ^ 3 + (-270 : k) * c * d * e + (-90 : k) * d ^ 3

def kappaCubicFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 27) : k), (-(5 / 27) : k), (10 / 9 : k)]
    [
    [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (7 / 6912 * l : k), (5 / 288 * l : k),
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
    [1, 3, 0, 0, 0], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
    [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0],
    [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
    [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
    [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [3, 0, 0, 0, 0],
    [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0],
    [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]

def lambdaCubicFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k), (-(10 / 27) : k),
    (-(5 / 81) : k), (5 / 9 : k)]
    [
    [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (-(5 / 27) : k), (-(5 / 6912 * l) : k),
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
    [1, 2, 1, 0, 0], [1, 0, 0, 2, 0], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
    [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
    [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
    [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
    [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
    [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
    [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]

def muCubicFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (20 / 243 : k), (-(10 / 27) : k), (-(5 / 27) : k),
    (-(5 / 27) : k)]
    [
    [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 1458) : k), (5 / 54 : k), (5 / 162 : k),
    (-(5 / 27) : k), (35 / 248832 * l : k), (5 / 2304 * l : k),
    (1 / 144 * l : k), (1 / 96 * l : k), (1 / 192 * l : k),
    (1 / 16 * l : k), (3 / 128 * l : k), (-(1 / 8 * l) : k),
    (-(3 / 16 * l) : k), (-(3 / 8 * l) : k), (-(1 / 16 * l) : k),
    (3 / 8 * l : k), (2 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
    (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
    (4 / 9 * alpha : k), (7 / 15552 * beta : k), (7 / 1296 * beta : k),
    (7 / 5184 * beta : k), (7 / 432 * beta : k), (-(7 / 108 * beta) : k),
    (-(35 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
    (5 / 3456 * delta : k), (5 / 432 * delta : k), (5 / 216 * delta : k),
    (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(1 / 9 * epsilon) : k),
    (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k), (-(1 / 8 * zeta) : k),
    (1 / 2 * zeta : k), (-(1 / 18 * eta) : k), (1 / 3 * eta : k),
    (1 / 72 * theta : k), (1 / 6 * theta : k)]
    [
    [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [1, 0, 0, 1, 1],
    [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
    [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0],
    [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
    [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
    [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
    [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
    [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
    [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
    [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]]

def omicronCubicFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (25 / 486 : k), (5 / 54 : k), (-(5 / 27) : k),
    (-(5 / 27) : k), (-(5 / 27) : k)]
    [
    [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1],
    [0, 0, 1, 2, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 486) : k), (5 / 81 : k), (10 / 81 : k),
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
    [1, 4, 0, 0, 0], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [4, 0, 0, 1, 0],
    [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
    [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
    [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
    [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
    [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
    [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
    [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
    [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]]

def primitiveCubicFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(4 / 243) : k), (10 / 81 : k), (5 / 9 : k),
    (5 / 27 : k), (-(10 / 9) : k), (-(10 / 27) : k)]
    [
    [0, 5, 0, 0, 0], [0, 3, 0, 0, 1], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
    [0, 0, 1, 1, 1], [0, 0, 0, 3, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 2916) : k), (-(5 / 108) : k), (5 / 324 : k),
    (-(25 / 243) : k), (-(5 / 54) : k), (10 / 27 : k),
    (5 / 27 : k), (5 / 27 : k), (5 / 27648 * l : k),
    (25 / 6912 * l : k), (-(17 / 13824 * l) : k), (1 / 128 * l : k),
    (1 / 288 * l : k), (13 / 576 * l : k), (-(5 / 192 * l) : k),
    (-(1 / 32 * l) : k), (1 / 16 * l : k), (1 / 8 * l : k),
    (3 / 8 * l : k), (1 / 16 * l : k), (3 / 16 * l : k),
    (9 / 32 * l : k), (-(3 / 4 * l) : k), (-(3 / 8 * l) : k),
    (-(3 / 4 * l) : k), (-(1 / 81 * alpha) : k), (-(1 / 27 * alpha) : k),
    (-(1 / 27 * alpha) : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
    (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
    (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (35 / 62208 * beta : k),
    (49 / 5184 * beta : k), (-(7 / 1728 * beta) : k), (7 / 432 * beta : k),
    (-(7 / 216 * beta) : k), (7 / 144 * beta : k), (35 / 432 * beta : k),
    (35 / 1728 * beta : k), (7 / 36 * beta : k), (-(7 / 36 * beta) : k),
    (-(7 / 72 * beta) : k), (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k),
    (7 / 12 * beta : k), (1 / 576 * delta : k), (5 / 216 * delta : k),
    (-(5 / 216 * delta) : k), (5 / 36 * delta : k), (5 / 36 * delta : k),
    (-(5 / 12 * delta) : k), (-(1 / 18 * epsilon) : k), (2 / 9 * epsilon : k),
    (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k), (1 / 192 * zeta : k),
    (1 / 24 * zeta : k), (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k),
    (-(1 / 4 * zeta) : k), (-(1 / 36 * eta) : k), (-(1 / 3 * eta) : k),
    (-(1 / 3 * eta) : k), (1 / 72 * theta : k), (1 / 6 * theta : k),
    (-(1 / 12 * theta) : k), (1 * theta : k)]
    [
    [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0],
    [2, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0], [1, 0, 2, 1, 0],
    [7, 0, 0, 0, 0], [5, 0, 1, 0, 0], [4, 2, 0, 0, 0], [4, 0, 0, 0, 1],
    [3, 1, 0, 1, 0], [3, 0, 2, 0, 0], [2, 2, 1, 0, 0], [1, 4, 0, 0, 0],
    [2, 0, 1, 0, 1], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 0, 3, 0, 0],
    [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1],
    [0, 0, 1, 2, 0], [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0],
    [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1],
    [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0],
    [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
    [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1],
    [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
    [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [2, 0, 0, 1, 0],
    [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
    [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0],
    [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]]

def kappaCubicInnerABCDE610 (a b c d e : k) : k :=
  5 * a * b ^ 3 + (-45 : k) * b ^ 2 * d + (-45 : k) * b * c ^ 2 + 270 * d * e

def lambdaCubicInnerABCDE610 (a b c d e : k) : k :=
  15 * a * b ^ 2 * c + (-45 : k) * a * d ^ 2 + 5 * b ^ 4 + (-45 : k) * b ^ 2 * e + (-90 : k) * b * c * d + (-15 : k) * c ^ 3 + 135 * e ^ 2

def muCubicInnerABCDE610 (a b c d e : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 135 * a * b ^ 2 * d + 45 * a * b * c ^ 2 + (-270 : k) * a * d * e + 120 * b ^ 3 * c + (-540 : k) * b * c * e + (-270 : k) * b * d ^ 2 + (-270 : k) * c ^ 2 * d

def omicronCubicInnerABCDE610 (a b c d e : k) : k :=
  (-5 : k) * a * b ^ 4 + 30 * a * b ^ 2 * e + 60 * a * b * c * d + 25 * b ^ 3 * d + 45 * b ^ 2 * c ^ 2 + (-90 : k) * b * d * e + (-90 : k) * c ^ 2 * e + (-90 : k) * c * d ^ 2

def primitiveCubicInnerABCDE610 (a b c d e : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-135 : k) * a ^ 2 * b ^ 2 * d + 45 * a ^ 2 * b * c ^ 2 + (-270 : k) * a ^ 2 * d * e + (-300 : k) * a * b ^ 3 * c + 1080 * a * b * c * e + 540 * a * b * d ^ 2 + 540 * a * c ^ 2 * d + (-48 : k) * b ^ 5 + 360 * b ^ 3 * e + 1620 * b ^ 2 * c * d + 540 * b * c ^ 3 + (-3240 : k) * c * d * e + (-1080 : k) * d ^ 3

def kappaCubicFaceABCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k),
    (10 / 9 : k)]
    [
    [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1]]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
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
    [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1],
    [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
    [0, 0, 0, 2, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0],
    [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1],
    [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
    [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
    [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]

def lambdaCubicFaceABCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
    (-(5 / 27) : k), (-(10 / 27) : k), (-(5 / 81) : k),
    (5 / 9 : k)]
    [
    [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
    [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2]]

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
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
    [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
    [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
    [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
    [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
    [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]]

def muCubicFaceABCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 1458) : k), (5 / 54 : k), (5 / 162 : k),
    (20 / 243 : k), (-(5 / 27) : k), (-(10 / 27) : k),
    (-(5 / 27) : k), (-(5 / 27) : k)]
    [
    [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
    [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (35 / 248832 * l : k), (5 / 2304 * l : k), (1 / 144 * l : k),
    (1 / 96 * l : k), (1 / 192 * l : k), (1 / 16 * l : k),
    (3 / 128 * l : k), (-(1 / 8 * l) : k), (-(3 / 16 * l) : k),
    (-(3 / 8 * l) : k), (-(1 / 16 * l) : k), (3 / 8 * l : k),
    (2 / 81 * alpha : k), (-(2 / 27 * alpha) : k), (-(2 / 27 * alpha) : k),
    (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
    (7 / 15552 * beta : k), (7 / 1296 * beta : k), (7 / 5184 * beta : k),
    (7 / 432 * beta : k), (-(7 / 108 * beta) : k), (-(35 / 432 * beta) : k),
    (7 / 36 * beta : k), (7 / 72 * beta : k), (5 / 3456 * delta : k),
    (5 / 432 * delta : k), (5 / 216 * delta : k), (-(5 / 36 * delta) : k),
    (-(5 / 72 * delta) : k), (-(1 / 9 * epsilon) : k), (-(2 / 9 * epsilon) : k),
    (1 / 216 * zeta : k), (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k),
    (-(1 / 18 * eta) : k), (1 / 3 * eta : k), (1 / 72 * theta : k),
    (1 / 6 * theta : k)]
    [
    [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
    [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0],
    [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
    [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
    [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
    [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
    [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
    [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
    [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]]

def omicronCubicFaceABCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 486) : k), (5 / 81 : k), (10 / 81 : k),
    (25 / 486 : k), (5 / 54 : k), (-(5 / 27) : k),
    (-(5 / 27) : k), (-(5 / 27) : k)]
    [
    [1, 4, 0, 0, 0], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [0, 3, 0, 1, 0],
    [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0]]

set_option maxHeartbeats 16000000 in
def degreeZeroOmicronCubicNoABCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
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
    [4, 0, 0, 1, 0], [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0],
    [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1],
    [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0],
    [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
    [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0],
    [1, 3, 0, 0, 0], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
    [0, 0, 0, 1, 1], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
    [0, 0, 1, 1, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0]]

def primitiveCubicFaceABCDE610 (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (-(5 / 2916) : k), (-(5 / 108) : k), (5 / 324 : k),
    (-(25 / 243) : k), (-(4 / 243) : k), (-(5 / 54) : k),
    (10 / 27 : k), (5 / 27 : k), (5 / 27 : k),
    (10 / 81 : k), (5 / 9 : k), (5 / 27 : k),
    (-(10 / 9) : k), (-(10 / 27) : k)]
    [
    [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0],
    [0, 5, 0, 0, 0], [2, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0],
    [1, 0, 2, 1, 0], [0, 3, 0, 0, 1], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
    [0, 0, 1, 1, 1], [0, 0, 0, 3, 0]]

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoABCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  Max11ReflectDeg.polyOf [A, B, C, D, E]
    [
    (5 / 27648 * l : k), (25 / 6912 * l : k), (-(17 / 13824 * l) : k),
    (1 / 128 * l : k), (1 / 288 * l : k), (13 / 576 * l : k),
    (-(5 / 192 * l) : k), (-(1 / 32 * l) : k), (1 / 16 * l : k),
    (1 / 8 * l : k), (3 / 8 * l : k), (1 / 16 * l : k),
    (3 / 16 * l : k), (9 / 32 * l : k), (-(3 / 4 * l) : k),
    (-(3 / 8 * l) : k), (-(3 / 4 * l) : k), (-(1 / 81 * alpha) : k),
    (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k), (4 / 27 * alpha : k),
    (4 / 27 * alpha : k), (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k),
    (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
    (35 / 62208 * beta : k), (49 / 5184 * beta : k), (-(7 / 1728 * beta) : k),
    (7 / 432 * beta : k), (-(7 / 216 * beta) : k), (7 / 144 * beta : k),
    (35 / 432 * beta : k), (35 / 1728 * beta : k), (7 / 36 * beta : k),
    (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k), (-(7 / 18 * beta) : k),
    (-(7 / 108 * beta) : k), (7 / 12 * beta : k), (1 / 576 * delta : k),
    (5 / 216 * delta : k), (-(5 / 216 * delta) : k), (5 / 36 * delta : k),
    (5 / 36 * delta : k), (-(5 / 12 * delta) : k), (-(1 / 18 * epsilon) : k),
    (2 / 9 * epsilon : k), (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k),
    (1 / 192 * zeta : k), (1 / 24 * zeta : k), (1 / 12 * zeta : k),
    (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k), (-(1 / 36 * eta) : k),
    (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k), (1 / 72 * theta : k),
    (1 / 6 * theta : k), (-(1 / 12 * theta) : k), (1 * theta : k)]
    [
    [7, 0, 0, 0, 0], [5, 0, 1, 0, 0], [4, 2, 0, 0, 0], [4, 0, 0, 0, 1],
    [3, 1, 0, 1, 0], [3, 0, 2, 0, 0], [2, 2, 1, 0, 0], [1, 4, 0, 0, 0],
    [2, 0, 1, 0, 1], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 0, 3, 0, 0],
    [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1],
    [0, 0, 1, 2, 0], [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0],
    [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1],
    [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0],
    [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
    [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1],
    [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 2], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
    [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [2, 0, 0, 1, 0],
    [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
    [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
    [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0],
    [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]]

end CubicKills610


/-! ## Exhaustiveness of the 31 argmax cones -/

section CubicExhaust610

variable {k : Type*} [Field k] [CharZero k]

inductive CubicSupportCone610 (A B C D E : k[X]) : Prop
  | coneA : CubicRatioConeA610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneB : CubicRatioConeB610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneC : CubicRatioConeC610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneD : CubicRatioConeD610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneE : CubicRatioConeE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneAB : CubicRatioConeAB610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneAC : CubicRatioConeAC610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneAD : CubicRatioConeAD610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneAE : CubicRatioConeAE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneBC : CubicRatioConeBC610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneBD : CubicRatioConeBD610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneBE : CubicRatioConeBE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneCD : CubicRatioConeCD610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneCE : CubicRatioConeCE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneDE : CubicRatioConeDE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneABC : CubicRatioConeABC610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneABD : CubicRatioConeABD610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneABE : CubicRatioConeABE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneACD : CubicRatioConeACD610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneACE : CubicRatioConeACE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneADE : CubicRatioConeADE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneBCD : CubicRatioConeBCD610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneBCE : CubicRatioConeBCE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneBDE : CubicRatioConeBDE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneCDE : CubicRatioConeCDE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneABCD : CubicRatioConeABCD610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneABCE : CubicRatioConeABCE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneABDE : CubicRatioConeABDE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneACDE : CubicRatioConeACDE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneBCDE : CubicRatioConeBCDE610 A B C D E →
      CubicSupportCone610 A B C D E
  | coneABCDE : CubicRatioConeABCDE610 A B C D E →
      CubicSupportCone610 A B C D E
  | allConst : A.natDegree = 0 ∧ B.natDegree = 0 ∧ C.natDegree = 0 ∧
      D.natDegree = 0 ∧ E.natDegree = 0 → CubicSupportCone610 A B C D E

end CubicExhaust610


/-! ## Stage A residual: the source lies in `R = {A}` -/

section CubicADominant610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

end CubicADominant610



end Max11DegreeRoutes

