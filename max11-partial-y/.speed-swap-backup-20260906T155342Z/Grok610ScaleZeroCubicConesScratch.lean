import Grok610ScaleZeroConeKappaMuScratch

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

theorem cubicC610_add (A C0 : k[X]) :
    cubicC610 A C0 + (1 / 3 : k) • A ^ 2 = C0 := by
  simp only [cubicC610]
  exact sub_add_cancel _ _

theorem cubicD610_add (A B D0 : k[X]) :
    cubicD610 A B D0 + (1 / 3 : k) • (A * B) = D0 := by
  simp only [cubicD610]
  exact sub_add_cancel _ _

set_option maxHeartbeats 8000000 in
theorem cubicE610_inv (A C0 E0 : k[X]) :
    E0 =
      cubicE610 A C0 E0 + (1 / 3 : k) • (A * cubicC610 A C0) +
        (1 / 27 : k) • A ^ 3 := by
  simp only [cubicC610, cubicE610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

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
  (-(5 / 243 : k)) • (A ^ 2 * B ^ 2 * C)
  - (5 / 243 : k) • (A * B ^ 4)
  + (5 / 81 : k) • (A ^ 2 * D ^ 2)
  + (10 / 81 : k) • (A * B ^ 2 * E)
  + (20 / 81 : k) • (A * B * C * D)
  + (5 / 243 : k) • (A * C ^ 3)
  + (20 / 243 : k) • (B ^ 3 * D)
  + (10 / 81 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (A * E ^ 2)
  - (10 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C ^ 2 * E)
  - (5 / 27 : k) • (C * D ^ 2)
  + (1 / 13824 * l : k) • (A ^ 5 * B)
  + (1 / 2304 * l : k) • (A ^ 4 * D)
  + (1 / 576 * l : k) • (A ^ 3 * B * C)
  - (5 / 384 * l : k) • (A ^ 2 * B ^ 3)
  + (1 / 32 * l : k) • (A ^ 2 * B * E)
  + (1 / 32 * l : k) • (A ^ 2 * C * D)
  + (5 / 32 * l : k) • (A * B ^ 2 * D)
  + (3 / 32 * l : k) • (A * B * C ^ 2)
  + (3 / 32 * l : k) • (B ^ 3 * C)
  - (3 / 8 * l : k) • (A * D * E)
  - (3 / 8 * l : k) • (B * C * E)
  - (3 / 16 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A ^ 2 * B * D)
  + (8 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (5 / 243 * alpha : k) • B ^ 4
  - (4 / 27 * alpha : k) • (A * C * E)
  - (4 / 27 * alpha : k) • (A * D ^ 2)
  - (4 / 27 * alpha : k) • (B ^ 2 * E)
  - (8 / 27 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  + (7 / 20736 * beta : k) • (A ^ 4 * B)
  + (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 864 * beta : k) • (A ^ 2 * B * C)
  + (175 / 7776 * beta : k) • (A * B ^ 3)
  - (7 / 72 * beta : k) • (A * B * E)
  - (7 / 72 * beta : k) • (A * C * D)
  - (35 / 432 * beta : k) • (B ^ 2 * D)
  - (35 / 432 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  + (5 / 2592 * delta : k) • (A ^ 3 * B)
  + (5 / 144 * delta : k) • (A ^ 2 * D)
  + (5 / 72 * delta : k) • (A * B * C)
  + (35 / 1296 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (B * E)
  - (5 / 36 * delta : k) • (C * D)
  + (2 / 27 * epsilon : k) • (A * B ^ 2)
  - (2 / 9 * epsilon : k) • (A * E)
  - (2 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  + (1 / 48 * zeta : k) • (A ^ 2 * B)
  - (1 / 4 * zeta : k) • (A * D)
  - (1 / 4 * zeta : k) • (B * C)
  - (1 / 9 * eta : k) • (A * C)
  - (1 / 9 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  - (1 / 12 * theta : k) • (A * B)
  + (1 / 6 * theta : k) • D


set_option maxHeartbeats 16000000 in
def degreeZeroAlphaGroupCubic610
    (A B C D E : k[X]) : k[X] :=
  (-(1 / 81 : k)) • (A ^ 2 * B ^ 3)
  - (1 / 27 : k) • (A ^ 2 * B * E)
  - (1 / 27 : k) • (A ^ 2 * C * D)
  + (4 / 27 : k) • (A * B ^ 2 * D)
  + (4 / 27 : k) • (A * B * C ^ 2)
  + (4 / 27 : k) • (B ^ 3 * C)
  - (4 / 9 : k) • (A * D * E)
  - (4 / 9 : k) • (B * C * E)
  - (4 / 9 : k) • (B * D ^ 2)
  - (4 / 9 : k) • (C ^ 2 * D)


set_option maxHeartbeats 16000000 in
def degreeZeroBaseGroupCubic610
    (l : k) (A B C D E : k[X]) : k[X] :=
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


set_option maxHeartbeats 16000000 in
def degreeZeroBetaGroupCubic610
    (A B C D E : k[X]) : k[X] :=
  (35 / 62208 : k) • A ^ 6
  + (49 / 5184 : k) • (A ^ 4 * C)
  - (7 / 1728 : k) • (A ^ 3 * B ^ 2)
  + (7 / 432 : k) • (A ^ 3 * E)
  - (7 / 216 : k) • (A ^ 2 * B * D)
  + (7 / 144 : k) • (A ^ 2 * C ^ 2)
  + (35 / 432 : k) • (A * B ^ 2 * C)
  + (35 / 1728 : k) • B ^ 4
  + (7 / 36 : k) • (A * C * E)
  - (7 / 36 : k) • (A * D ^ 2)
  - (7 / 72 : k) • (B ^ 2 * E)
  - (7 / 18 : k) • (B * C * D)
  - (7 / 108 : k) • C ^ 3
  + (7 / 12 : k) • E ^ 2


set_option maxHeartbeats 16000000 in
def degreeZeroDeltaGroupCubic610
    (A B C D : k[X]) : k[X] :=
  (1 / 576 : k) • A ^ 5
  + (5 / 216 : k) • (A ^ 3 * C)
  - (5 / 216 : k) • (A ^ 2 * B ^ 2)
  + (5 / 36 : k) • (A * C ^ 2)
  + (5 / 36 : k) • (B ^ 2 * C)
  - (5 / 12 : k) • D ^ 2


set_option maxHeartbeats 16000000 in
def degreeZeroEpsilonGroupCubic610
    (A B C D : k[X]) : k[X] :=
  (-(1 / 18 : k)) • (A ^ 2 * D)
  + (2 / 9 : k) • (A * B * C)
  + (2 / 27 : k) • B ^ 3
  - (2 / 3 : k) • (C * D)


set_option maxHeartbeats 16000000 in
def degreeZeroEtaGroupCubic610
    (A B C D : k[X]) : k[X] :=
  (-(1 / 36 : k)) • (A ^ 2 * B)
  - (1 / 3 : k) • (A * D)
  - (1 / 3 : k) • (B * C)


set_option maxHeartbeats 16000000 in
def degreeZeroThetaGroupCubic610
    (A B C E : k[X]) : k[X] :=
  (1 / 72 : k) • A ^ 3
  + (1 / 6 : k) • (A * C)
  - (1 / 12 : k) • B ^ 2
  + (1 : k) • E


set_option maxHeartbeats 16000000 in
def degreeZeroZetaGroupCubic610
    (A B C D : k[X]) : k[X] :=
  (1 / 192 : k) • A ^ 4
  + (1 / 24 : k) • (A ^ 2 * C)
  + (1 / 12 : k) • (A * B ^ 2)
  - (1 / 2 : k) • (B * D)
  - (1 / 4 : k) • C ^ 2


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

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveCubic610_eq_flat
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E =
      degreeZeroPrimitiveCubicFlat610 l alpha beta delta epsilon zeta
        eta theta A B C D E := by
  simp only [degreeZeroPrimitiveCubic610,
    degreeZeroPrimitiveCubicFlat610, degreeZeroBaseGroupCubic610,
    degreeZeroAlphaGroupCubic610, degreeZeroBetaGroupCubic610,
    degreeZeroDeltaGroupCubic610, degreeZeroEpsilonGroupCubic610,
    degreeZeroZetaGroupCubic610, degreeZeroEtaGroupCubic610,
    degreeZeroThetaGroupCubic610, smul_add, smul_sub, smul_smul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


end CubicIntegrals610


/-! ## Transport identities -/

section CubicTransport610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta theta
        A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E := by
  simp only [degreeZeroKappaPolynomial610, degreeZeroKappaCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta theta
        A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E := by
  simp only [degreeZeroLambdaPolynomial610, degreeZeroLambdaCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta theta
        A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E := by
  simp only [degreeZeroMuPolynomial610, degreeZeroMuCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem degreeZeroRawFourthTailPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroRawFourthTailPolynomial610 l alpha beta delta epsilon
        zeta eta theta A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroRawFourthTailCubic610 l alpha beta delta epsilon zeta
        eta theta A B C D E := by
  simp only [degreeZeroRawFourthTailPolynomial610, degreeZeroRawFourthTailCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E := by
  simp only [degreeZeroOmicronPolynomial610]
  rw [degreeZeroRawFourthTailPolynomial610_eq_cubic,
    degreeZeroKappaPolynomial610_eq_cubic,
    degreeZeroLambdaPolynomial610_eq_cubic]
  simp only [degreeZeroOmicronCubic610, degreeZeroRawFourthTailCubic610, degreeZeroKappaCubic610, degreeZeroLambdaCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem degreeZeroBaseGroupPolynomial610_eq_cubic
    (l : k) (A B C D E : k[X]) :
    degreeZeroBaseGroupPolynomial610 l A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroBaseGroupCubic610 l A B C D E := by
  simp only [degreeZeroBaseGroupPolynomial610, degreeZeroBaseGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem degreeZeroAlphaGroupPolynomial610_eq_cubic
    (A B C D E : k[X]) :
    degreeZeroAlphaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroAlphaGroupCubic610 A B C D E := by
  simp only [degreeZeroAlphaGroupPolynomial610, degreeZeroAlphaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem degreeZeroBetaGroupPolynomial610_eq_cubic
    (A B C D E : k[X]) :
    degreeZeroBetaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroBetaGroupCubic610 A B C D E := by
  simp only [degreeZeroBetaGroupPolynomial610, degreeZeroBetaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem degreeZeroDeltaGroupPolynomial610_eq_cubic
    (A B C D : k[X]) :
    degreeZeroDeltaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B)) =
      degreeZeroDeltaGroupCubic610 A B C D := by
  simp only [degreeZeroDeltaGroupPolynomial610, degreeZeroDeltaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem degreeZeroEpsilonGroupPolynomial610_eq_cubic
    (A B C D : k[X]) :
    degreeZeroEpsilonGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B)) =
      degreeZeroEpsilonGroupCubic610 A B C D := by
  simp only [degreeZeroEpsilonGroupPolynomial610, degreeZeroEpsilonGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem degreeZeroZetaGroupPolynomial610_eq_cubic
    (A B C D : k[X]) :
    degreeZeroZetaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B)) =
      degreeZeroZetaGroupCubic610 A B C D := by
  simp only [degreeZeroZetaGroupPolynomial610, degreeZeroZetaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem degreeZeroEtaGroupPolynomial610_eq_cubic
    (A B C D : k[X]) :
    degreeZeroEtaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2) (D + (1 / 3 : k) • (A * B)) =
      degreeZeroEtaGroupCubic610 A B C D := by
  simp only [degreeZeroEtaGroupPolynomial610, degreeZeroEtaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem degreeZeroThetaGroupPolynomial610_eq_cubic
    (A B C E : k[X]) :
    degreeZeroThetaGroupPolynomial610 A B (C + (1 / 3 : k) • A ^ 2)
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroThetaGroupCubic610 A B C E := by
  simp only [degreeZeroThetaGroupPolynomial610, degreeZeroThetaGroupCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitivePolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
        eta theta A B (C + (1 / 3 : k) • A ^ 2)
        (D + (1 / 3 : k) • (A * B))
        (E + (1 / 3 : k) • (A * C) + (1 / 27 : k) • A ^ 3) =
      degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveCubic610, degreeZeroBaseGroupPolynomial610_eq_cubic,
    degreeZeroAlphaGroupPolynomial610_eq_cubic,
    degreeZeroBetaGroupPolynomial610_eq_cubic,
    degreeZeroDeltaGroupPolynomial610_eq_cubic,
    degreeZeroEpsilonGroupPolynomial610_eq_cubic,
    degreeZeroZetaGroupPolynomial610_eq_cubic,
    degreeZeroEtaGroupPolynomial610_eq_cubic,
    degreeZeroThetaGroupPolynomial610_eq_cubic]
  all_goals module


end CubicTransport610


/-! ## Residual in cubic letters -/

section CubicResidual610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 32000000 in
theorem normalized610ScaleZero_cubicResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C D E : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
            eta theta A B C D E) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0,
      ht, hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg,
      _, _, _, _, _⟩ :=
    normalized610ScaleZero_coneKappaMuResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, cubicC610 A C0,
    cubicD610 A B D0, cubicE610 A C0 E0, ht, hj, hjdiv, hHsq, ?_, ?_, ?_,
    ?_, ?_⟩
  · have hC0 := (cubicC610_add A C0).symm
    have hD0 := (cubicD610_add A B D0).symm
    have hE0 := cubicE610_inv A C0 E0
    rw [hC0, hD0, hE0] at hder
    rw [degreeZeroPrimitivePolynomial610_eq_cubic] at hder
    exact hder
  · have hC0 := (cubicC610_add A C0).symm
    have hD0 := (cubicD610_add A B D0).symm
    have hE0 := cubicE610_inv A C0 E0
    rw [hC0, hD0, hE0] at hlamDeg
    rw [degreeZeroLambdaPolynomial610_eq_cubic] at hlamDeg
    exact hlamDeg
  · have hC0 := (cubicC610_add A C0).symm
    have hD0 := (cubicD610_add A B D0).symm
    have hE0 := cubicE610_inv A C0 E0
    rw [hC0, hD0, hE0] at hkapDeg
    rw [degreeZeroKappaPolynomial610_eq_cubic] at hkapDeg
    exact hkapDeg
  · have hC0 := (cubicC610_add A C0).symm
    have hD0 := (cubicD610_add A B D0).symm
    have hE0 := cubicE610_inv A C0 E0
    rw [hC0, hD0, hE0] at hmuDeg
    rw [degreeZeroMuPolynomial610_eq_cubic] at hmuDeg
    exact hmuDeg
  · have hC0 := (cubicC610_add A C0).symm
    have hD0 := (cubicD610_add A B D0).symm
    have hE0 := cubicE610_inv A C0 E0
    rw [hC0, hD0, hE0] at homiDeg
    rw [degreeZeroOmicronPolynomial610_eq_cubic] at homiDeg
    exact homiDeg

end CubicResidual610


/-! ## Degree helpers -/

section CubicDegreeHelpers610

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_pow_mul5_le610
    (A B C D E : k[X]) (ia ib ic id ie : ℕ) :
    (A ^ ia * B ^ ib * C ^ ic * D ^ id * E ^ ie).natDegree ≤
      ia * A.natDegree + ib * B.natDegree + ic * C.natDegree +
        id * D.natDegree + ie * E.natDegree := by
  have hA : (A ^ ia).natDegree ≤ ia * A.natDegree := (natDegree_pow A ia).le
  have hB : (B ^ ib).natDegree ≤ ib * B.natDegree := (natDegree_pow B ib).le
  have hC : (C ^ ic).natDegree ≤ ic * C.natDegree := (natDegree_pow C ic).le
  have hD : (D ^ id).natDegree ≤ id * D.natDegree := (natDegree_pow D id).le
  have hE : (E ^ ie).natDegree ≤ ie * E.natDegree := (natDegree_pow E ie).le
  have hAB :
      (A ^ ia * B ^ ib).natDegree ≤ ia * A.natDegree + ib * B.natDegree :=
    (natDegree_mul_le (p := A ^ ia) (q := B ^ ib)).trans (add_le_add hA hB)
  have hABC :
      (A ^ ia * B ^ ib * C ^ ic).natDegree ≤
        ia * A.natDegree + ib * B.natDegree + ic * C.natDegree :=
    (natDegree_mul_le (p := A ^ ia * B ^ ib) (q := C ^ ic)).trans
      (add_le_add hAB hC)
  have hABCD :
      (A ^ ia * B ^ ib * C ^ ic * D ^ id).natDegree ≤
        ia * A.natDegree + ib * B.natDegree + ic * C.natDegree +
          id * D.natDegree :=
    (natDegree_mul_le (p := A ^ ia * B ^ ib * C ^ ic) (q := D ^ id)).trans
      (add_le_add hABC hD)
  exact
    (natDegree_mul_le (p := A ^ ia * B ^ ib * C ^ ic * D ^ id)
        (q := E ^ ie)).trans
      (add_le_add hABCD hE)

theorem natDegree_smul_pow_mul5_le610
    (c : k) (A B C D E : k[X]) (ia ib ic id ie : ℕ) :
    (c • (A ^ ia * B ^ ib * C ^ ic * D ^ id * E ^ ie)).natDegree ≤
      ia * A.natDegree + ib * B.natDegree + ic * C.natDegree +
        id * D.natDegree + ie * E.natDegree :=
  (natDegree_smul_le610 c _).trans
    (natDegree_pow_mul5_le610 A B C D E ia ib ic id ie)

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
  (5 / 243 : k) • B ^ 4

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoB610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_B_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceB610 A B C D E +
        degreeZeroLambdaCubicNoB610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceB610, degreeZeroLambdaCubicNoB610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoB610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeB610 A B C D E) :
    (degreeZeroLambdaCubicNoB610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroLambdaCubicNoB610]
  compute_degree
  omega


theorem cubicCone_B_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeB610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt⟩
    omega
  have hc : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (lambdaCubicFaceB610 A B C D E).natDegree = 4 * B.natDegree := by
    simp only [lambdaCubicFaceB610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoB610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_B_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt⟩
  omega


def lambdaCubicFaceC610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • C ^ 3

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoC610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_C_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceC610 A B C D E +
        degreeZeroLambdaCubicNoC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceC610, degreeZeroLambdaCubicNoC610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeC610 A B C D E) :
    (degreeZeroLambdaCubicNoC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroLambdaCubicNoC610]
  compute_degree
  omega


theorem cubicCone_C_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeC610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt⟩
    omega
  have hc : (-(5 / 81 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicFaceC610 A B C D E).natDegree = 3 * C.natDegree := by
    simp only [lambdaCubicFaceC610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoC610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_C_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt⟩
  omega


def primitiveCubicFaceD610 (A B C D E : k[X]) : k[X] :=
  (-(10 / 27 : k)) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoD610
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_D_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceD610 A B C D E +
        degreeZeroPrimitiveCubicNoD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceD610, degreeZeroPrimitiveCubicNoD610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeD610 A B C D E) :
    (degreeZeroPrimitiveCubicNoD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * D.natDegree := by
  rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : 5 * E.natDegree + 1 ≤ 6 * D.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroPrimitiveCubicNoD610]
  compute_degree
  omega


theorem cubicCone_D_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeD610 A B C D E)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt⟩
    omega
  have hc : (-(10 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hlead : (primitiveCubicFaceD610 A B C D E).natDegree = 3 * D.natDegree := by
    simp only [primitiveCubicFaceD610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroPrimitiveCubicNoD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroPrimitiveCubic610_eq_D_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt⟩
  omega


def lambdaCubicFaceE610 (A B C D E : k[X]) : k[X] :=
  (5 / 9 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoE610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_E_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceE610 A B C D E +
        degreeZeroLambdaCubicNoE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceE610, degreeZeroLambdaCubicNoE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeE610 A B C D E) :
    (degreeZeroLambdaCubicNoE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hEpos, hAlt, hBlt, hClt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 2 * B.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 3 * C.natDegree + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 6 * D.natDegree + 1 ≤ 5 * E.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroLambdaCubicNoE610]
  compute_degree
  omega


theorem cubicCone_E_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeE610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hEpos, hAlt, hBlt, hClt, hDlt⟩
    omega
  have hc : (5 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (lambdaCubicFaceE610 A B C D E).natDegree = 2 * E.natDegree := by
    simp only [lambdaCubicFaceE610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_E_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, hAlt, hBlt, hClt, hDlt⟩
  omega


def kappaCubicFaceAB610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoAB610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_AB_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceAB610 A B C D E +
        degreeZeroKappaCubicNoAB610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceAB610, degreeZeroKappaCubicNoAB610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoAB610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeAB610 A B C D E) :
    (degreeZeroKappaCubicNoAB610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaCubicNoAB610]
  compute_degree
  omega


theorem cubicCone_AB_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeAB610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt⟩
    omega
  have hc : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceAB610 A B C D E).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaCubicFaceAB610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoAB610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_AB_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt⟩
  omega


def lambdaCubicFaceAC610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • C ^ 3

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoAC610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_AC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceAC610 A B C D E +
        degreeZeroLambdaCubicNoAC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceAC610, degreeZeroLambdaCubicNoAC610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoAC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeAC610 A B C D E) :
    (degreeZeroLambdaCubicNoAC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroLambdaCubicNoAC610]
  compute_degree
  omega


theorem cubicCone_AC_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeAC610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt⟩
    omega
  have hc : (-(5 / 81 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicFaceAC610 A B C D E).natDegree = 3 * C.natDegree := by
    simp only [lambdaCubicFaceAC610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoAC610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_AC_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt⟩
  omega


def lambdaCubicFaceAD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoAD610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_AD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceAD610 A B C D E +
        degreeZeroLambdaCubicNoAD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceAD610, degreeZeroLambdaCubicNoAD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoAD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeAD610 A B C D E) :
    (degreeZeroLambdaCubicNoAD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroLambdaCubicNoAD610]
  compute_degree
  omega


theorem cubicCone_AD_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeAD610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicFaceAD610 A B C D E).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [lambdaCubicFaceAD610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoAD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_AD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt⟩
  omega


def lambdaCubicFaceAE610 (A B C D E : k[X]) : k[X] :=
  (5 / 9 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoAE610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_AE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceAE610 A B C D E +
        degreeZeroLambdaCubicNoAE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceAE610, degreeZeroLambdaCubicNoAE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoAE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeAE610 A B C D E) :
    (degreeZeroLambdaCubicNoAE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroLambdaCubicNoAE610]
  compute_degree
  omega


theorem cubicCone_AE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeAE610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt⟩
    omega
  have hc : (5 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (lambdaCubicFaceAE610 A B C D E).natDegree = 2 * E.natDegree := by
    simp only [lambdaCubicFaceAE610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoAE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_AE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt⟩
  omega


def kappaCubicFaceBC610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B * C ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoBC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)
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
theorem degreeZeroKappaCubic610_eq_BC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceBC610 A B C D E +
        degreeZeroKappaCubicNoBC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceBC610, degreeZeroKappaCubicNoBC610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoBC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBC610 A B C D E) :
    (degreeZeroKappaCubicNoBC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      B.natDegree + 2 * C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaCubicNoBC610]
  compute_degree
  omega


theorem cubicCone_BC_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBC610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaCubicFaceBC610 A B C D E).natDegree = B.natDegree + 2 * C.natDegree := by
    simp only [kappaCubicFaceBC610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoBC610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_BC_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt⟩
  omega


def kappaCubicFaceBD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoBD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
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
theorem degreeZeroKappaCubic610_eq_BD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceBD610 A B C D E +
        degreeZeroKappaCubicNoBD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceBD610, degreeZeroKappaCubicNoBD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoBD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBD610 A B C D E) :
    (degreeZeroKappaCubicNoBD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaCubicNoBD610]
  compute_degree
  omega


theorem cubicCone_BD_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBD610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaCubicFaceBD610 A B C D E).natDegree = 2 * B.natDegree + D.natDegree := by
    simp only [kappaCubicFaceBD610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hrest := degreeZeroKappaCubicNoBD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_BD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt⟩
  omega


def lambdaCubicFaceCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 81 : k)) • C ^ 3

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoCD610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_CD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceCD610 A B C D E +
        degreeZeroLambdaCubicNoCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceCD610, degreeZeroLambdaCubicNoCD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCD610 A B C D E) :
    (degreeZeroLambdaCubicNoCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroLambdaCubicNoCD610]
  compute_degree
  omega


theorem cubicCone_CD_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCD610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt⟩
    omega
  have hc : (-(5 / 81 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicFaceCD610 A B C D E).natDegree = 3 * C.natDegree := by
    simp only [lambdaCubicFaceCD610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoCD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_CD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt⟩
  omega


def omicronCubicFaceCE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoCE610
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_CE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceCE610 A B C D E +
        degreeZeroOmicronCubicNoCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicFaceCE610, degreeZeroOmicronCubicNoCE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCE610 A B C D E) :
    (degreeZeroOmicronCubicNoCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroOmicronCubicNoCE610]
  compute_degree
  omega


theorem cubicCone_CE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCE610 A B C D E)
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (omicronCubicFaceCE610 A B C D E).natDegree = 2 * C.natDegree + E.natDegree := by
    simp only [omicronCubicFaceCE610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hrest := degreeZeroOmicronCubicNoCE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroOmicronCubic610_eq_CE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt⟩
  omega


def kappaCubicFaceDE610 (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoDE610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_DE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceDE610 A B C D E +
        degreeZeroKappaCubicNoDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceDE610, degreeZeroKappaCubicNoDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeDE610 A B C D E) :
    (degreeZeroKappaCubicNoDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroKappaCubicNoDE610]
  compute_degree
  omega


theorem cubicCone_DE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeDE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceDE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaCubicFaceDE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_DE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt⟩
  omega


def kappaCubicFaceABE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABE610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_ABE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceABE610 A B C D E +
        degreeZeroKappaCubicNoABE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceABE610, degreeZeroKappaCubicNoABE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoABE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABE610 A B C D E) :
    (degreeZeroKappaCubicNoABE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroKappaCubicNoABE610]
  compute_degree
  omega


theorem cubicCone_ABE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt⟩
    omega
  have hc : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceABE610 A B C D E).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaCubicFaceABE610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoABE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_ABE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt⟩
  omega


def muCubicFaceACD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * D)

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoACD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 54 : k) • (A * B ^ 2 * D)
  + (5 / 162 : k) • (A * B * C ^ 2)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (5 / 27 : k) • (A * D * E)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
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
theorem degreeZeroMuCubic610_eq_ACD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceACD610 A B C D E +
        degreeZeroMuCubicNoACD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroMuCubic610, muCubicFaceACD610, degreeZeroMuCubicNoACD610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoACD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACD610 A B C D E) :
    (degreeZeroMuCubicNoACD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + D.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroMuCubicNoACD610]
  compute_degree
  omega


theorem cubicCone_ACD_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACD610 A B C D E)
    (hdeg : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muCubicFaceACD610 A B C D E).natDegree = 2 * C.natDegree + D.natDegree := by
    simp only [muCubicFaceACD610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
  have hrest := degreeZeroMuCubicNoACD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroMuCubic610_eq_ACD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt⟩
  omega


def omicronCubicFaceACE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoACE610
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_ACE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceACE610 A B C D E +
        degreeZeroOmicronCubicNoACE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicFaceACE610, degreeZeroOmicronCubicNoACE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoACE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACE610 A B C D E) :
    (degreeZeroOmicronCubicNoACE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroOmicronCubicNoACE610]
  compute_degree
  omega


theorem cubicCone_ACE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACE610 A B C D E)
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (omicronCubicFaceACE610 A B C D E).natDegree = 2 * C.natDegree + E.natDegree := by
    simp only [omicronCubicFaceACE610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hrest := degreeZeroOmicronCubicNoACE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroOmicronCubic610_eq_ACE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt⟩
  omega


def kappaCubicFaceADE610 (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoADE610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_ADE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceADE610 A B C D E +
        degreeZeroKappaCubicNoADE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceADE610, degreeZeroKappaCubicNoADE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoADE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeADE610 A B C D E) :
    (degreeZeroKappaCubicNoADE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroKappaCubicNoADE610]
  compute_degree
  omega


theorem cubicCone_ADE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeADE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceADE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaCubicFaceADE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoADE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_ADE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt⟩
  omega


def kappaCubicFaceBCE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B * C ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoBCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)
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
theorem degreeZeroKappaCubic610_eq_BCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceBCE610 A B C D E +
        degreeZeroKappaCubicNoBCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceBCE610, degreeZeroKappaCubicNoBCE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoBCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCE610 A B C D E) :
    (degreeZeroKappaCubicNoBCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      B.natDegree + 2 * C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroKappaCubicNoBCE610]
  compute_degree
  omega


theorem cubicCone_BCE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaCubicFaceBCE610 A B C D E).natDegree = B.natDegree + 2 * C.natDegree := by
    simp only [kappaCubicFaceBCE610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoBCE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_BCE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt⟩
  omega


def muCubicFaceBDE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B * D ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoBDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 54 : k) • (A * B ^ 2 * D)
  + (5 / 162 : k) • (A * B * C ^ 2)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (5 / 27 : k) • (A * D * E)
  - (10 / 27 : k) • (B * C * E)
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
theorem degreeZeroMuCubic610_eq_BDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceBDE610 A B C D E +
        degreeZeroMuCubicNoBDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroMuCubic610, muCubicFaceBDE610, degreeZeroMuCubicNoBDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoBDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBDE610 A B C D E) :
    (degreeZeroMuCubicNoBDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      B.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroMuCubicNoBDE610]
  compute_degree
  omega


theorem cubicCone_BDE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBDE610 A B C D E)
    (hdeg : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muCubicFaceBDE610 A B C D E).natDegree = B.natDegree + 2 * D.natDegree := by
    simp only [muCubicFaceBDE610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroMuCubicNoBDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroMuCubic610_eq_BDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt⟩
  omega


def kappaCubicFaceCDE610 (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoCDE610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_CDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceCDE610 A B C D E +
        degreeZeroKappaCubicNoCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceCDE610, degreeZeroKappaCubicNoCDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCDE610 A B C D E) :
    (degreeZeroKappaCubicNoCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  simp only [degreeZeroKappaCubicNoCDE610]
  compute_degree
  omega


theorem cubicCone_CDE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCDE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceCDE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaCubicFaceCDE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoCDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_CDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt⟩
  omega


def kappaCubicFaceACDE610 (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoACDE610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_ACDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceACDE610 A B C D E +
        degreeZeroKappaCubicNoACDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceACDE610, degreeZeroKappaCubicNoACDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoACDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACDE610 A B C D E) :
    (degreeZeroKappaCubicNoACDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  simp only [degreeZeroKappaCubicNoACDE610]
  compute_degree
  omega


theorem cubicCone_ACDE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACDE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceACDE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaCubicFaceACDE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoACDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_ACDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
  omega


def lambdaCubicInnerBE610 (b e : k) : k :=
  5 * b ^ 4 + (-45 : k) * b ^ 2 * e + 135 * e ^ 2

def primitiveCubicInnerBE610 (b e : k) : k :=
  (-4 : k) * b ^ 5 + 30 * b ^ 3 * e

set_option maxHeartbeats 32000000 in
theorem cubicInner_BE_identity
    (b e : k) :
    ((-2 / 8505 : k) * b ^ 4 + (1 / 405 : k) * b ^ 2 * e + (1 / 135 : k) * e ^ 2) * lambdaCubicInnerBE610 b e +
      ((-1 / 3402 : k) * b ^ 3 + (2 / 567 : k) * b * e) * primitiveCubicInnerBE610 b e =
      e ^ 4 := by
  simp only [lambdaCubicInnerBE610, primitiveCubicInnerBE610]
  ring

def lambdaCubicFaceBE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (B ^ 2 * E)
  + (5 / 9 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoBE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 27 : k) • (A * D ^ 2)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_BE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceBE610 A B C D E +
        degreeZeroLambdaCubicNoBE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceBE610, degreeZeroLambdaCubicNoBE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoBE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBE610 A B C D E) :
    (degreeZeroLambdaCubicNoBE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroLambdaCubicNoBE610]
  compute_degree
  omega

theorem lambdaCubicFaceBE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBE610 A B C D E)
    (hBne : B ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicFaceBE610 A B C D E).coeff (4 * B.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerBE610 B.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
  simp only [lambdaCubicFaceBE610, lambdaCubicInnerBE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4 : (B ^ 4).natDegree = 4 * B.natDegree := by
    exact natDegree_pow _ _
  have hcf_B4 : (B ^ 4).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (4 * B.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4, hcf_B2E, hcf_E2]
  ring

def primitiveCubicFaceBE610 (A B C D E : k[X]) : k[X] :=
  (-(4 / 243 : k)) • B ^ 5
  + (10 / 81 : k) • (B ^ 3 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoBE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 2916 : k)) • (A ^ 3 * B ^ 3)
  - (5 / 108 : k) • (A ^ 2 * B ^ 2 * D)
  + (5 / 324 : k) • (A ^ 2 * B * C ^ 2)
  - (25 / 243 : k) • (A * B ^ 3 * C)
  - (5 / 54 : k) • (A ^ 2 * D * E)
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (5 / 27 : k) • (A * C ^ 2 * D)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_BE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceBE610 A B C D E +
        degreeZeroPrimitiveCubicNoBE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceBE610, degreeZeroPrimitiveCubicNoBE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoBE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBE610 A B C D E) :
    (degreeZeroPrimitiveCubicNoBE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroPrimitiveCubicNoBE610]
  compute_degree
  omega

theorem primitiveCubicFaceBE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBE610 A B C D E)
    (hBne : B ≠ 0)
    (hEne : E ≠ 0)
    : (primitiveCubicFaceBE610 A B C D E).coeff (5 * B.natDegree) =
      (1 / 243 : k) * primitiveCubicInnerBE610 B.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
  simp only [primitiveCubicFaceBE610, primitiveCubicInnerBE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 5 * B.natDegree := by
    exact natDegree_pow _ _
  have hcf_B5 : (B ^ 5).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B5, hcf_B3E]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicCone_BE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hlambdainner : lambdaCubicInnerBE610 B.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoBE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceBE610_coeff_top (hcone := hcone) (hBne := hBne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_BE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerBE610 B.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoBE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceBE610_coeff_top (hcone := hcone) (hBne := hBne) (hEne := hEne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_BE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_BE_identity B.leadingCoeff E.leadingCoeff
  have hpow : E.leadingCoeff ^ 4 = 0 := by
    rw [hlambdainner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)


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

set_option maxHeartbeats 32000000 in
theorem cubicInner_ABC_identity
    (a b c : k) :
    ((-73 / 2880 : k) * a * b * c + (-1 / 120 : k) * b ^ 3) * kappaCubicInnerABC610 a b c +
      ((1 / 120 : k) * a * b ^ 2 + (-1 / 15 : k) * c ^ 2) * lambdaCubicInnerABC610 a b c +
      ((-1 / 2880 : k) * b * c) * muCubicInnerABC610 a b c =
      c ^ 5 := by
  simp only [kappaCubicInnerABC610, lambdaCubicInnerABC610, muCubicInnerABC610, omicronCubicInnerABC610, primitiveCubicInnerABC610]
  ring

def kappaCubicFaceABC610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABC610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_ABC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceABC610 A B C D E +
        degreeZeroKappaCubicNoABC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceABC610, degreeZeroKappaCubicNoABC610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoABC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABC610 A B C D E) :
    (degreeZeroKappaCubicNoABC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaCubicNoABC610]
  compute_degree
  omega

theorem kappaCubicFaceABC610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABC610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    : (kappaCubicFaceABC610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicInnerABC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
  simp only [kappaCubicFaceABC610, kappaCubicInnerABC610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB3, hcf_BC2]
  ring

def lambdaCubicFaceABC610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 81 : k) • C ^ 3

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D ^ 2)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_ABC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceABC610 A B C D E +
        degreeZeroLambdaCubicNoABC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceABC610, degreeZeroLambdaCubicNoABC610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoABC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABC610 A B C D E) :
    (degreeZeroLambdaCubicNoABC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroLambdaCubicNoABC610]
  compute_degree
  omega

theorem lambdaCubicFaceABC610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABC610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    : (lambdaCubicFaceABC610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerABC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
  simp only [lambdaCubicFaceABC610, lambdaCubicInnerABC610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_B4, hcf_C3]
  ring

def muCubicFaceABC610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 162 : k) • (A * B * C ^ 2)
  + (20 / 243 : k) • (B ^ 3 * C)

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 54 : k) • (A * B ^ 2 * D)
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
theorem degreeZeroMuCubic610_eq_ABC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceABC610 A B C D E +
        degreeZeroMuCubicNoABC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroMuCubic610, muCubicFaceABC610, degreeZeroMuCubicNoABC610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoABC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABC610 A B C D E) :
    (degreeZeroMuCubicNoABC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroMuCubicNoABC610]
  compute_degree
  omega

theorem muCubicFaceABC610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABC610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    : (muCubicFaceABC610 A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 1458 : k) * muCubicInnerABC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
  simp only [muCubicFaceABC610, muCubicInnerABC610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A2B3, hcf_ABC2, hcf_B3C]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicCone_ABC_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABC610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerABC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoABC610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceABC610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
      omega
    rw [degreeZeroKappaCubic610_eq_ABC_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerABC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoABC610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceABC610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_ABC_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerABC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoABC610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceABC610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
      omega
    rw [degreeZeroMuCubic610_eq_ABC_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1458 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_ABC_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff
  have hpow : C.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner] at hid
    simpa using hid.symm
  have hlc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)


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

set_option maxHeartbeats 32000000 in
theorem cubicInner_ABD_identity
    (a b d : k) :
    ((-19 / 5400 : k) * a ^ 2 * d + (1 / 675 : k) * b ^ 3) * kappaCubicInnerABD610 a b d +
      ((-1 / 675 : k) * a * b ^ 2 + (1 / 225 : k) * b * d) * lambdaCubicInnerABD610 a b d +
      ((-7 / 2700 : k) * a * d) * muCubicInnerABD610 a b d +
      ((-1 / 1080 : k) * d) * primitiveCubicInnerABD610 a b d =
      d ^ 4 := by
  simp only [kappaCubicInnerABD610, lambdaCubicInnerABD610, muCubicInnerABD610, omicronCubicInnerABD610, primitiveCubicInnerABD610]
  ring

def kappaCubicFaceABD610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B * C ^ 2)
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
theorem degreeZeroKappaCubic610_eq_ABD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceABD610 A B C D E +
        degreeZeroKappaCubicNoABD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceABD610, degreeZeroKappaCubicNoABD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoABD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABD610 A B C D E) :
    (degreeZeroKappaCubicNoABD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaCubicNoABD610]
  compute_degree
  omega

theorem kappaCubicFaceABD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABD610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    : (kappaCubicFaceABD610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicInnerABD610 A.leadingCoeff B.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
  simp only [kappaCubicFaceABD610, kappaCubicInnerABD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2D : ((B ^ 2 * D)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB3, hcf_B2D]
  ring

def lambdaCubicFaceABD610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_ABD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceABD610 A B C D E +
        degreeZeroLambdaCubicNoABD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceABD610, degreeZeroLambdaCubicNoABD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoABD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABD610 A B C D E) :
    (degreeZeroLambdaCubicNoABD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroLambdaCubicNoABD610]
  compute_degree
  omega

theorem lambdaCubicFaceABD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABD610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    : (lambdaCubicFaceABD610 A B C D E).coeff (A.natDegree + 2 * D.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerABD610 A.leadingCoeff B.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
  simp only [lambdaCubicFaceABD610, lambdaCubicInnerABD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * D.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AD2, hcf_B4]
  ring

def muCubicFaceABD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 54 : k) • (A * B ^ 2 * D)
  - (5 / 27 : k) • (B * D ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 162 : k) • (A * B * C ^ 2)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (5 / 27 : k) • (A * D * E)
  - (10 / 27 : k) • (B * C * E)
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
theorem degreeZeroMuCubic610_eq_ABD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceABD610 A B C D E +
        degreeZeroMuCubicNoABD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroMuCubic610, muCubicFaceABD610, degreeZeroMuCubicNoABD610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoABD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABD610 A B C D E) :
    (degreeZeroMuCubicNoABD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroMuCubicNoABD610]
  compute_degree
  omega

theorem muCubicFaceABD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABD610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    : (muCubicFaceABD610 A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 1458 : k) * muCubicInnerABD610 A.leadingCoeff B.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
  simp only [muCubicFaceABD610, muCubicInnerABD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A2B3, hcf_AB2D, hcf_BD2]
  ring

def primitiveCubicFaceABD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 2916 : k)) • (A ^ 3 * B ^ 3)
  - (5 / 108 : k) • (A ^ 2 * B ^ 2 * D)
  - (4 / 243 : k) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  - (10 / 27 : k) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoABD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 324 : k) • (A ^ 2 * B * C ^ 2)
  - (25 / 243 : k) • (A * B ^ 3 * C)
  - (5 / 54 : k) • (A ^ 2 * D * E)
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * C ^ 2 * D)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  - (10 / 9 : k) • (C * D * E)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_ABD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceABD610 A B C D E +
        degreeZeroPrimitiveCubicNoABD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceABD610, degreeZeroPrimitiveCubicNoABD610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoABD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABD610 A B C D E) :
    (degreeZeroPrimitiveCubicNoABD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroPrimitiveCubicNoABD610]
  compute_degree
  omega

theorem primitiveCubicFaceABD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABD610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    : (primitiveCubicFaceABD610 A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 2916 : k) * primitiveCubicInnerABD610 A.leadingCoeff B.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
  simp only [primitiveCubicFaceABD610, primitiveCubicInnerABD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_ABD2 : ((A * B * D ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hDne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABD2 : ((A * B * D ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ABD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A3B3, hcf_A2B2D, hcf_ABD2, hcf_B5, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicCone_ABD_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABD610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerABD610 A.leadingCoeff B.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoABD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceABD610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
      omega
    rw [degreeZeroKappaCubic610_eq_ABD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerABD610 A.leadingCoeff B.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoABD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceABD610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_ABD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerABD610 A.leadingCoeff B.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoABD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceABD610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
      omega
    rw [degreeZeroMuCubic610_eq_ABD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1458 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerABD610 A.leadingCoeff B.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoABD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceABD610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hDpos, hAB, hAD, hClt, hElt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_ABD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2916 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_ABD_identity A.leadingCoeff B.leadingCoeff D.leadingCoeff
  have hpow : D.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)


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

set_option maxHeartbeats 32000000 in
theorem cubicInner_BCD_identity
    (b c d : k) :
    ((-1 / 225 : k) * b ^ 3 + (-1 / 20 : k) * c * d) * kappaCubicInnerBCD610 b c d +
      ((-1 / 75 : k) * b * d) * lambdaCubicInnerBCD610 b c d +
      ((-1 / 900 : k) * b * c) * muCubicInnerBCD610 b c d +
      ((-1 / 90 : k) * d) * primitiveCubicInnerBCD610 b c d =
      d ^ 4 := by
  simp only [kappaCubicInnerBCD610, lambdaCubicInnerBCD610, muCubicInnerBCD610, omicronCubicInnerBCD610, primitiveCubicInnerBCD610]
  ring

def kappaCubicFaceBCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
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
theorem degreeZeroKappaCubic610_eq_BCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceBCD610 A B C D E +
        degreeZeroKappaCubicNoBCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceBCD610, degreeZeroKappaCubicNoBCD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoBCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCD610 A B C D E) :
    (degreeZeroKappaCubicNoBCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaCubicNoBCD610]
  compute_degree
  omega

theorem kappaCubicFaceBCD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCD610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (kappaCubicFaceBCD610 A B C D E).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 27 : k) * kappaCubicInnerBCD610 B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
  simp only [kappaCubicFaceBCD610, kappaCubicInnerBCD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hcf_B2D : ((B ^ 2 * D)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B2D, hcf_BC2]
  ring

def lambdaCubicFaceBCD610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (10 / 27 : k) • (B * C * D)
  - (5 / 81 : k) • C ^ 3

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_BCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceBCD610 A B C D E +
        degreeZeroLambdaCubicNoBCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceBCD610, degreeZeroLambdaCubicNoBCD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoBCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCD610 A B C D E) :
    (degreeZeroLambdaCubicNoBCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroLambdaCubicNoBCD610]
  compute_degree
  omega

theorem lambdaCubicFaceBCD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCD610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (lambdaCubicFaceBCD610 A B C D E).coeff (4 * B.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerBCD610 B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
  simp only [lambdaCubicFaceBCD610, lambdaCubicInnerBCD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4 : (B ^ 4).natDegree = 4 * B.natDegree := by
    exact natDegree_pow _ _
  have hcf_B4 : (B ^ 4).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (4 * B.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4, hcf_BCD, hcf_C3]
  ring

def muCubicFaceBCD610 (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 54 : k) • (A * B ^ 2 * D)
  + (5 / 162 : k) • (A * B * C ^ 2)
  - (5 / 27 : k) • (A * D * E)
  - (10 / 27 : k) • (B * C * E)
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
theorem degreeZeroMuCubic610_eq_BCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceBCD610 A B C D E +
        degreeZeroMuCubicNoBCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroMuCubic610, muCubicFaceBCD610, degreeZeroMuCubicNoBCD610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoBCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCD610 A B C D E) :
    (degreeZeroMuCubicNoBCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroMuCubicNoBCD610]
  compute_degree
  omega

theorem muCubicFaceBCD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCD610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (muCubicFaceBCD610 A B C D E).coeff (3 * B.natDegree + C.natDegree) =
      (1 / 243 : k) * muCubicInnerBCD610 B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
  simp only [muCubicFaceBCD610, muCubicInnerBCD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
  have hcf_B3C : ((B ^ 3 * C)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (3 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B3C, hcf_BD2, hcf_C2D]
  ring

def primitiveCubicFaceBCD610 (A B C D E : k[X]) : k[X] :=
  (-(4 / 243 : k)) • B ^ 5
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  - (10 / 27 : k) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 2916 : k)) • (A ^ 3 * B ^ 3)
  - (5 / 108 : k) • (A ^ 2 * B ^ 2 * D)
  + (5 / 324 : k) • (A ^ 2 * B * C ^ 2)
  - (25 / 243 : k) • (A * B ^ 3 * C)
  - (5 / 54 : k) • (A ^ 2 * D * E)
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (5 / 27 : k) • (A * C ^ 2 * D)
  + (10 / 81 : k) • (B ^ 3 * E)
  - (10 / 9 : k) • (C * D * E)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_BCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceBCD610 A B C D E +
        degreeZeroPrimitiveCubicNoBCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceBCD610, degreeZeroPrimitiveCubicNoBCD610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoBCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCD610 A B C D E) :
    (degreeZeroPrimitiveCubicNoBCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroPrimitiveCubicNoBCD610]
  compute_degree
  omega

theorem primitiveCubicFaceBCD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCD610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (primitiveCubicFaceBCD610 A B C D E).coeff (5 * B.natDegree) =
      (1 / 243 : k) * primitiveCubicInnerBCD610 B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
  simp only [primitiveCubicFaceBCD610, primitiveCubicInnerBCD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 5 * B.natDegree := by
    exact natDegree_pow _ _
  have hcf_B5 : (B ^ 5).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2CD : ((B ^ 2 * C * D)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hDne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CD : ((B ^ 2 * C * D)).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_B2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (5 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D3 : (D ^ 3).natDegree = 5 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (5 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B5, hcf_B2CD, hcf_BC3, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicCone_BCD_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCD610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerBCD610 B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoBCD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceBCD610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
      omega
    rw [degreeZeroKappaCubic610_eq_BCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 27 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerBCD610 B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoBCD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceBCD610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_BCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerBCD610 B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoBCD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceBCD610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
      omega
    rw [degreeZeroMuCubic610_eq_BCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerBCD610 B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoBCD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceBCD610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_BCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_BCD_identity B.leadingCoeff C.leadingCoeff D.leadingCoeff
  have hpow : D.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)


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

set_option maxHeartbeats 32000000 in
theorem cubicInner_ABCD_identity
    (a b c d : k) :
    ((-164 / 107775 : k) * a ^ 3 * b * d + (30917 / 862200 : k) * a ^ 2 * d ^ 2 + (71 / 323325 : k) * a * b ^ 4 + (7 / 150 : k) * a * b * c * d + (568 / 107775 : k) * a * c ^ 3 + (-1591 / 215550 : k) * b ^ 3 * d + (1816 / 35925 : k) * b ^ 2 * c ^ 2 + (9731 / 215550 : k) * c * d ^ 2) * kappaCubicInnerABCD610 a b c d +
      ((152 / 35925 : k) * a * b ^ 2 * d + (-568 / 107775 : k) * b ^ 3 * c + (-808 / 11975 : k) * b * d ^ 2 + (-1136 / 11975 : k) * c ^ 2 * d) * lambdaCubicInnerABCD610 a b c d +
      ((-164 / 107775 : k) * a ^ 2 * b * d + (12149 / 1293300 : k) * a * d ^ 2 + (71 / 323325 : k) * b ^ 4 + (219 / 23950 : k) * b * c * d + (568 / 107775 : k) * c ^ 3) * muCubicInnerABCD610 a b c d +
      ((164 / 11975 : k) * a * c * d + (173 / 215550 : k) * b ^ 2 * d + (416 / 11975 : k) * b * c ^ 2) * omicronCubicInnerABCD610 a b c d +
      ((-1 / 1080 : k) * d ^ 2) * primitiveCubicInnerABCD610 a b c d =
      d ^ 5 := by
  simp only [kappaCubicInnerABCD610, lambdaCubicInnerABCD610, muCubicInnerABCD610, omicronCubicInnerABCD610, primitiveCubicInnerABCD610]
  ring

def kappaCubicFaceABCD610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (10 / 9 : k) • (D * E)
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
theorem degreeZeroKappaCubic610_eq_ABCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceABCD610 A B C D E +
        degreeZeroKappaCubicNoABCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceABCD610, degreeZeroKappaCubicNoABCD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoABCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCD610 A B C D E) :
    (degreeZeroKappaCubicNoABCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaCubicNoABCD610]
  compute_degree
  omega

theorem kappaCubicFaceABCD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCD610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (kappaCubicFaceABCD610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicInnerABCD610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
  simp only [kappaCubicFaceABCD610, kappaCubicInnerABCD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2D : ((B ^ 2 * D)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB3, hcf_B2D, hcf_BC2]
  ring

def lambdaCubicFaceABCD610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 81 : k) • C ^ 3

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * E)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_ABCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceABCD610 A B C D E +
        degreeZeroLambdaCubicNoABCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceABCD610, degreeZeroLambdaCubicNoABCD610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoABCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCD610 A B C D E) :
    (degreeZeroLambdaCubicNoABCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroLambdaCubicNoABCD610]
  compute_degree
  omega

theorem lambdaCubicFaceABCD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCD610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (lambdaCubicFaceABCD610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerABCD610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
  simp only [lambdaCubicFaceABCD610, lambdaCubicInnerABCD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_AD2, hcf_B4, hcf_BCD, hcf_C3]
  ring

def muCubicFaceABCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 54 : k) • (A * B ^ 2 * D)
  + (5 / 162 : k) • (A * B * C ^ 2)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D * E)
  - (10 / 27 : k) • (B * C * E)
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
theorem degreeZeroMuCubic610_eq_ABCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceABCD610 A B C D E +
        degreeZeroMuCubicNoABCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroMuCubic610, muCubicFaceABCD610, degreeZeroMuCubicNoABCD610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoABCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCD610 A B C D E) :
    (degreeZeroMuCubicNoABCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroMuCubicNoABCD610]
  compute_degree
  omega

theorem muCubicFaceABCD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCD610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (muCubicFaceABCD610 A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 1458 : k) * muCubicInnerABCD610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
  simp only [muCubicFaceABCD610, muCubicInnerABCD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A2B3, hcf_AB2D, hcf_ABC2, hcf_B3C, hcf_BD2, hcf_C2D]
  ring

def omicronCubicFaceABCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (10 / 81 : k) • (A * B * C * D)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (C * D ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoABCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * E)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C ^ 2 * E)
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
theorem degreeZeroOmicronCubic610_eq_ABCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceABCD610 A B C D E +
        degreeZeroOmicronCubicNoABCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicFaceABCD610, degreeZeroOmicronCubicNoABCD610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoABCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCD610 A B C D E) :
    (degreeZeroOmicronCubicNoABCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroOmicronCubicNoABCD610]
  compute_degree
  omega

theorem omicronCubicFaceABCD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCD610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (omicronCubicFaceABCD610 A B C D E).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 486 : k) * omicronCubicInnerABCD610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
  simp only [omicronCubicFaceABCD610, omicronCubicInnerABCD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB4 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne), natDegree_pow]
  have hcf_AB4 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hdeg_AB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCD : ((A * B * C * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCD : ((A * B * C * D)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_ABCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
    omega
  have hcf_B3D : ((B ^ 3 * D)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB4, hcf_ABCD, hcf_B3D, hcf_B2C2, hcf_CD2]
  ring

def primitiveCubicFaceABCD610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 2916 : k)) • (A ^ 3 * B ^ 3)
  - (5 / 108 : k) • (A ^ 2 * B ^ 2 * D)
  + (5 / 324 : k) • (A ^ 2 * B * C ^ 2)
  - (25 / 243 : k) • (A * B ^ 3 * C)
  - (4 / 243 : k) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (5 / 27 : k) • (A * C ^ 2 * D)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  - (10 / 27 : k) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoABCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 54 : k)) • (A ^ 2 * D * E)
  + (10 / 27 : k) • (A * B * C * E)
  + (10 / 81 : k) • (B ^ 3 * E)
  - (10 / 9 : k) • (C * D * E)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_ABCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceABCD610 A B C D E +
        degreeZeroPrimitiveCubicNoABCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceABCD610, degreeZeroPrimitiveCubicNoABCD610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoABCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCD610 A B C D E) :
    (degreeZeroPrimitiveCubicNoABCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroPrimitiveCubicNoABCD610]
  compute_degree
  omega

theorem primitiveCubicFaceABCD610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCD610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (primitiveCubicFaceABCD610 A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 2916 : k) * primitiveCubicInnerABCD610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
  simp only [primitiveCubicFaceABCD610, primitiveCubicInnerABCD610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BC2 : ((A ^ 2 * B * C ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BC2 : ((A ^ 2 * B * C ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB3C : ((A * B ^ 3 * C)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3C : ((A * B ^ 3 * C)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_AB3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABD2 : ((A * B * D ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hDne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABD2 : ((A * B * D ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ABD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AC2D : ((A * C ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_AC2D : ((A * C ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2CD : ((B ^ 2 * C * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hDne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CD : ((B ^ 2 * C * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_B2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A3B3, hcf_A2B2D, hcf_A2BC2, hcf_AB3C, hcf_ABD2, hcf_AC2D, hcf_B5, hcf_B2CD, hcf_BC3, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicCone_ABCD_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCD610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerABCD610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoABCD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceABCD610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
      omega
    rw [degreeZeroKappaCubic610_eq_ABCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerABCD610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoABCD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceABCD610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_ABCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerABCD610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoABCD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceABCD610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
      omega
    rw [degreeZeroMuCubic610_eq_ABCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1458 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronCubicInnerABCD610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronCubicNoABCD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := omicronCubicFaceABCD610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_ABCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 486 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerABCD610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoABCD610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceABCD610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hAB, hAC, hAD, hElt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_ABCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2916 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_ABCD_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
  have hpow : D.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, homicroninner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)


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

set_option maxHeartbeats 32000000 in
theorem cubicInner_ABCE_identity
    (a b c e : k) :
    ((-1 / 40824 : k) * a ^ 2 * b ^ 3 + (26 / 25515 : k) * a ^ 2 * b * e + (-1 / 4860 : k) * a * b * c ^ 2 + (-43 / 17010 : k) * b ^ 3 * c + (127 / 17010 : k) * b * c * e) * kappaCubicInnerABCE610 a b c e +
      ((-2 / 8505 : k) * b ^ 4 + (1 / 405 : k) * b ^ 2 * e + (1 / 135 : k) * e ^ 2) * lambdaCubicInnerABCE610 a b c e +
      ((37 / 51030 : k) * a * b * e + (-1 / 4860 : k) * b * c ^ 2) * muCubicInnerABCE610 a b c e +
      ((-1 / 567 : k) * b ^ 2 * c + (-1 / 810 : k) * c * e) * omicronCubicInnerABCE610 a b c e +
      ((-1 / 40824 : k) * b ^ 3 + (1 / 3402 : k) * b * e) * primitiveCubicInnerABCE610 a b c e =
      e ^ 4 := by
  simp only [kappaCubicInnerABCE610, lambdaCubicInnerABCE610, muCubicInnerABCE610, omicronCubicInnerABCE610, primitiveCubicInnerABCE610]
  ring

def kappaCubicFaceABCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABCE610
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_ABCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceABCE610 A B C D E +
        degreeZeroKappaCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceABCE610, degreeZeroKappaCubicNoABCE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoABCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E) :
    (degreeZeroKappaCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroKappaCubicNoABCE610]
  compute_degree
  omega

theorem kappaCubicFaceABCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (kappaCubicFaceABCE610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  simp only [kappaCubicFaceABCE610, kappaCubicInnerABCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB3, hcf_BC2]
  ring

def lambdaCubicFaceABCE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (B ^ 2 * E)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (A * D ^ 2)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_ABCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceABCE610 A B C D E +
        degreeZeroLambdaCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceABCE610, degreeZeroLambdaCubicNoABCE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoABCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E) :
    (degreeZeroLambdaCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroLambdaCubicNoABCE610]
  compute_degree
  omega

theorem lambdaCubicFaceABCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicFaceABCE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  simp only [lambdaCubicFaceABCE610, lambdaCubicInnerABCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_B4, hcf_B2E, hcf_C3, hcf_E2]
  ring

def muCubicFaceABCE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 162 : k) • (A * B * C ^ 2)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 54 : k) • (A * B ^ 2 * D)
  - (5 / 27 : k) • (A * D * E)
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
theorem degreeZeroMuCubic610_eq_ABCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceABCE610 A B C D E +
        degreeZeroMuCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroMuCubic610, muCubicFaceABCE610, degreeZeroMuCubicNoABCE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoABCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E) :
    (degreeZeroMuCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroMuCubicNoABCE610]
  compute_degree
  omega

theorem muCubicFaceABCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (muCubicFaceABCE610 A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 1458 : k) * muCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  simp only [muCubicFaceABCE610, muCubicInnerABCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  rw [hcf_A2B3, hcf_ABC2, hcf_B3C, hcf_BCE]
  ring

def omicronCubicFaceABCE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (5 / 81 : k) • (A * B ^ 2 * E)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (C ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoABCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (10 / 81 : k) • (A * B * C * D)
  + (25 / 486 : k) • (B ^ 3 * D)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_ABCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceABCE610 A B C D E +
        degreeZeroOmicronCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicFaceABCE610, degreeZeroOmicronCubicNoABCE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoABCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E) :
    (degreeZeroOmicronCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroOmicronCubicNoABCE610]
  compute_degree
  omega

theorem omicronCubicFaceABCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (omicronCubicFaceABCE610 A B C D E).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 486 : k) * omicronCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  simp only [omicronCubicFaceABCE610, omicronCubicInnerABCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB4 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne), natDegree_pow]
  have hcf_AB4 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hdeg_AB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB4, hcf_AB2E, hcf_B2C2, hcf_C2E]
  ring

def primitiveCubicFaceABCE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 2916 : k)) • (A ^ 3 * B ^ 3)
  + (5 / 324 : k) • (A ^ 2 * B * C ^ 2)
  - (25 / 243 : k) • (A * B ^ 3 * C)
  - (4 / 243 : k) • B ^ 5
  + (10 / 27 : k) • (A * B * C * E)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 27 : k) • (B * C ^ 3)

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoABCE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 108 : k)) • (A ^ 2 * B ^ 2 * D)
  - (5 / 54 : k) • (A ^ 2 * D * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (5 / 27 : k) • (A * C ^ 2 * D)
  + (5 / 9 : k) • (B ^ 2 * C * D)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_ABCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceABCE610 A B C D E +
        degreeZeroPrimitiveCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceABCE610, degreeZeroPrimitiveCubicNoABCE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoABCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E) :
    (degreeZeroPrimitiveCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroPrimitiveCubicNoABCE610]
  compute_degree
  omega

theorem primitiveCubicFaceABCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (primitiveCubicFaceABCE610 A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 2916 : k) * primitiveCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  simp only [primitiveCubicFaceABCE610, primitiveCubicInnerABCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BC2 : ((A ^ 2 * B * C ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BC2 : ((A ^ 2 * B * C ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB3C : ((A * B ^ 3 * C)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3C : ((A * B ^ 3 * C)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_AB3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCE : ((A * B * C * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCE : ((A * B * C * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ABCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A3B3, hcf_A2BC2, hcf_AB3C, hcf_ABCE, hcf_B5, hcf_B3E, hcf_BC3]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicCone_ABCE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoABCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceABCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
      omega
    rw [degreeZeroKappaCubic610_eq_ABCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoABCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceABCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_ABCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoABCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceABCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
      omega
    rw [degreeZeroMuCubic610_eq_ABCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1458 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronCubicNoABCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := omicronCubicFaceABCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_ABCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 486 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoABCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceABCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_ABCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2916 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_ABCE_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff
  have hpow : E.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, homicroninner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)


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

set_option maxHeartbeats 32000000 in
theorem cubicInner_ABDE_identity
    (a b d e : k) :
    ((-23 / 5400 : k) * a ^ 2 * d + (1 / 1350 : k) * b ^ 3) * kappaCubicInnerABDE610 a b d e +
      ((-2 / 675 : k) * a * b ^ 2 + (2 / 225 : k) * b * d) * lambdaCubicInnerABDE610 a b d e +
      ((-1 / 300 : k) * a * d) * muCubicInnerABDE610 a b d e +
      ((-1 / 450 : k) * b ^ 2 + (1 / 75 : k) * e) * omicronCubicInnerABDE610 a b d e +
      ((-1 / 1080 : k) * d) * primitiveCubicInnerABDE610 a b d e =
      d ^ 4 := by
  simp only [kappaCubicInnerABDE610, lambdaCubicInnerABDE610, muCubicInnerABDE610, omicronCubicInnerABDE610, primitiveCubicInnerABDE610]
  ring

def kappaCubicFaceABDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)
  + (10 / 9 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B * C ^ 2)
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
theorem degreeZeroKappaCubic610_eq_ABDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceABDE610 A B C D E +
        degreeZeroKappaCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceABDE610, degreeZeroKappaCubicNoABDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoABDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABDE610 A B C D E) :
    (degreeZeroKappaCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroKappaCubicNoABDE610]
  compute_degree
  omega

theorem kappaCubicFaceABDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (kappaCubicFaceABDE610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  simp only [kappaCubicFaceABDE610, kappaCubicInnerABDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2D : ((B ^ 2 * D)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_B2D, hcf_DE]
  ring

def lambdaCubicFaceABDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  + (5 / 9 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_ABDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceABDE610 A B C D E +
        degreeZeroLambdaCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceABDE610, degreeZeroLambdaCubicNoABDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoABDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABDE610 A B C D E) :
    (degreeZeroLambdaCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroLambdaCubicNoABDE610]
  compute_degree
  omega

theorem lambdaCubicFaceABDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicFaceABDE610 A B C D E).coeff (A.natDegree + 2 * D.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  simp only [lambdaCubicFaceABDE610, lambdaCubicInnerABDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * D.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (A.natDegree + 2 * D.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * D.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AD2, hcf_B4, hcf_B2E, hcf_E2]
  ring

def muCubicFaceABDE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 54 : k) • (A * B ^ 2 * D)
  - (5 / 27 : k) • (A * D * E)
  - (5 / 27 : k) • (B * D ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 162 : k) • (A * B * C ^ 2)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
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
theorem degreeZeroMuCubic610_eq_ABDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceABDE610 A B C D E +
        degreeZeroMuCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroMuCubic610, muCubicFaceABDE610, degreeZeroMuCubicNoABDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoABDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABDE610 A B C D E) :
    (degreeZeroMuCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroMuCubicNoABDE610]
  compute_degree
  omega

theorem muCubicFaceABDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (muCubicFaceABDE610 A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 1458 : k) * muCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  simp only [muCubicFaceABDE610, muCubicInnerABDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ADE : ((A * D * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    omega
  have hcf_ADE : ((A * D * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ADE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A2B3, hcf_AB2D, hcf_ADE, hcf_BD2]
  ring

def omicronCubicFaceABDE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (5 / 81 : k) • (A * B ^ 2 * E)
  + (25 / 486 : k) • (B ^ 3 * D)
  - (5 / 27 : k) • (B * D * E)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoABDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (10 / 81 : k) • (A * B * C * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
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
theorem degreeZeroOmicronCubic610_eq_ABDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceABDE610 A B C D E +
        degreeZeroOmicronCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicFaceABDE610, degreeZeroOmicronCubicNoABDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoABDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABDE610 A B C D E) :
    (degreeZeroOmicronCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroOmicronCubicNoABDE610]
  compute_degree
  omega

theorem omicronCubicFaceABDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (omicronCubicFaceABDE610 A B C D E).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 486 : k) * omicronCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  simp only [omicronCubicFaceABDE610, omicronCubicInnerABDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB4 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne), natDegree_pow]
  have hcf_AB4 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hdeg_AB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
    omega
  have hcf_B3D : ((B ^ 3 * D)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDE : ((B * D * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    omega
  have hcf_BDE : ((B * D * E)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  rw [hcf_AB4, hcf_AB2E, hcf_B3D, hcf_BDE]
  ring

def primitiveCubicFaceABDE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 2916 : k)) • (A ^ 3 * B ^ 3)
  - (5 / 108 : k) • (A ^ 2 * B ^ 2 * D)
  - (4 / 243 : k) • B ^ 5
  - (5 / 54 : k) • (A ^ 2 * D * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  - (10 / 27 : k) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoABDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 324 : k) • (A ^ 2 * B * C ^ 2)
  - (25 / 243 : k) • (A * B ^ 3 * C)
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * C ^ 2 * D)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  - (10 / 9 : k) • (C * D * E)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_ABDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceABDE610 A B C D E +
        degreeZeroPrimitiveCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceABDE610, degreeZeroPrimitiveCubicNoABDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoABDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABDE610 A B C D E) :
    (degreeZeroPrimitiveCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroPrimitiveCubicNoABDE610]
  compute_degree
  omega

theorem primitiveCubicFaceABDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (primitiveCubicFaceABDE610 A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 2916 : k) * primitiveCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  simp only [primitiveCubicFaceABDE610, primitiveCubicInnerABDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2DE : ((A ^ 2 * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DE : ((A ^ 2 * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABD2 : ((A * B * D ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hDne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABD2 : ((A * B * D ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ABD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A3B3, hcf_A2B2D, hcf_A2DE, hcf_ABD2, hcf_B5, hcf_B3E, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicCone_ABDE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABDE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoABDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceABDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
      omega
    rw [degreeZeroKappaCubic610_eq_ABDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoABDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceABDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_ABDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoABDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceABDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
      omega
    rw [degreeZeroMuCubic610_eq_ABDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1458 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronCubicNoABDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := omicronCubicFaceABDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_ABDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 486 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoABDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceABDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_ABDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2916 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_ABDE_identity A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff
  have hpow : D.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, homicroninner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)


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

set_option maxHeartbeats 32000000 in
theorem cubicInner_BCDE_identity
    (b c d e : k) :
    ((-437 / 48195 : k) * b ^ 3 * c * e + (79 / 27540 : k) * b ^ 3 * d ^ 2 + (-139 / 3060 : k) * b ^ 2 * c ^ 2 * d + (-91 / 9180 : k) * b * c ^ 4 + (6733 / 64260 : k) * b * c * e ^ 2 + (-1 / 21420 : k) * b * d ^ 2 * e + (-8 / 1071 : k) * c ^ 2 * d * e + (1 / 510 : k) * c * d ^ 3) * kappaCubicInnerBCDE610 b c d e +
      ((-2 / 8505 : k) * b ^ 4 * e + (1 / 405 : k) * b ^ 2 * e ^ 2 + (-517 / 96390 : k) * b * c * d * e + (79 / 27540 : k) * b * d ^ 3 + (91 / 13770 : k) * c ^ 3 * e + (73 / 9180 : k) * c ^ 2 * d ^ 2 + (1 / 135 : k) * e ^ 3) * lambdaCubicInnerBCDE610 b c d e +
      ((-331 / 96390 : k) * b * c ^ 2 * e + (-41 / 6885 : k) * b * c * d ^ 2 + (-37 / 82620 : k) * c ^ 3 * d + (41 / 192780 : k) * d * e ^ 2) * muCubicInnerBCDE610 b c d e +
      ((-49 / 9180 : k) * b * c ^ 2 * d + (-91 / 82620 : k) * c ^ 4 + (239 / 27540 : k) * c * e ^ 2 + (1 / 1530 : k) * d ^ 2 * e) * omicronCubicInnerBCDE610 b c d e +
      ((-1 / 3402 : k) * b ^ 3 * e + (2 / 567 : k) * b * e ^ 2) * primitiveCubicInnerBCDE610 b c d e =
      e ^ 5 := by
  simp only [kappaCubicInnerBCDE610, lambdaCubicInnerBCDE610, muCubicInnerBCDE610, omicronCubicInnerBCDE610, primitiveCubicInnerBCDE610]
  ring

def kappaCubicFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
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
theorem degreeZeroKappaCubic610_eq_BCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceBCDE610 A B C D E +
        degreeZeroKappaCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceBCDE610, degreeZeroKappaCubicNoBCDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E) :
    (degreeZeroKappaCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  simp only [degreeZeroKappaCubicNoBCDE610]
  compute_degree
  omega

theorem kappaCubicFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (kappaCubicFaceBCDE610 A B C D E).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 27 : k) * kappaCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  simp only [kappaCubicFaceBCDE610, kappaCubicInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hcf_B2D : ((B ^ 2 * D)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE : ((D * E)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (2 * B.natDegree + D.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2D, hcf_BC2, hcf_DE]
  ring

def lambdaCubicFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  - (5 / 27 : k) • (A * D ^ 2)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_BCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceBCDE610 A B C D E +
        degreeZeroLambdaCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceBCDE610, degreeZeroLambdaCubicNoBCDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E) :
    (degreeZeroLambdaCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  simp only [degreeZeroLambdaCubicNoBCDE610]
  compute_degree
  omega

theorem lambdaCubicFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicFaceBCDE610 A B C D E).coeff (4 * B.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  simp only [lambdaCubicFaceBCDE610, lambdaCubicInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4 : (B ^ 4).natDegree = 4 * B.natDegree := by
    exact natDegree_pow _ _
  have hcf_B4 : (B ^ 4).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (4 * B.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (4 * B.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4, hcf_B2E, hcf_BCD, hcf_C3, hcf_E2]
  ring

def muCubicFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 54 : k) • (A * B ^ 2 * D)
  + (5 / 162 : k) • (A * B * C ^ 2)
  - (5 / 27 : k) • (A * D * E)
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
theorem degreeZeroMuCubic610_eq_BCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceBCDE610 A B C D E +
        degreeZeroMuCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroMuCubic610, muCubicFaceBCDE610, degreeZeroMuCubicNoBCDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E) :
    (degreeZeroMuCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  simp only [degreeZeroMuCubicNoBCDE610]
  compute_degree
  omega

theorem muCubicFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (muCubicFaceBCDE610 A B C D E).coeff (3 * B.natDegree + C.natDegree) =
      (1 / 243 : k) * muCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  simp only [muCubicFaceBCDE610, muCubicInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
  have hcf_B3C : ((B ^ 3 * C)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (3 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B3C, hcf_BCE, hcf_BD2, hcf_C2D]
  ring

def omicronCubicFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C ^ 2 * E)
  - (5 / 27 : k) • (C * D ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (5 / 81 : k) • (A * B ^ 2 * E)
  + (10 / 81 : k) • (A * B * C * D)
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
theorem degreeZeroOmicronCubic610_eq_BCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceBCDE610 A B C D E +
        degreeZeroOmicronCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicFaceBCDE610, degreeZeroOmicronCubicNoBCDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E) :
    (degreeZeroOmicronCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  simp only [degreeZeroOmicronCubicNoBCDE610]
  compute_degree
  omega

theorem omicronCubicFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (omicronCubicFaceBCDE610 A B C D E).coeff (3 * B.natDegree + D.natDegree) =
      (1 / 486 : k) * omicronCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  simp only [omicronCubicFaceBCDE610, omicronCubicInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
  have hcf_B3D : ((B ^ 3 * D)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BDE : ((B * D * E)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    omega
  have hcf_BDE : ((B * D * E)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (3 * B.natDegree + D.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (3 * B.natDegree + D.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B3D, hcf_B2C2, hcf_BDE, hcf_C2E, hcf_CD2]
  ring

def primitiveCubicFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (-(4 / 243 : k)) • B ^ 5
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  - (10 / 9 : k) • (C * D * E)
  - (10 / 27 : k) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 2916 : k)) • (A ^ 3 * B ^ 3)
  - (5 / 108 : k) • (A ^ 2 * B ^ 2 * D)
  + (5 / 324 : k) • (A ^ 2 * B * C ^ 2)
  - (25 / 243 : k) • (A * B ^ 3 * C)
  - (5 / 54 : k) • (A ^ 2 * D * E)
  + (10 / 27 : k) • (A * B * C * E)
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (5 / 27 : k) • (A * C ^ 2 * D)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_BCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceBCDE610 A B C D E +
        degreeZeroPrimitiveCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceBCDE610, degreeZeroPrimitiveCubicNoBCDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E) :
    (degreeZeroPrimitiveCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  simp only [degreeZeroPrimitiveCubicNoBCDE610]
  compute_degree
  omega

theorem primitiveCubicFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (primitiveCubicFaceBCDE610 A B C D E).coeff (5 * B.natDegree) =
      (1 / 243 : k) * primitiveCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  simp only [primitiveCubicFaceBCDE610, primitiveCubicInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 5 * B.natDegree := by
    exact natDegree_pow _ _
  have hcf_B5 : (B ^ 5).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CD : ((B ^ 2 * C * D)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hDne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CD : ((B ^ 2 * C * D)).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_B2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (5 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDE : ((C * D * E)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hEne, natDegree_mul hCne hDne]
    omega
  have hcf_CDE : ((C * D * E)).coeff (5 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_CDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D3 : (D ^ 3).natDegree = 5 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (5 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B5, hcf_B3E, hcf_B2CD, hcf_BC3, hcf_CDE, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicCone_BCDE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoBCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceBCDE610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
      omega
    rw [degreeZeroKappaCubic610_eq_BCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 27 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoBCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceBCDE610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_BCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoBCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceBCDE610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
      omega
    rw [degreeZeroMuCubic610_eq_BCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronCubicNoBCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := omicronCubicFaceBCDE610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_BCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 486 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoBCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceBCDE610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_BCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_BCDE_identity B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff
  have hpow : E.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, homicroninner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)


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

set_option maxHeartbeats 32000000 in
theorem cubicInner_ABCDE_identity
    (a b c d e : k) :
    ((-1 / 29070 : k) * a ^ 4 * b ^ 2 + (2 / 1995 : k) * a ^ 4 * e + (31 / 67830 : k) * a ^ 3 * b * d + (-83 / 67830 : k) * a ^ 3 * c ^ 2 + (26 / 305235 : k) * a ^ 2 * b ^ 2 * c + (43 / 35910 : k) * a ^ 2 * c * e + (-3631 / 2441880 : k) * a ^ 2 * d ^ 2 + (-319 / 2747115 : k) * a * b ^ 4 + (-2 / 3591 : k) * a * b ^ 2 * e + (3361 / 1017450 : k) * a * b * c * d + (-4586 / 915705 : k) * a * c ^ 3 + (937 / 508725 : k) * a * e ^ 2 + (2339 / 1017450 : k) * b ^ 3 * d + (704 / 80325 : k) * b ^ 2 * c ^ 2 + (-1696 / 508725 : k) * b * d * e + (-1678 / 72675 : k) * c ^ 2 * e + (-22711 / 1017450 : k) * c * d ^ 2) * kappaCubicInnerABCDE610 a b c d e +
      ((872 / 305235 : k) * a * b ^ 2 * d + (-16 / 1995 : k) * a * d * e + (10456 / 4578525 : k) * b ^ 3 * c + (-4412 / 508725 : k) * b * c * e + (-232 / 20349 : k) * b * d ^ 2 + (208 / 101745 : k) * c ^ 2 * d) * lambdaCubicInnerABCDE610 a b c d e +
      ((-1 / 43605 : k) * a ^ 3 * b ^ 2 + (4 / 5985 : k) * a ^ 3 * e + (31 / 101745 : k) * a ^ 2 * b * d + (-83 / 101745 : k) * a ^ 2 * c ^ 2 + (-31 / 17955 : k) * a * c * e + (-137 / 244188 : k) * a * d ^ 2 + (-83 / 13735575 : k) * b ^ 4 + (134 / 1526175 : k) * b ^ 2 * e + (-3 / 6650 : k) * b * c * d + (-104 / 915705 : k) * c ^ 3 + (-1103 / 508725 : k) * e ^ 2) * muCubicInnerABCDE610 a b c d e +
      ((-4 / 855 : k) * a * b * e + (7 / 1530 : k) * b ^ 2 * d + (104 / 14535 : k) * b * c ^ 2 + (-499 / 24225 : k) * d * e) * omicronCubicInnerABCDE610 a b c d e +
      ((-1 / 87210 : k) * a ^ 2 * b ^ 2 + (2 / 5985 : k) * a ^ 2 * e + (31 / 203490 : k) * a * b * d + (-83 / 203490 : k) * a * c ^ 2 + (4 / 17955 : k) * b ^ 2 * c + (-13 / 11970 : k) * c * e + (-1 / 1080 : k) * d ^ 2) * primitiveCubicInnerABCDE610 a b c d e =
      d ^ 5 := by
  simp only [kappaCubicInnerABCDE610, lambdaCubicInnerABCDE610, muCubicInnerABCDE610, omicronCubicInnerABCDE610, primitiveCubicInnerABCDE610]
  ring

def kappaCubicFaceABCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaCubicNoABCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (7 / 6912 * l : k) • A ^ 5
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
theorem degreeZeroKappaCubic610_eq_ABCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceABCDE610 A B C D E +
        degreeZeroKappaCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicFaceABCDE610, degreeZeroKappaCubicNoABCDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoABCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCDE610 A B C D E) :
    (degreeZeroKappaCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [degreeZeroKappaCubicNoABCDE610]
  compute_degree
  omega

theorem kappaCubicFaceABCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (kappaCubicFaceABCDE610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [kappaCubicFaceABCDE610, kappaCubicInnerABCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2D : ((B ^ 2 * D)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_B2D, hcf_BC2, hcf_DE]
  ring

def lambdaCubicFaceABCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * C)
  + (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  - (5 / 81 : k) • C ^ 3
  + (5 / 9 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoABCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 6912 * l : k)) • (A ^ 4 * B)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_ABCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceABCDE610 A B C D E +
        degreeZeroLambdaCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicFaceABCDE610, degreeZeroLambdaCubicNoABCDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoABCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCDE610 A B C D E) :
    (degreeZeroLambdaCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [degreeZeroLambdaCubicNoABCDE610]
  compute_degree
  omega

theorem lambdaCubicFaceABCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicFaceABCDE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [lambdaCubicFaceABCDE610, lambdaCubicInnerABCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_AD2, hcf_B4, hcf_B2E, hcf_BCD, hcf_C3, hcf_E2]
  ring

def muCubicFaceABCDE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 1458 : k)) • (A ^ 2 * B ^ 3)
  + (5 / 54 : k) • (A * B ^ 2 * D)
  + (5 / 162 : k) • (A * B * C ^ 2)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (5 / 27 : k) • (A * D * E)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)

set_option maxHeartbeats 32000000 in
def degreeZeroMuCubicNoABCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (35 / 248832 * l : k) • A ^ 6
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
theorem degreeZeroMuCubic610_eq_ABCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceABCDE610 A B C D E +
        degreeZeroMuCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroMuCubic610, muCubicFaceABCDE610, degreeZeroMuCubicNoABCDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoABCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCDE610 A B C D E) :
    (degreeZeroMuCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [degreeZeroMuCubicNoABCDE610]
  compute_degree
  omega

theorem muCubicFaceABCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (muCubicFaceABCDE610 A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 1458 : k) * muCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [muCubicFaceABCDE610, muCubicInnerABCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ADE : ((A * D * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    omega
  have hcf_ADE : ((A * D * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ADE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A2B3, hcf_AB2D, hcf_ABC2, hcf_ADE, hcf_B3C, hcf_BCE, hcf_BD2, hcf_C2D]
  ring

def omicronCubicFaceABCDE610 (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (5 / 81 : k) • (A * B ^ 2 * E)
  + (10 / 81 : k) • (A * B * C * D)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C ^ 2 * E)
  - (5 / 27 : k) • (C * D ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroOmicronCubicNoABCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 6912 * l : k)) • (A ^ 4 * D)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronCubic610_eq_ABCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceABCDE610 A B C D E +
        degreeZeroOmicronCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicFaceABCDE610, degreeZeroOmicronCubicNoABCDE610]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronCubicNoABCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCDE610 A B C D E) :
    (degreeZeroOmicronCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [degreeZeroOmicronCubicNoABCDE610]
  compute_degree
  omega

theorem omicronCubicFaceABCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (omicronCubicFaceABCDE610 A B C D E).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 486 : k) * omicronCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [omicronCubicFaceABCDE610, omicronCubicInnerABCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB4 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne), natDegree_pow]
  have hcf_AB4 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hdeg_AB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCD : ((A * B * C * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCD : ((A * B * C * D)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_ABCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
    omega
  have hcf_B3D : ((B ^ 3 * D)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BDE : ((B * D * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    omega
  have hcf_BDE : ((B * D * E)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB4, hcf_AB2E, hcf_ABCD, hcf_B3D, hcf_B2C2, hcf_BDE, hcf_C2E, hcf_CD2]
  ring

def primitiveCubicFaceABCDE610 (A B C D E : k[X]) : k[X] :=
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

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveCubicNoABCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 27648 * l : k) • A ^ 7
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_ABCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceABCDE610 A B C D E +
        degreeZeroPrimitiveCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceABCDE610, degreeZeroPrimitiveCubicNoABCDE610]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoABCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCDE610 A B C D E) :
    (degreeZeroPrimitiveCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [degreeZeroPrimitiveCubicNoABCDE610]
  compute_degree
  omega

theorem primitiveCubicFaceABCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (primitiveCubicFaceABCDE610 A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 2916 : k) * primitiveCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [primitiveCubicFaceABCDE610, primitiveCubicInnerABCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BC2 : ((A ^ 2 * B * C ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BC2 : ((A ^ 2 * B * C ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2DE : ((A ^ 2 * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DE : ((A ^ 2 * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3C : ((A * B ^ 3 * C)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3C : ((A * B ^ 3 * C)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_AB3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCE : ((A * B * C * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCE : ((A * B * C * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ABCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABD2 : ((A * B * D ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hDne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABD2 : ((A * B * D ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ABD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AC2D : ((A * C ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_AC2D : ((A * C ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CD : ((B ^ 2 * C * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hDne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CD : ((B ^ 2 * C * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_B2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDE : ((C * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hEne, natDegree_mul hCne hDne]
    omega
  have hcf_CDE : ((C * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_CDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A3B3, hcf_A2B2D, hcf_A2BC2, hcf_A2DE, hcf_AB3C, hcf_ABCE, hcf_ABD2, hcf_AC2D, hcf_B5, hcf_B3E, hcf_B2CD, hcf_BC3, hcf_CDE, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
theorem cubicCone_ABCDE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCDE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoABCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceABCDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
      omega
    rw [degreeZeroKappaCubic610_eq_ABCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoABCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceABCDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_ABCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoABCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceABCDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
      omega
    rw [degreeZeroMuCubic610_eq_ABCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1458 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronCubicNoABCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := omicronCubicFaceABCDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_ABCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 486 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoABCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceABCDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_ABCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2916 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_ABCDE_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff
  have hpow : D.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, homicroninner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)



set_option maxHeartbeats 32000000 in
theorem primitiveCubic_natDegree_le_zero_of_constants
    (l alpha beta delta epsilon zeta eta theta : k)
    {A B C D E : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C.natDegree = 0) (hD : D.natDegree = 0)
    (hE : E.natDegree = 0) :
    (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree ≤
      0 := by
  simp only [degreeZeroPrimitiveCubic610, degreeZeroBaseGroupCubic610,
    degreeZeroAlphaGroupCubic610, degreeZeroBetaGroupCubic610,
    degreeZeroDeltaGroupCubic610, degreeZeroEpsilonGroupCubic610,
    degreeZeroZetaGroupCubic610, degreeZeroEtaGroupCubic610,
    degreeZeroThetaGroupCubic610]
  compute_degree
  omega

theorem cubicCone_allConstant_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C.natDegree = 0) (hD : D.natDegree = 0)
    (hE : E.natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hdeg :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E) (j / t) hjdiv hder
  have hle :=
    primitiveCubic_natDegree_le_zero_of_constants l alpha beta delta
      epsilon zeta eta theta hA hB hC hD hE
  omega


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

theorem cubicSupportCone610_of (A B C D E : k[X]) :
    CubicSupportCone610 A B C D E := by
  by_cases hABlt : 3 * A.natDegree < 2 * B.natDegree
  · -- B strictly outranks A
    by_cases hBClt : 4 * B.natDegree < 3 * C.natDegree
    · -- C strictly outranks B
      by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
      · -- D strictly outranks C
        by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
        · -- E strictly outranks D
          by_cases hpos : 0 < E.natDegree
          · -- nonempty cone E
            refine CubicSupportCone610.coneE ?_
            refine ⟨by omega, by omega, by omega, by omega, by omega⟩
          · -- ruler degree 0 ⇒ all constant
            refine CubicSupportCone610.allConst ?_
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · omega
            · omega
            · omega
            · omega
            · omega
        · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
          · -- E ties D
            by_cases hpos : 0 < D.natDegree
            · -- nonempty cone DE
              refine CubicSupportCone610.coneDE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · -- D strictly outranks E
            by_cases hpos : 0 < D.natDegree
            · -- nonempty cone D
              refine CubicSupportCone610.coneD ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
      · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
        · -- D ties C
          by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
          · -- E strictly outranks CD
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
            · -- E ties CD
              by_cases hpos : 0 < C.natDegree
              · -- nonempty cone CDE
                refine CubicSupportCone610.coneCDE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- CD strictly outranks E
              by_cases hpos : 0 < C.natDegree
              · -- nonempty cone CD
                refine CubicSupportCone610.coneCD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
        · -- C strictly outranks D
          by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
          · -- E strictly outranks C
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
            · -- E ties C
              by_cases hpos : 0 < C.natDegree
              · -- nonempty cone CE
                refine CubicSupportCone610.coneCE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- C strictly outranks E
              by_cases hpos : 0 < C.natDegree
              · -- nonempty cone C
                refine CubicSupportCone610.coneC ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
    · by_cases hBCeq : 4 * B.natDegree = 3 * C.natDegree
      · -- C ties B
        by_cases hBDlt : 5 * B.natDegree < 3 * D.natDegree
        · -- D strictly outranks BC
          by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
          · -- E strictly outranks D
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
            · -- E ties D
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone DE
                refine CubicSupportCone610.coneDE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- D strictly outranks E
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone D
                refine CubicSupportCone610.coneD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
        · by_cases hBDeq : 5 * B.natDegree = 3 * D.natDegree
          · -- D ties BC
            by_cases hBElt : 2 * B.natDegree < E.natDegree
            · -- E strictly outranks BCD
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hBEeq : 2 * B.natDegree = E.natDegree
              · -- E ties BCD
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BCDE
                  refine CubicSupportCone610.coneBCDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- BCD strictly outranks E
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BCD
                  refine CubicSupportCone610.coneBCD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · -- BC strictly outranks D
            by_cases hBElt : 2 * B.natDegree < E.natDegree
            · -- E strictly outranks BC
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hBEeq : 2 * B.natDegree = E.natDegree
              · -- E ties BC
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BCE
                  refine CubicSupportCone610.coneBCE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- BC strictly outranks E
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BC
                  refine CubicSupportCone610.coneBC ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
      · -- B strictly outranks C
        by_cases hBDlt : 5 * B.natDegree < 3 * D.natDegree
        · -- D strictly outranks B
          by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
          · -- E strictly outranks D
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
            · -- E ties D
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone DE
                refine CubicSupportCone610.coneDE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- D strictly outranks E
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone D
                refine CubicSupportCone610.coneD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
        · by_cases hBDeq : 5 * B.natDegree = 3 * D.natDegree
          · -- D ties B
            by_cases hBElt : 2 * B.natDegree < E.natDegree
            · -- E strictly outranks BD
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hBEeq : 2 * B.natDegree = E.natDegree
              · -- E ties BD
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BDE
                  refine CubicSupportCone610.coneBDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- BD strictly outranks E
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BD
                  refine CubicSupportCone610.coneBD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · -- B strictly outranks D
            by_cases hBElt : 2 * B.natDegree < E.natDegree
            · -- E strictly outranks B
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hBEeq : 2 * B.natDegree = E.natDegree
              · -- E ties B
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BE
                  refine CubicSupportCone610.coneBE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- B strictly outranks E
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone B
                  refine CubicSupportCone610.coneB ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
  · by_cases hABeq : 3 * A.natDegree = 2 * B.natDegree
    · -- B ties A
      by_cases hAClt : 2 * A.natDegree < C.natDegree
      · -- C strictly outranks AB
        by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
        · -- D strictly outranks C
          by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
          · -- E strictly outranks D
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
            · -- E ties D
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone DE
                refine CubicSupportCone610.coneDE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- D strictly outranks E
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone D
                refine CubicSupportCone610.coneD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
        · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
          · -- D ties C
            by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
            · -- E strictly outranks CD
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
              · -- E ties CD
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CDE
                  refine CubicSupportCone610.coneCDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- CD strictly outranks E
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CD
                  refine CubicSupportCone610.coneCD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · -- C strictly outranks D
            by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
            · -- E strictly outranks C
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
              · -- E ties C
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CE
                  refine CubicSupportCone610.coneCE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- C strictly outranks E
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone C
                  refine CubicSupportCone610.coneC ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
      · by_cases hACeq : 2 * A.natDegree = C.natDegree
        · -- C ties AB
          by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
          · -- D strictly outranks ABC
            by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
            · -- E strictly outranks D
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
              · -- E ties D
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone DE
                  refine CubicSupportCone610.coneDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- D strictly outranks E
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone D
                  refine CubicSupportCone610.coneD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
            · -- D ties ABC
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks ABCD
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties ABCD
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABCDE
                    refine CubicSupportCone610.coneABCDE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- ABCD strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABCD
                    refine CubicSupportCone610.coneABCD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
            · -- ABC strictly outranks D
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks ABC
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties ABC
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABCE
                    refine CubicSupportCone610.coneABCE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- ABC strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABC
                    refine CubicSupportCone610.coneABC ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
        · -- AB strictly outranks C
          by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
          · -- D strictly outranks AB
            by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
            · -- E strictly outranks D
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
              · -- E ties D
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone DE
                  refine CubicSupportCone610.coneDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- D strictly outranks E
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone D
                  refine CubicSupportCone610.coneD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
            · -- D ties AB
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks ABD
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties ABD
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABDE
                    refine CubicSupportCone610.coneABDE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- ABD strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABD
                    refine CubicSupportCone610.coneABD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
            · -- AB strictly outranks D
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks AB
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties AB
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABE
                    refine CubicSupportCone610.coneABE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- AB strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone AB
                    refine CubicSupportCone610.coneAB ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
    · -- A strictly outranks B
      by_cases hAClt : 2 * A.natDegree < C.natDegree
      · -- C strictly outranks A
        by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
        · -- D strictly outranks C
          by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
          · -- E strictly outranks D
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
            · -- E ties D
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone DE
                refine CubicSupportCone610.coneDE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- D strictly outranks E
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone D
                refine CubicSupportCone610.coneD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
        · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
          · -- D ties C
            by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
            · -- E strictly outranks CD
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
              · -- E ties CD
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CDE
                  refine CubicSupportCone610.coneCDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- CD strictly outranks E
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CD
                  refine CubicSupportCone610.coneCD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · -- C strictly outranks D
            by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
            · -- E strictly outranks C
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
              · -- E ties C
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CE
                  refine CubicSupportCone610.coneCE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- C strictly outranks E
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone C
                  refine CubicSupportCone610.coneC ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
      · by_cases hACeq : 2 * A.natDegree = C.natDegree
        · -- C ties A
          by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
          · -- D strictly outranks AC
            by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
            · -- E strictly outranks D
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
              · -- E ties D
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone DE
                  refine CubicSupportCone610.coneDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- D strictly outranks E
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone D
                  refine CubicSupportCone610.coneD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
            · -- D ties AC
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks ACD
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties ACD
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ACDE
                    refine CubicSupportCone610.coneACDE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- ACD strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ACD
                    refine CubicSupportCone610.coneACD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
            · -- AC strictly outranks D
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks AC
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties AC
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ACE
                    refine CubicSupportCone610.coneACE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- AC strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone AC
                    refine CubicSupportCone610.coneAC ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
        · -- A strictly outranks C
          by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
          · -- D strictly outranks A
            by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
            · -- E strictly outranks D
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
              · -- E ties D
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone DE
                  refine CubicSupportCone610.coneDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- D strictly outranks E
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone D
                  refine CubicSupportCone610.coneD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
            · -- D ties A
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks AD
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties AD
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ADE
                    refine CubicSupportCone610.coneADE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- AD strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone AD
                    refine CubicSupportCone610.coneAD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
            · -- A strictly outranks D
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks A
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties A
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone AE
                    refine CubicSupportCone610.coneAE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- A strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone A
                    refine CubicSupportCone610.coneA ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega

end CubicExhaust610


/-! ## Stage A residual: the source lies in `R = {A}` -/

section CubicADominant610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem normalized610ScaleZero_cubicADominantResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C D E : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
            eta theta A B C D E) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      CubicRatioConeA610 A B C D E := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg⟩ :=
    normalized610ScaleZero_cubicResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, ?_⟩
  cases cubicSupportCone610_of A B C D E with

  | coneA h => exact h
  | coneB h =>
    exact (cubicCone_B_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneC h =>
    exact (cubicCone_C_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneD h =>
    exact (cubicCone_D_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hjdiv hder).elim
  | coneE h =>
    exact (cubicCone_E_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneAB h =>
    exact (cubicCone_AB_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneAC h =>
    exact (cubicCone_AC_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneAD h =>
    exact (cubicCone_AD_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneAE h =>
    exact (cubicCone_AE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneBC h =>
    exact (cubicCone_BC_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneBD h =>
    exact (cubicCone_BD_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneBE h =>
    exact (cubicCone_BE_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneCD h =>
    exact (cubicCone_CD_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hlamDeg).elim
  | coneCE h =>
    exact (cubicCone_CE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h homiDeg).elim
  | coneDE h =>
    exact (cubicCone_DE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneABC h =>
    exact (cubicCone_ABC_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneABD h =>
    exact (cubicCone_ABD_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneABE h =>
    exact (cubicCone_ABE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneACD h =>
    exact (cubicCone_ACD_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hmuDeg).elim
  | coneACE h =>
    exact (cubicCone_ACE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h homiDeg).elim
  | coneADE h =>
    exact (cubicCone_ADE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneBCD h =>
    exact (cubicCone_BCD_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneBCE h =>
    exact (cubicCone_BCE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneBDE h =>
    exact (cubicCone_BDE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hmuDeg).elim
  | coneCDE h =>
    exact (cubicCone_CDE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneABCD h =>
    exact (cubicCone_ABCD_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneABCE h =>
    exact (cubicCone_ABCE_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneABDE h =>
    exact (cubicCone_ABDE_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneACDE h =>
    exact (cubicCone_ACDE_impossible l alpha beta delta
        epsilon zeta eta theta A B C D E h hkapDeg).elim
  | coneBCDE h =>
    exact (cubicCone_BCDE_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | coneABCDE h =>
    exact (cubicCone_ABCDE_impossible (j := j) (t := t) l
        alpha beta delta epsilon zeta eta theta A B C D E h
        hlamDeg hkapDeg hmuDeg homiDeg hjdiv hder).elim
  | allConst h =>
    exact (cubicCone_allConstant_impossible (j := j) (t := t) l alpha
        beta delta epsilon zeta eta theta A B C D E h.1 h.2.1 h.2.2.1
        h.2.2.2.1 h.2.2.2.2 hjdiv hder).elim

end CubicADominant610


#print axioms cubicC610_add
#print axioms degreeZeroKappaPolynomial610_eq_cubic
#print axioms degreeZeroLambdaPolynomial610_eq_cubic
#print axioms degreeZeroMuPolynomial610_eq_cubic
#print axioms degreeZeroOmicronPolynomial610_eq_cubic
#print axioms degreeZeroPrimitivePolynomial610_eq_cubic
#print axioms normalized610ScaleZero_cubicResidual
#print axioms normalized610ScaleZero_cubicADominantResidual

end Max11DegreeRoutes
