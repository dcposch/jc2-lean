import Grok810ScaleZeroConeEliminationScratch

/-! # Scale-zero first-integral faces for the normalized `(8,10)`, `H = 0` leaf

Continuation of `Grok810ScaleZeroConeEliminationScratch` on the constant
core `H = (C t)²`.  That file closed the unique Newton faces of the
degree-one primitive and recorded the leftover cones in
`normalized810ScaleZero_coneEliminationResidual`.  The unused first
integrals of the same monic depression — in particular the weight-`98`
cleared defect `ξ` and the weight-`105` cleared defect `ο`, together
with the weight-`84` integral `μ` — are ground constants on both
constant faces of `N`.

CAS job `derive_810_scale_zero_cone_defect_faces.py` (outer degrees
`(8,10)`, leading `h⁴`, `h⁵` with `h` a nonzero constant) substitutes
the triangular Faber constants into `xiResidual810`,
`omicronResidual810`, and `muResidual810`.  After that substitution
the load-free faces

* `-(165/65536) A⁷` of `ξ`, of degree `7 deg A`,
* `-(21/4096) B⁵` of `ο`, of degree `5 deg B`,
* `-(5/128) C₀³` of `μ`, of degree `3 deg C₀`,
* `-(5/128) D₀³` of `ο`, of degree `3 deg D₀`,
* `(5/32) E₀²` of `μ`, of degree `2 deg E₀`,
* `(5/32) F₀²` of `ξ`, of degree `2 deg F₀`

never meet a load term of equal degree (loads are ground constants).
Consequently a unique maximum among those weighted degrees is empty.
A constant free core is already empty by the parent.  Unique-`G₀` of
degree one with vanishing `G₀`-linear coefficients of `ξ`, `μ`, and
`ο` is recorded rather than forced (the primitive linear coefficient
`θ` is independent of those three).  Pair-ratio ties in which no
load-free face strictly leads are likewise recorded.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.  The theorems
`normalized810ScaleZero_impossible` and
`planeKeller810ScaleZeroExclusion_closed` are not claimed.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Weighted cones -/

section DefectCones810

variable {k : Type*} [Field k] [CharZero k]

/-- `A` is a (not necessarily unique) maximum of the free core.  On this
cone the face `A⁷` of `ξ` is unique of degree `7 deg A ≥ 7`. -/
def AMaximalCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    B.natDegree ≤ A.natDegree ∧
    C0.natDegree ≤ A.natDegree ∧
    D0.natDegree ≤ A.natDegree ∧
    E0.natDegree ≤ A.natDegree ∧
    F0.natDegree ≤ A.natDegree ∧
    G0.natDegree ≤ A.natDegree

/-- Unique-`B`: `B` strictly outranks the other six free letters. -/
def UniqueHighBCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    A.natDegree < B.natDegree ∧
    C0.natDegree < B.natDegree ∧
    D0.natDegree < B.natDegree ∧
    E0.natDegree < B.natDegree ∧
    F0.natDegree < B.natDegree ∧
    G0.natDegree < B.natDegree

/-- Unique-`B` with `A` of degree zero (the parent leftover unique-`B`
chamber).  On this cone the face `B⁵` of `ο` is unique of degree
`5 deg B ≥ 5`. -/
def BLeadsOmicronCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  UniqueHighBCone810 A B C0 D0 E0 F0 G0 ∧
    A.natDegree = 0

/-- Unique-`C₀`. -/
def UniqueHighC0Cone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    A.natDegree < C0.natDegree ∧
    B.natDegree < C0.natDegree ∧
    D0.natDegree < C0.natDegree ∧
    E0.natDegree < C0.natDegree ∧
    F0.natDegree < C0.natDegree ∧
    G0.natDegree < C0.natDegree

/-- Unique-`C₀` with `A` and `B` of degree zero. -/
def C0LeadsMuCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  UniqueHighC0Cone810 A B C0 D0 E0 F0 G0 ∧
    A.natDegree = 0 ∧
    B.natDegree = 0

/-- Unique-`D₀`. -/
def UniqueHighD0Cone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < D0.natDegree ∧
    A.natDegree < D0.natDegree ∧
    B.natDegree < D0.natDegree ∧
    C0.natDegree < D0.natDegree ∧
    E0.natDegree < D0.natDegree ∧
    F0.natDegree < D0.natDegree ∧
    G0.natDegree < D0.natDegree

/-- Unique-`D₀` with `A` and `B` of degree zero. -/
def D0LeadsOmicronCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  UniqueHighD0Cone810 A B C0 D0 E0 F0 G0 ∧
    A.natDegree = 0 ∧
    B.natDegree = 0

/-- Unique nonconstant `E₀` with the other six letters of degree zero. -/
def E0LeadsMuCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique nonconstant `F₀` with the other six letters of degree zero. -/
def F0LeadsXiCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < F0.natDegree ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    G0.natDegree = 0

/-- Unique-`G₀` of Newton degree one (the parent leftover chamber).
The other six letters then have degree zero. -/
def UniqueHighG0DegOneCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  G0.natDegree = 1 ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    F0.natDegree = 0

private theorem zero_pow_two {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

private theorem zero_pow_six {R : Type*} [Semiring R] : (0 : R) ^ 6 = 0 :=
  zero_pow (by decide : (6 : ℕ) ≠ 0)

private theorem zero_pow_seven {R : Type*} [Semiring R] : (0 : R) ^ 7 = 0 :=
  zero_pow (by decide : (7 : ℕ) ≠ 0)

end DefectCones810

/-! ## Polynomial pullbacks of the first integrals -/

section FirstIntegralPolynomials810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000 in
/-- Polynomial pullback of `xiResidual810` after the triangular Faber
coordinates are ground constants.  CAS: load-free face `A⁷`. -/
def degreeZeroXiPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(165 / 65536 : k) • A ^ 7
    + (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
    + (385 / 16384 : k) • (A ^ 5 * C0)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (35 / 1024 : k) • (A * B ^ 4)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (35 / 512 : k) • (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (245 / 8192 : k) • (A ^ 4 * E0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)
    + (357 / 16384 * beta : k) • (A ^ 4 * B)
    + (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (15 / 256 : k) • (A * C0 ^ 3)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)
    + (75 / 512 : k) • (A ^ 2 * C0 * E0)
    + (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4
    - (15 / 128 : k) • (C0 * D0 ^ 2)
    - (15 / 128 : k) • (C0 ^ 2 * E0)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)
    + (5 / 128 * delta : k) • B ^ 3
    - (5 / 64 : k) • (A * E0 ^ 2)
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)
    + (1 / 8 * epsilon : k) • (A * B ^ 2)
    + (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 32 : k) • F0 ^ 2
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2
    - (7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)
    - (1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 8000000 in
/-- Polynomial pullback of `muResidual810` after triangular substitution.
CAS: load-free faces `B⁴`, `C₀³`, `E₀²`. -/
def degreeZeroMuPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (5 / 128 : k) • C0 ^ 3
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)
    + (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)
    - (15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)
    - (3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 8000000 in
/-- Polynomial pullback of `omicronResidual810` after the triangular Faber
coordinates are ground constants.  CAS: load-free faces `B⁵`, `D₀³`. -/
def degreeZeroOmicronPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(12705 / 1048576 : k) • (A ^ 6 * B)
    - (34155 / 33554432 * l : k) • A ^ 7
    + (3745 / 65536 : k) • (A ^ 3 * B ^ 3)
    + (1365 / 16384 : k) • (A ^ 4 * B * C0)
    + (103005 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
    + (525 / 32768 : k) • (A ^ 5 * D0)
    + (19845 / 2097152 * l : k) • (A ^ 5 * C0)
    - (3927 / 2097152 * beta : k) • A ^ 6
    - (21 / 4096 : k) • B ^ 5
    - (105 / 1024 : k) • (A * B ^ 3 * C0)
    - (945 / 65536 * l : k) • (A * B ^ 4)
    - (2475 / 16384 : k) • (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : k) • (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : k) • (A ^ 3 * C0 * D0)
    - (3591 / 131072 * l : k) • (A ^ 3 * C0 ^ 2)
    - (725 / 8192 : k) • (A ^ 3 * B * E0)
    - (3591 / 65536 * l : k) • (A ^ 3 * B * D0)
    + (4095 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
    - (305 / 16384 : k) • (A ^ 4 * F0)
    - (3087 / 262144 * l : k) • (A ^ 4 * E0)
    + (1953 / 131072 * beta : k) • (A ^ 4 * C0)
    + (495 / 16384 * gamma : k) • (A ^ 4 * B)
    + (1089 / 131072 * delta : k) • A ^ 5
    + (45 / 1024 : k) • (B * C0 ^ 3)
    + (135 / 1024 : k) • (B ^ 2 * C0 * D0)
    + (567 / 16384 * l : k) • (B ^ 2 * C0 ^ 2)
    + (5 / 128 : k) • (B ^ 3 * E0)
    + (189 / 8192 * l : k) • (B ^ 3 * D0)
    - (189 / 32768 * beta : k) • B ^ 4
    + (135 / 1024 : k) • (A * C0 ^ 2 * D0)
    + (189 / 8192 * l : k) • (A * C0 ^ 3)
    + (135 / 1024 : k) • (A * B * D0 ^ 2)
    + (15 / 64 : k) • (A * B * C0 * E0)
    + (567 / 4096 * l : k) • (A * B * C0 * D0)
    + (105 / 1024 : k) • (A * B ^ 2 * F0)
    + (63 / 1024 * l : k) • (A * B ^ 2 * E0)
    - (567 / 8192 * beta : k) • (A * B ^ 2 * C0)
    - (45 / 1024 * gamma : k) • (A * B ^ 3)
    + (225 / 2048 : k) • (A ^ 2 * D0 * E0)
    + (135 / 4096 * l : k) • (A ^ 2 * D0 ^ 2)
    + (195 / 2048 : k) • (A ^ 2 * C0 * F0)
    + (477 / 8192 * l : k) • (A ^ 2 * C0 * E0)
    - (273 / 8192 * beta : k) • (A ^ 2 * C0 ^ 2)
    + (165 / 2048 : k) • (A ^ 2 * B * G0)
    + (207 / 4096 * l : k) • (A ^ 2 * B * F0)
    - (273 / 4096 * beta : k) • (A ^ 2 * B * D0)
    - (261 / 2048 * gamma : k) • (A ^ 2 * B * C0)
    - (45 / 512 * delta : k) • (A ^ 2 * B ^ 2)
    + (99 / 8192 * l : k) • (A ^ 3 * G0)
    - (147 / 8192 * beta : k) • (A ^ 3 * E0)
    - (81 / 2048 * gamma : k) • (A ^ 3 * D0)
    - (225 / 4096 * delta : k) • (A ^ 3 * C0)
    - (33 / 512 * epsilon : k) • (A ^ 3 * B)
    - (495 / 32768 * zeta : k) • A ^ 4
    - (5 / 128 : k) • D0 ^ 3
    - (25 / 128 : k) • (C0 * D0 * E0)
    - (27 / 512 * l : k) • (C0 * D0 ^ 2)
    - (5 / 64 : k) • (C0 ^ 2 * F0)
    - (45 / 1024 * l : k) • (C0 ^ 2 * E0)
    + (7 / 512 * beta : k) • C0 ^ 3
    - (5 / 64 : k) • (B * E0 ^ 2)
    - (5 / 32 : k) • (B * D0 * F0)
    - (45 / 512 * l : k) • (B * D0 * E0)
    - (15 / 128 : k) • (B * C0 * G0)
    - (9 / 128 * l : k) • (B * C0 * F0)
    + (21 / 256 * beta : k) • (B * C0 * D0)
    + (9 / 128 * gamma : k) • (B * C0 ^ 2)
    - (27 / 1024 * l : k) • (B ^ 2 * G0)
    + (35 / 1024 * beta : k) • (B ^ 2 * E0)
    + (9 / 128 * gamma : k) • (B ^ 2 * D0)
    + (45 / 512 * delta : k) • (B ^ 2 * C0)
    + (1 / 32 * epsilon : k) • B ^ 3
    - (15 / 128 : k) • (A * E0 * F0)
    - (9 / 256 * l : k) • (A * E0 ^ 2)
    - (15 / 128 : k) • (A * D0 * G0)
    - (9 / 128 * l : k) • (A * D0 * F0)
    + (21 / 512 * beta : k) • (A * D0 ^ 2)
    - (27 / 512 * l : k) • (A * C0 * G0)
    + (35 / 512 * beta : k) • (A * C0 * E0)
    + (9 / 64 * gamma : k) • (A * C0 * D0)
    + (45 / 512 * delta : k) • (A * C0 ^ 2)
    + (7 / 128 * beta : k) • (A * B * F0)
    + (15 / 128 * gamma : k) • (A * B * E0)
    + (45 / 256 * delta : k) • (A * B * D0)
    + (3 / 16 * epsilon : k) • (A * B * C0)
    + (45 / 512 * zeta : k) • (A * B ^ 2)
    + (15 / 512 * gamma : k) • (A ^ 2 * F0)
    + (15 / 256 * delta : k) • (A ^ 2 * E0)
    + (21 / 256 * epsilon : k) • (A ^ 2 * D0)
    + (81 / 1024 * zeta : k) • (A ^ 2 * C0)
    + (33 / 512 * eta : k) • (A ^ 2 * B)
    + (11 / 1024 * theta : k) • A ^ 3
    + (5 / 16 : k) • (F0 * G0)
    + (9 / 128 * l : k) • F0 ^ 2
    + (9 / 64 * l : k) • (E0 * G0)
    - (7 / 128 * beta : k) • E0 ^ 2
    - (7 / 64 * beta : k) • (D0 * F0)
    - (3 / 16 * gamma : k) • (D0 * E0)
    - (15 / 128 * delta : k) • D0 ^ 2
    - (3 / 32 * gamma : k) • (C0 * F0)
    - (5 / 32 * delta : k) • (C0 * E0)
    - (3 / 16 * epsilon : k) • (C0 * D0)
    - (9 / 128 * zeta : k) • C0 ^ 2
    - (5 / 64 * delta : k) • (B * F0)
    - (1 / 8 * epsilon : k) • (B * E0)
    - (9 / 64 * zeta : k) • (B * D0)
    - (3 / 32 * eta : k) • (B * C0)
    - (3 / 128 * theta : k) • B ^ 2
    - (1 / 16 * epsilon : k) • (A * F0)
    - (3 / 32 * zeta : k) • (A * E0)
    - (3 / 32 * eta : k) • (A * D0)
    - (3 / 64 * theta : k) • (A * C0)
    + (3 / 8 * zeta : k) • G0
    + (1 / 4 * eta : k) • F0
    + (1 / 8 * theta : k) • E0

set_option maxHeartbeats 8000000 in
/-- `ξ` with the unique `A⁷` face deleted. -/
def degreeZeroXiNoA7Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
    + (385 / 16384 : k) • (A ^ 5 * C0)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (35 / 1024 : k) • (A * B ^ 4)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (35 / 512 : k) • (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (245 / 8192 : k) • (A ^ 4 * E0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)
    + (357 / 16384 * beta : k) • (A ^ 4 * B)
    + (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (15 / 256 : k) • (A * C0 ^ 3)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)
    + (75 / 512 : k) • (A ^ 2 * C0 * E0)
    + (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4
    - (15 / 128 : k) • (C0 * D0 ^ 2)
    - (15 / 128 : k) • (C0 ^ 2 * E0)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)
    + (5 / 128 * delta : k) • B ^ 3
    - (5 / 64 : k) • (A * E0 ^ 2)
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)
    + (1 / 8 * epsilon : k) • (A * B ^ 2)
    + (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 32 : k) • F0 ^ 2
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2
    - (7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)
    - (1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 8000000 in
/-- `ξ` with the unique `F₀²` face deleted. -/
def degreeZeroXiNoF02Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(165 / 65536 : k) • A ^ 7
    + (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
    + (385 / 16384 : k) • (A ^ 5 * C0)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (35 / 1024 : k) • (A * B ^ 4)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (35 / 512 : k) • (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (245 / 8192 : k) • (A ^ 4 * E0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)
    + (357 / 16384 * beta : k) • (A ^ 4 * B)
    + (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (15 / 256 : k) • (A * C0 ^ 3)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)
    + (75 / 512 : k) • (A ^ 2 * C0 * E0)
    + (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4
    - (15 / 128 : k) • (C0 * D0 ^ 2)
    - (15 / 128 : k) • (C0 ^ 2 * E0)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)
    + (5 / 128 * delta : k) • B ^ 3
    - (5 / 64 : k) • (A * E0 ^ 2)
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)
    + (1 / 8 * epsilon : k) • (A * B ^ 2)
    + (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2
    - (7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)
    - (1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 8000000 in
/-- `μ` with the unique `B⁴` face deleted. -/
def degreeZeroMuNoB4Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (5 / 128 : k) • C0 ^ 3
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)
    + (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)
    - (15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)
    - (3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 8000000 in
/-- `μ` with the unique `C₀³` face deleted. -/
def degreeZeroMuNoC03Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)
    + (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)
    - (15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)
    - (3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 8000000 in
/-- `μ` with the unique `E₀²` face deleted. -/
def degreeZeroMuNoE02Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (5 / 128 : k) • C0 ^ 3
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)
    + (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)
    - (15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)
    - (3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 8000000 in
/-- `ο` with the unique `B⁵` face deleted. -/
def degreeZeroOmicronNoB5Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(12705 / 1048576 : k) • (A ^ 6 * B)
    - (34155 / 33554432 * l : k) • A ^ 7
    + (3745 / 65536 : k) • (A ^ 3 * B ^ 3)
    + (1365 / 16384 : k) • (A ^ 4 * B * C0)
    + (103005 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
    + (525 / 32768 : k) • (A ^ 5 * D0)
    + (19845 / 2097152 * l : k) • (A ^ 5 * C0)
    - (3927 / 2097152 * beta : k) • A ^ 6
    - (105 / 1024 : k) • (A * B ^ 3 * C0)
    - (945 / 65536 * l : k) • (A * B ^ 4)
    - (2475 / 16384 : k) • (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : k) • (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : k) • (A ^ 3 * C0 * D0)
    - (3591 / 131072 * l : k) • (A ^ 3 * C0 ^ 2)
    - (725 / 8192 : k) • (A ^ 3 * B * E0)
    - (3591 / 65536 * l : k) • (A ^ 3 * B * D0)
    + (4095 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
    - (305 / 16384 : k) • (A ^ 4 * F0)
    - (3087 / 262144 * l : k) • (A ^ 4 * E0)
    + (1953 / 131072 * beta : k) • (A ^ 4 * C0)
    + (495 / 16384 * gamma : k) • (A ^ 4 * B)
    + (1089 / 131072 * delta : k) • A ^ 5
    + (45 / 1024 : k) • (B * C0 ^ 3)
    + (135 / 1024 : k) • (B ^ 2 * C0 * D0)
    + (567 / 16384 * l : k) • (B ^ 2 * C0 ^ 2)
    + (5 / 128 : k) • (B ^ 3 * E0)
    + (189 / 8192 * l : k) • (B ^ 3 * D0)
    - (189 / 32768 * beta : k) • B ^ 4
    + (135 / 1024 : k) • (A * C0 ^ 2 * D0)
    + (189 / 8192 * l : k) • (A * C0 ^ 3)
    + (135 / 1024 : k) • (A * B * D0 ^ 2)
    + (15 / 64 : k) • (A * B * C0 * E0)
    + (567 / 4096 * l : k) • (A * B * C0 * D0)
    + (105 / 1024 : k) • (A * B ^ 2 * F0)
    + (63 / 1024 * l : k) • (A * B ^ 2 * E0)
    - (567 / 8192 * beta : k) • (A * B ^ 2 * C0)
    - (45 / 1024 * gamma : k) • (A * B ^ 3)
    + (225 / 2048 : k) • (A ^ 2 * D0 * E0)
    + (135 / 4096 * l : k) • (A ^ 2 * D0 ^ 2)
    + (195 / 2048 : k) • (A ^ 2 * C0 * F0)
    + (477 / 8192 * l : k) • (A ^ 2 * C0 * E0)
    - (273 / 8192 * beta : k) • (A ^ 2 * C0 ^ 2)
    + (165 / 2048 : k) • (A ^ 2 * B * G0)
    + (207 / 4096 * l : k) • (A ^ 2 * B * F0)
    - (273 / 4096 * beta : k) • (A ^ 2 * B * D0)
    - (261 / 2048 * gamma : k) • (A ^ 2 * B * C0)
    - (45 / 512 * delta : k) • (A ^ 2 * B ^ 2)
    + (99 / 8192 * l : k) • (A ^ 3 * G0)
    - (147 / 8192 * beta : k) • (A ^ 3 * E0)
    - (81 / 2048 * gamma : k) • (A ^ 3 * D0)
    - (225 / 4096 * delta : k) • (A ^ 3 * C0)
    - (33 / 512 * epsilon : k) • (A ^ 3 * B)
    - (495 / 32768 * zeta : k) • A ^ 4
    - (5 / 128 : k) • D0 ^ 3
    - (25 / 128 : k) • (C0 * D0 * E0)
    - (27 / 512 * l : k) • (C0 * D0 ^ 2)
    - (5 / 64 : k) • (C0 ^ 2 * F0)
    - (45 / 1024 * l : k) • (C0 ^ 2 * E0)
    + (7 / 512 * beta : k) • C0 ^ 3
    - (5 / 64 : k) • (B * E0 ^ 2)
    - (5 / 32 : k) • (B * D0 * F0)
    - (45 / 512 * l : k) • (B * D0 * E0)
    - (15 / 128 : k) • (B * C0 * G0)
    - (9 / 128 * l : k) • (B * C0 * F0)
    + (21 / 256 * beta : k) • (B * C0 * D0)
    + (9 / 128 * gamma : k) • (B * C0 ^ 2)
    - (27 / 1024 * l : k) • (B ^ 2 * G0)
    + (35 / 1024 * beta : k) • (B ^ 2 * E0)
    + (9 / 128 * gamma : k) • (B ^ 2 * D0)
    + (45 / 512 * delta : k) • (B ^ 2 * C0)
    + (1 / 32 * epsilon : k) • B ^ 3
    - (15 / 128 : k) • (A * E0 * F0)
    - (9 / 256 * l : k) • (A * E0 ^ 2)
    - (15 / 128 : k) • (A * D0 * G0)
    - (9 / 128 * l : k) • (A * D0 * F0)
    + (21 / 512 * beta : k) • (A * D0 ^ 2)
    - (27 / 512 * l : k) • (A * C0 * G0)
    + (35 / 512 * beta : k) • (A * C0 * E0)
    + (9 / 64 * gamma : k) • (A * C0 * D0)
    + (45 / 512 * delta : k) • (A * C0 ^ 2)
    + (7 / 128 * beta : k) • (A * B * F0)
    + (15 / 128 * gamma : k) • (A * B * E0)
    + (45 / 256 * delta : k) • (A * B * D0)
    + (3 / 16 * epsilon : k) • (A * B * C0)
    + (45 / 512 * zeta : k) • (A * B ^ 2)
    + (15 / 512 * gamma : k) • (A ^ 2 * F0)
    + (15 / 256 * delta : k) • (A ^ 2 * E0)
    + (21 / 256 * epsilon : k) • (A ^ 2 * D0)
    + (81 / 1024 * zeta : k) • (A ^ 2 * C0)
    + (33 / 512 * eta : k) • (A ^ 2 * B)
    + (11 / 1024 * theta : k) • A ^ 3
    + (5 / 16 : k) • (F0 * G0)
    + (9 / 128 * l : k) • F0 ^ 2
    + (9 / 64 * l : k) • (E0 * G0)
    - (7 / 128 * beta : k) • E0 ^ 2
    - (7 / 64 * beta : k) • (D0 * F0)
    - (3 / 16 * gamma : k) • (D0 * E0)
    - (15 / 128 * delta : k) • D0 ^ 2
    - (3 / 32 * gamma : k) • (C0 * F0)
    - (5 / 32 * delta : k) • (C0 * E0)
    - (3 / 16 * epsilon : k) • (C0 * D0)
    - (9 / 128 * zeta : k) • C0 ^ 2
    - (5 / 64 * delta : k) • (B * F0)
    - (1 / 8 * epsilon : k) • (B * E0)
    - (9 / 64 * zeta : k) • (B * D0)
    - (3 / 32 * eta : k) • (B * C0)
    - (3 / 128 * theta : k) • B ^ 2
    - (1 / 16 * epsilon : k) • (A * F0)
    - (3 / 32 * zeta : k) • (A * E0)
    - (3 / 32 * eta : k) • (A * D0)
    - (3 / 64 * theta : k) • (A * C0)
    + (3 / 8 * zeta : k) • G0
    + (1 / 4 * eta : k) • F0
    + (1 / 8 * theta : k) • E0

set_option maxHeartbeats 8000000 in
/-- `ο` with the unique `D₀³` face deleted. -/
def degreeZeroOmicronNoD03Polynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(12705 / 1048576 : k) • (A ^ 6 * B)
    - (34155 / 33554432 * l : k) • A ^ 7
    + (3745 / 65536 : k) • (A ^ 3 * B ^ 3)
    + (1365 / 16384 : k) • (A ^ 4 * B * C0)
    + (103005 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
    + (525 / 32768 : k) • (A ^ 5 * D0)
    + (19845 / 2097152 * l : k) • (A ^ 5 * C0)
    - (3927 / 2097152 * beta : k) • A ^ 6
    - (21 / 4096 : k) • B ^ 5
    - (105 / 1024 : k) • (A * B ^ 3 * C0)
    - (945 / 65536 * l : k) • (A * B ^ 4)
    - (2475 / 16384 : k) • (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : k) • (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : k) • (A ^ 3 * C0 * D0)
    - (3591 / 131072 * l : k) • (A ^ 3 * C0 ^ 2)
    - (725 / 8192 : k) • (A ^ 3 * B * E0)
    - (3591 / 65536 * l : k) • (A ^ 3 * B * D0)
    + (4095 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
    - (305 / 16384 : k) • (A ^ 4 * F0)
    - (3087 / 262144 * l : k) • (A ^ 4 * E0)
    + (1953 / 131072 * beta : k) • (A ^ 4 * C0)
    + (495 / 16384 * gamma : k) • (A ^ 4 * B)
    + (1089 / 131072 * delta : k) • A ^ 5
    + (45 / 1024 : k) • (B * C0 ^ 3)
    + (135 / 1024 : k) • (B ^ 2 * C0 * D0)
    + (567 / 16384 * l : k) • (B ^ 2 * C0 ^ 2)
    + (5 / 128 : k) • (B ^ 3 * E0)
    + (189 / 8192 * l : k) • (B ^ 3 * D0)
    - (189 / 32768 * beta : k) • B ^ 4
    + (135 / 1024 : k) • (A * C0 ^ 2 * D0)
    + (189 / 8192 * l : k) • (A * C0 ^ 3)
    + (135 / 1024 : k) • (A * B * D0 ^ 2)
    + (15 / 64 : k) • (A * B * C0 * E0)
    + (567 / 4096 * l : k) • (A * B * C0 * D0)
    + (105 / 1024 : k) • (A * B ^ 2 * F0)
    + (63 / 1024 * l : k) • (A * B ^ 2 * E0)
    - (567 / 8192 * beta : k) • (A * B ^ 2 * C0)
    - (45 / 1024 * gamma : k) • (A * B ^ 3)
    + (225 / 2048 : k) • (A ^ 2 * D0 * E0)
    + (135 / 4096 * l : k) • (A ^ 2 * D0 ^ 2)
    + (195 / 2048 : k) • (A ^ 2 * C0 * F0)
    + (477 / 8192 * l : k) • (A ^ 2 * C0 * E0)
    - (273 / 8192 * beta : k) • (A ^ 2 * C0 ^ 2)
    + (165 / 2048 : k) • (A ^ 2 * B * G0)
    + (207 / 4096 * l : k) • (A ^ 2 * B * F0)
    - (273 / 4096 * beta : k) • (A ^ 2 * B * D0)
    - (261 / 2048 * gamma : k) • (A ^ 2 * B * C0)
    - (45 / 512 * delta : k) • (A ^ 2 * B ^ 2)
    + (99 / 8192 * l : k) • (A ^ 3 * G0)
    - (147 / 8192 * beta : k) • (A ^ 3 * E0)
    - (81 / 2048 * gamma : k) • (A ^ 3 * D0)
    - (225 / 4096 * delta : k) • (A ^ 3 * C0)
    - (33 / 512 * epsilon : k) • (A ^ 3 * B)
    - (495 / 32768 * zeta : k) • A ^ 4
    - (25 / 128 : k) • (C0 * D0 * E0)
    - (27 / 512 * l : k) • (C0 * D0 ^ 2)
    - (5 / 64 : k) • (C0 ^ 2 * F0)
    - (45 / 1024 * l : k) • (C0 ^ 2 * E0)
    + (7 / 512 * beta : k) • C0 ^ 3
    - (5 / 64 : k) • (B * E0 ^ 2)
    - (5 / 32 : k) • (B * D0 * F0)
    - (45 / 512 * l : k) • (B * D0 * E0)
    - (15 / 128 : k) • (B * C0 * G0)
    - (9 / 128 * l : k) • (B * C0 * F0)
    + (21 / 256 * beta : k) • (B * C0 * D0)
    + (9 / 128 * gamma : k) • (B * C0 ^ 2)
    - (27 / 1024 * l : k) • (B ^ 2 * G0)
    + (35 / 1024 * beta : k) • (B ^ 2 * E0)
    + (9 / 128 * gamma : k) • (B ^ 2 * D0)
    + (45 / 512 * delta : k) • (B ^ 2 * C0)
    + (1 / 32 * epsilon : k) • B ^ 3
    - (15 / 128 : k) • (A * E0 * F0)
    - (9 / 256 * l : k) • (A * E0 ^ 2)
    - (15 / 128 : k) • (A * D0 * G0)
    - (9 / 128 * l : k) • (A * D0 * F0)
    + (21 / 512 * beta : k) • (A * D0 ^ 2)
    - (27 / 512 * l : k) • (A * C0 * G0)
    + (35 / 512 * beta : k) • (A * C0 * E0)
    + (9 / 64 * gamma : k) • (A * C0 * D0)
    + (45 / 512 * delta : k) • (A * C0 ^ 2)
    + (7 / 128 * beta : k) • (A * B * F0)
    + (15 / 128 * gamma : k) • (A * B * E0)
    + (45 / 256 * delta : k) • (A * B * D0)
    + (3 / 16 * epsilon : k) • (A * B * C0)
    + (45 / 512 * zeta : k) • (A * B ^ 2)
    + (15 / 512 * gamma : k) • (A ^ 2 * F0)
    + (15 / 256 * delta : k) • (A ^ 2 * E0)
    + (21 / 256 * epsilon : k) • (A ^ 2 * D0)
    + (81 / 1024 * zeta : k) • (A ^ 2 * C0)
    + (33 / 512 * eta : k) • (A ^ 2 * B)
    + (11 / 1024 * theta : k) • A ^ 3
    + (5 / 16 : k) • (F0 * G0)
    + (9 / 128 * l : k) • F0 ^ 2
    + (9 / 64 * l : k) • (E0 * G0)
    - (7 / 128 * beta : k) • E0 ^ 2
    - (7 / 64 * beta : k) • (D0 * F0)
    - (3 / 16 * gamma : k) • (D0 * E0)
    - (15 / 128 * delta : k) • D0 ^ 2
    - (3 / 32 * gamma : k) • (C0 * F0)
    - (5 / 32 * delta : k) • (C0 * E0)
    - (3 / 16 * epsilon : k) • (C0 * D0)
    - (9 / 128 * zeta : k) • C0 ^ 2
    - (5 / 64 * delta : k) • (B * F0)
    - (1 / 8 * epsilon : k) • (B * E0)
    - (9 / 64 * zeta : k) • (B * D0)
    - (3 / 32 * eta : k) • (B * C0)
    - (3 / 128 * theta : k) • B ^ 2
    - (1 / 16 * epsilon : k) • (A * F0)
    - (3 / 32 * zeta : k) • (A * E0)
    - (3 / 32 * eta : k) • (A * D0)
    - (3 / 64 * theta : k) • (A * C0)
    + (3 / 8 * zeta : k) • G0
    + (1 / 4 * eta : k) • F0
    + (1 / 8 * theta : k) • E0

set_option maxHeartbeats 8000000 in
/-- `G₀`-linear coefficient of `ξ` (no `G₀²` term). -/
def xiG0Coefficient810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (5 / 128 : k) • A ^ 3
    - (5 / 64 : k) • B ^ 2
    - (5 / 32 : k) • (A * C0)
    - (9 / 128 * l : k) • (A * B)
    + (5 / 16 : k) • E0
    + (9 / 64 * l : k) • D0
    + (1 / 2 * epsilon : k) • 1

/-- `G₀`-linear coefficient of `μ`. -/
def muG0Coefficient810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 128 : k) • A ^ 2
    + (5 / 16 : k) • C0
    + (9 / 64 * l : k) • B
    + (3 / 4 * gamma : k) • 1

/-- `G₀`-linear coefficient of `ο`. -/
def omicronG0Coefficient810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (165 / 2048 : k) • (A ^ 2 * B)
    + (99 / 8192 * l : k) • A ^ 3
    - (15 / 128 : k) • (B * C0)
    - (27 / 1024 * l : k) • B ^ 2
    - (15 / 128 : k) • (A * D0)
    - (27 / 512 * l : k) • (A * C0)
    + (5 / 16 : k) • F0
    + (9 / 64 * l : k) • E0
    + (3 / 8 * zeta : k) • 1

end FirstIntegralPolynomials810

/-! ## Splittings -/

section DefectSplittings810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiPolynomial810_eq_A7_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (-(165 / 65536 : k)) • A ^ 7 +
        degreeZeroXiNoA7Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, degreeZeroXiNoA7Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiPolynomial810_eq_F02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (5 / 32 : k) • F0 ^ 2 +
        degreeZeroXiNoF02Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, degreeZeroXiNoF02Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_B4_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (35 / 2048 : k) • B ^ 4 +
        degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuNoB4Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_C03_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (-(5 / 128 : k)) • C0 ^ 3 +
        degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuNoC03Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_E02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (5 / 32 : k) • E0 ^ 2 +
        degreeZeroMuNoE02Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuNoE02Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronPolynomial810_eq_B5_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (-(21 / 4096 : k)) • B ^ 5 +
        degreeZeroOmicronNoB5Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronPolynomial810,
    degreeZeroOmicronNoB5Polynomial810]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronPolynomial810_eq_D03_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (-(5 / 128 : k)) • D0 ^ 3 +
        degreeZeroOmicronNoD03Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronPolynomial810,
    degreeZeroOmicronNoD03Polynomial810]
  module

end DefectSplittings810

/-! ## Eight-term groups of rest polynomials -/

section DefectGroups810

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroXiNoA7G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
    + (385 / 16384 : k) • (A ^ 5 * C0)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (35 / 1024 : k) • (A * B ^ 4)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (35 / 512 : k) • (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (245 / 8192 : k) • (A ^ 4 * E0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)
    + (357 / 16384 * beta : k) • (A ^ 4 * B)

def degreeZeroXiNoA7G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (15 / 256 : k) • (A * C0 ^ 3)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)
    + (75 / 512 : k) • (A ^ 2 * C0 * E0)

def degreeZeroXiNoA7G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4
    - (15 / 128 : k) • (C0 * D0 ^ 2)

def degreeZeroXiNoA7G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 128 : k) • (C0 ^ 2 * E0)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)
    + (5 / 128 * delta : k) • B ^ 3

def degreeZeroXiNoA7G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(5 / 64 : k) • (A * E0 ^ 2)
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)
    + (1 / 8 * epsilon : k) • (A * B ^ 2)

def degreeZeroXiNoA7G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 32 : k) • F0 ^ 2
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2

def degreeZeroXiNoA7G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)

def degreeZeroXiNoA7G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiNoA7Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoA7Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroXiNoA7G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiNoA7Polynomial810,
    degreeZeroXiNoA7G1,
    degreeZeroXiNoA7G2,
    degreeZeroXiNoA7G3,
    degreeZeroXiNoA7G4,
    degreeZeroXiNoA7G5,
    degreeZeroXiNoA7G6,
    degreeZeroXiNoA7G7,
    degreeZeroXiNoA7G8]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G1, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G2, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G3, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G4, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G5, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G6, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G7, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoA7G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  simp only [degreeZeroXiNoA7G8, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven]
  compute_degree
  omega

theorem degreeZeroXiNoA7Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rw [degreeZeroXiNoA7Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroXiNoA7G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

def degreeZeroXiNoF02G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(165 / 65536 : k) • A ^ 7
    + (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
    + (385 / 16384 : k) • (A ^ 5 * C0)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (35 / 1024 : k) • (A * B ^ 4)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (35 / 512 : k) • (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (245 / 8192 : k) • (A ^ 4 * E0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)

def degreeZeroXiNoF02G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (357 / 16384 * beta : k) • (A ^ 4 * B)
    + (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (15 / 256 : k) • (A * C0 ^ 3)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)

def degreeZeroXiNoF02G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (75 / 512 : k) • (A ^ 2 * C0 * E0)
    + (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4

def degreeZeroXiNoF02G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 128 : k) • (C0 * D0 ^ 2)
    - (15 / 128 : k) • (C0 ^ 2 * E0)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)

def degreeZeroXiNoF02G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (5 / 128 * delta : k) • B ^ 3
    - (5 / 64 : k) • (A * E0 ^ 2)
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)

def degreeZeroXiNoF02G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (1 / 8 * epsilon : k) • (A * B ^ 2)
    + (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2

def degreeZeroXiNoF02G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)

def degreeZeroXiNoF02G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 16000000 in
theorem degreeZeroXiNoF02Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoF02Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroXiNoF02G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiNoF02Polynomial810,
    degreeZeroXiNoF02G1,
    degreeZeroXiNoF02G2,
    degreeZeroXiNoF02G3,
    degreeZeroXiNoF02G4,
    degreeZeroXiNoF02G5,
    degreeZeroXiNoF02G6,
    degreeZeroXiNoF02G7,
    degreeZeroXiNoF02G8]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoF02G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  simp only [degreeZeroXiNoF02G1, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hE, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoF02G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  simp only [degreeZeroXiNoF02G2, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hE, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoF02G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  simp only [degreeZeroXiNoF02G3, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hE, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoF02G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  simp only [degreeZeroXiNoF02G4, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hE, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoF02G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  simp only [degreeZeroXiNoF02G5, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hE, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoF02G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  simp only [degreeZeroXiNoF02G6, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hE, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoF02G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  simp only [degreeZeroXiNoF02G7, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hE, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroXiNoF02G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  simp only [degreeZeroXiNoF02G8, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hE, hG]
  compute_degree
  omega

theorem degreeZeroXiNoF02Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rw [degreeZeroXiNoF02Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroXiNoF02G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

def degreeZeroMuNoB4G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)

def degreeZeroMuNoB4G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (5 / 128 : k) • C0 ^ 3

def degreeZeroMuNoB4G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)

def degreeZeroMuNoB4G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)

def degreeZeroMuNoB4G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)

def degreeZeroMuNoB4G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)

def degreeZeroMuNoB4G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)

def degreeZeroMuNoB4G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoB4Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroMuNoB4G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuNoB4Polynomial810,
    degreeZeroMuNoB4G1,
    degreeZeroMuNoB4G2,
    degreeZeroMuNoB4G3,
    degreeZeroMuNoB4G4,
    degreeZeroMuNoB4G5,
    degreeZeroMuNoB4G6,
    degreeZeroMuNoB4G7,
    degreeZeroMuNoB4G8]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoB4G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroMuNoB4G1, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoB4G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroMuNoB4G2, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoB4G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroMuNoB4G3, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoB4G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroMuNoB4G4, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoB4G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroMuNoB4G5, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoB4G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroMuNoB4G6, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoB4G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroMuNoB4G7, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoB4G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroMuNoB4G8, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

theorem degreeZeroMuNoB4Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rw [degreeZeroMuNoB4Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroMuNoB4G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

def degreeZeroMuNoC03G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)

def degreeZeroMuNoC03G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4

def degreeZeroMuNoC03G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)

def degreeZeroMuNoC03G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)

def degreeZeroMuNoC03G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)

def degreeZeroMuNoC03G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)

def degreeZeroMuNoC03G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)

def degreeZeroMuNoC03G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoC03Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroMuNoC03G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuNoC03Polynomial810,
    degreeZeroMuNoC03G1,
    degreeZeroMuNoC03G2,
    degreeZeroMuNoC03G3,
    degreeZeroMuNoC03G4,
    degreeZeroMuNoC03G5,
    degreeZeroMuNoC03G6,
    degreeZeroMuNoC03G7,
    degreeZeroMuNoC03G8]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoC03G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroMuNoC03G1, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoC03G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroMuNoC03G2, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoC03G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroMuNoC03G3, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoC03G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroMuNoC03G4, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoC03G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroMuNoC03G5, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoC03G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroMuNoC03G6, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoC03G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroMuNoC03G7, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoC03G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroMuNoC03G8, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

theorem degreeZeroMuNoC03Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rw [degreeZeroMuNoC03Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroMuNoC03G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

def degreeZeroMuNoE02G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)

def degreeZeroMuNoE02G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4

def degreeZeroMuNoE02G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(5 / 128 : k) • C0 ^ 3
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)

def degreeZeroMuNoE02G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)

def degreeZeroMuNoE02G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)

def degreeZeroMuNoE02G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)

def degreeZeroMuNoE02G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)

def degreeZeroMuNoE02G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuNoE02Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoE02Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroMuNoE02G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuNoE02Polynomial810,
    degreeZeroMuNoE02G1,
    degreeZeroMuNoE02G2,
    degreeZeroMuNoE02G3,
    degreeZeroMuNoE02G4,
    degreeZeroMuNoE02G5,
    degreeZeroMuNoE02G6,
    degreeZeroMuNoE02G7,
    degreeZeroMuNoE02G8]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoE02G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoE02G1, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoE02G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoE02G2, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoE02G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoE02G3, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoE02G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoE02G4, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoE02G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoE02G5, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoE02G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoE02G6, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoE02G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoE02G7, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hF, hG]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroMuNoE02G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  simp only [degreeZeroMuNoE02G8, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA, hB, hC, hD, hF, hG]
  compute_degree
  omega

theorem degreeZeroMuNoE02Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rw [degreeZeroMuNoE02Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroMuNoE02G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

def degreeZeroOmicronNoB5G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(12705 / 1048576 : k) • (A ^ 6 * B)
    - (34155 / 33554432 * l : k) • A ^ 7
    + (3745 / 65536 : k) • (A ^ 3 * B ^ 3)
    + (1365 / 16384 : k) • (A ^ 4 * B * C0)
    + (103005 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
    + (525 / 32768 : k) • (A ^ 5 * D0)
    + (19845 / 2097152 * l : k) • (A ^ 5 * C0)
    - (3927 / 2097152 * beta : k) • A ^ 6
    - (105 / 1024 : k) • (A * B ^ 3 * C0)
    - (945 / 65536 * l : k) • (A * B ^ 4)
    - (2475 / 16384 : k) • (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : k) • (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : k) • (A ^ 3 * C0 * D0)
    - (3591 / 131072 * l : k) • (A ^ 3 * C0 ^ 2)

def degreeZeroOmicronNoB5G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(725 / 8192 : k) • (A ^ 3 * B * E0)
    - (3591 / 65536 * l : k) • (A ^ 3 * B * D0)
    + (4095 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
    - (305 / 16384 : k) • (A ^ 4 * F0)
    - (3087 / 262144 * l : k) • (A ^ 4 * E0)
    + (1953 / 131072 * beta : k) • (A ^ 4 * C0)
    + (495 / 16384 * gamma : k) • (A ^ 4 * B)
    + (1089 / 131072 * delta : k) • A ^ 5
    + (45 / 1024 : k) • (B * C0 ^ 3)
    + (135 / 1024 : k) • (B ^ 2 * C0 * D0)
    + (567 / 16384 * l : k) • (B ^ 2 * C0 ^ 2)
    + (5 / 128 : k) • (B ^ 3 * E0)
    + (189 / 8192 * l : k) • (B ^ 3 * D0)
    - (189 / 32768 * beta : k) • B ^ 4
    + (135 / 1024 : k) • (A * C0 ^ 2 * D0)

def degreeZeroOmicronNoB5G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (189 / 8192 * l : k) • (A * C0 ^ 3)
    + (135 / 1024 : k) • (A * B * D0 ^ 2)
    + (15 / 64 : k) • (A * B * C0 * E0)
    + (567 / 4096 * l : k) • (A * B * C0 * D0)
    + (105 / 1024 : k) • (A * B ^ 2 * F0)
    + (63 / 1024 * l : k) • (A * B ^ 2 * E0)
    - (567 / 8192 * beta : k) • (A * B ^ 2 * C0)
    - (45 / 1024 * gamma : k) • (A * B ^ 3)
    + (225 / 2048 : k) • (A ^ 2 * D0 * E0)
    + (135 / 4096 * l : k) • (A ^ 2 * D0 ^ 2)
    + (195 / 2048 : k) • (A ^ 2 * C0 * F0)
    + (477 / 8192 * l : k) • (A ^ 2 * C0 * E0)
    - (273 / 8192 * beta : k) • (A ^ 2 * C0 ^ 2)
    + (165 / 2048 : k) • (A ^ 2 * B * G0)
    + (207 / 4096 * l : k) • (A ^ 2 * B * F0)

def degreeZeroOmicronNoB5G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(273 / 4096 * beta : k) • (A ^ 2 * B * D0)
    - (261 / 2048 * gamma : k) • (A ^ 2 * B * C0)
    - (45 / 512 * delta : k) • (A ^ 2 * B ^ 2)
    + (99 / 8192 * l : k) • (A ^ 3 * G0)
    - (147 / 8192 * beta : k) • (A ^ 3 * E0)
    - (81 / 2048 * gamma : k) • (A ^ 3 * D0)
    - (225 / 4096 * delta : k) • (A ^ 3 * C0)
    - (33 / 512 * epsilon : k) • (A ^ 3 * B)
    - (495 / 32768 * zeta : k) • A ^ 4
    - (5 / 128 : k) • D0 ^ 3
    - (25 / 128 : k) • (C0 * D0 * E0)
    - (27 / 512 * l : k) • (C0 * D0 ^ 2)
    - (5 / 64 : k) • (C0 ^ 2 * F0)
    - (45 / 1024 * l : k) • (C0 ^ 2 * E0)
    + (7 / 512 * beta : k) • C0 ^ 3

def degreeZeroOmicronNoB5G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(5 / 64 : k) • (B * E0 ^ 2)
    - (5 / 32 : k) • (B * D0 * F0)
    - (45 / 512 * l : k) • (B * D0 * E0)
    - (15 / 128 : k) • (B * C0 * G0)
    - (9 / 128 * l : k) • (B * C0 * F0)
    + (21 / 256 * beta : k) • (B * C0 * D0)
    + (9 / 128 * gamma : k) • (B * C0 ^ 2)
    - (27 / 1024 * l : k) • (B ^ 2 * G0)
    + (35 / 1024 * beta : k) • (B ^ 2 * E0)
    + (9 / 128 * gamma : k) • (B ^ 2 * D0)
    + (45 / 512 * delta : k) • (B ^ 2 * C0)
    + (1 / 32 * epsilon : k) • B ^ 3
    - (15 / 128 : k) • (A * E0 * F0)
    - (9 / 256 * l : k) • (A * E0 ^ 2)
    - (15 / 128 : k) • (A * D0 * G0)

def degreeZeroOmicronNoB5G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(9 / 128 * l : k) • (A * D0 * F0)
    + (21 / 512 * beta : k) • (A * D0 ^ 2)
    - (27 / 512 * l : k) • (A * C0 * G0)
    + (35 / 512 * beta : k) • (A * C0 * E0)
    + (9 / 64 * gamma : k) • (A * C0 * D0)
    + (45 / 512 * delta : k) • (A * C0 ^ 2)
    + (7 / 128 * beta : k) • (A * B * F0)
    + (15 / 128 * gamma : k) • (A * B * E0)
    + (45 / 256 * delta : k) • (A * B * D0)
    + (3 / 16 * epsilon : k) • (A * B * C0)
    + (45 / 512 * zeta : k) • (A * B ^ 2)
    + (15 / 512 * gamma : k) • (A ^ 2 * F0)
    + (15 / 256 * delta : k) • (A ^ 2 * E0)
    + (21 / 256 * epsilon : k) • (A ^ 2 * D0)
    + (81 / 1024 * zeta : k) • (A ^ 2 * C0)

def degreeZeroOmicronNoB5G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (33 / 512 * eta : k) • (A ^ 2 * B)
    + (11 / 1024 * theta : k) • A ^ 3
    + (5 / 16 : k) • (F0 * G0)
    + (9 / 128 * l : k) • F0 ^ 2
    + (9 / 64 * l : k) • (E0 * G0)
    - (7 / 128 * beta : k) • E0 ^ 2
    - (7 / 64 * beta : k) • (D0 * F0)
    - (3 / 16 * gamma : k) • (D0 * E0)
    - (15 / 128 * delta : k) • D0 ^ 2
    - (3 / 32 * gamma : k) • (C0 * F0)
    - (5 / 32 * delta : k) • (C0 * E0)
    - (3 / 16 * epsilon : k) • (C0 * D0)
    - (9 / 128 * zeta : k) • C0 ^ 2
    - (5 / 64 * delta : k) • (B * F0)
    - (1 / 8 * epsilon : k) • (B * E0)

def degreeZeroOmicronNoB5G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(9 / 64 * zeta : k) • (B * D0)
    - (3 / 32 * eta : k) • (B * C0)
    - (3 / 128 * theta : k) • B ^ 2
    - (1 / 16 * epsilon : k) • (A * F0)
    - (3 / 32 * zeta : k) • (A * E0)
    - (3 / 32 * eta : k) • (A * D0)
    - (3 / 64 * theta : k) • (A * C0)
    + (3 / 8 * zeta : k) • G0
    + (1 / 4 * eta : k) • F0
    + (1 / 8 * theta : k) • E0

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronNoB5Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoB5Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroOmicronNoB5G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronNoB5Polynomial810,
    degreeZeroOmicronNoB5G1,
    degreeZeroOmicronNoB5G2,
    degreeZeroOmicronNoB5G3,
    degreeZeroOmicronNoB5G4,
    degreeZeroOmicronNoB5G5,
    degreeZeroOmicronNoB5G6,
    degreeZeroOmicronNoB5G7,
    degreeZeroOmicronNoB5G8]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoB5G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroOmicronNoB5G1, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoB5G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroOmicronNoB5G2, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoB5G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroOmicronNoB5G3, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoB5G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroOmicronNoB5G4, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoB5G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroOmicronNoB5G5, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoB5G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroOmicronNoB5G6, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoB5G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroOmicronNoB5G7, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoB5G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  simp only [degreeZeroOmicronNoB5G8, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0]
  compute_degree
  omega

theorem degreeZeroOmicronNoB5Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rw [degreeZeroOmicronNoB5Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroOmicronNoB5G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

def degreeZeroOmicronNoD03G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(12705 / 1048576 : k) • (A ^ 6 * B)
    - (34155 / 33554432 * l : k) • A ^ 7
    + (3745 / 65536 : k) • (A ^ 3 * B ^ 3)
    + (1365 / 16384 : k) • (A ^ 4 * B * C0)
    + (103005 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
    + (525 / 32768 : k) • (A ^ 5 * D0)
    + (19845 / 2097152 * l : k) • (A ^ 5 * C0)
    - (3927 / 2097152 * beta : k) • A ^ 6
    - (21 / 4096 : k) • B ^ 5
    - (105 / 1024 : k) • (A * B ^ 3 * C0)
    - (945 / 65536 * l : k) • (A * B ^ 4)
    - (2475 / 16384 : k) • (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : k) • (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : k) • (A ^ 3 * C0 * D0)

def degreeZeroOmicronNoD03G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(3591 / 131072 * l : k) • (A ^ 3 * C0 ^ 2)
    - (725 / 8192 : k) • (A ^ 3 * B * E0)
    - (3591 / 65536 * l : k) • (A ^ 3 * B * D0)
    + (4095 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
    - (305 / 16384 : k) • (A ^ 4 * F0)
    - (3087 / 262144 * l : k) • (A ^ 4 * E0)
    + (1953 / 131072 * beta : k) • (A ^ 4 * C0)
    + (495 / 16384 * gamma : k) • (A ^ 4 * B)
    + (1089 / 131072 * delta : k) • A ^ 5
    + (45 / 1024 : k) • (B * C0 ^ 3)
    + (135 / 1024 : k) • (B ^ 2 * C0 * D0)
    + (567 / 16384 * l : k) • (B ^ 2 * C0 ^ 2)
    + (5 / 128 : k) • (B ^ 3 * E0)
    + (189 / 8192 * l : k) • (B ^ 3 * D0)
    - (189 / 32768 * beta : k) • B ^ 4

def degreeZeroOmicronNoD03G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (135 / 1024 : k) • (A * C0 ^ 2 * D0)
    + (189 / 8192 * l : k) • (A * C0 ^ 3)
    + (135 / 1024 : k) • (A * B * D0 ^ 2)
    + (15 / 64 : k) • (A * B * C0 * E0)
    + (567 / 4096 * l : k) • (A * B * C0 * D0)
    + (105 / 1024 : k) • (A * B ^ 2 * F0)
    + (63 / 1024 * l : k) • (A * B ^ 2 * E0)
    - (567 / 8192 * beta : k) • (A * B ^ 2 * C0)
    - (45 / 1024 * gamma : k) • (A * B ^ 3)
    + (225 / 2048 : k) • (A ^ 2 * D0 * E0)
    + (135 / 4096 * l : k) • (A ^ 2 * D0 ^ 2)
    + (195 / 2048 : k) • (A ^ 2 * C0 * F0)
    + (477 / 8192 * l : k) • (A ^ 2 * C0 * E0)
    - (273 / 8192 * beta : k) • (A ^ 2 * C0 ^ 2)
    + (165 / 2048 : k) • (A ^ 2 * B * G0)

def degreeZeroOmicronNoD03G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (207 / 4096 * l : k) • (A ^ 2 * B * F0)
    - (273 / 4096 * beta : k) • (A ^ 2 * B * D0)
    - (261 / 2048 * gamma : k) • (A ^ 2 * B * C0)
    - (45 / 512 * delta : k) • (A ^ 2 * B ^ 2)
    + (99 / 8192 * l : k) • (A ^ 3 * G0)
    - (147 / 8192 * beta : k) • (A ^ 3 * E0)
    - (81 / 2048 * gamma : k) • (A ^ 3 * D0)
    - (225 / 4096 * delta : k) • (A ^ 3 * C0)
    - (33 / 512 * epsilon : k) • (A ^ 3 * B)
    - (495 / 32768 * zeta : k) • A ^ 4
    - (25 / 128 : k) • (C0 * D0 * E0)
    - (27 / 512 * l : k) • (C0 * D0 ^ 2)
    - (5 / 64 : k) • (C0 ^ 2 * F0)
    - (45 / 1024 * l : k) • (C0 ^ 2 * E0)
    + (7 / 512 * beta : k) • C0 ^ 3

def degreeZeroOmicronNoD03G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(5 / 64 : k) • (B * E0 ^ 2)
    - (5 / 32 : k) • (B * D0 * F0)
    - (45 / 512 * l : k) • (B * D0 * E0)
    - (15 / 128 : k) • (B * C0 * G0)
    - (9 / 128 * l : k) • (B * C0 * F0)
    + (21 / 256 * beta : k) • (B * C0 * D0)
    + (9 / 128 * gamma : k) • (B * C0 ^ 2)
    - (27 / 1024 * l : k) • (B ^ 2 * G0)
    + (35 / 1024 * beta : k) • (B ^ 2 * E0)
    + (9 / 128 * gamma : k) • (B ^ 2 * D0)
    + (45 / 512 * delta : k) • (B ^ 2 * C0)
    + (1 / 32 * epsilon : k) • B ^ 3
    - (15 / 128 : k) • (A * E0 * F0)
    - (9 / 256 * l : k) • (A * E0 ^ 2)
    - (15 / 128 : k) • (A * D0 * G0)

def degreeZeroOmicronNoD03G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(9 / 128 * l : k) • (A * D0 * F0)
    + (21 / 512 * beta : k) • (A * D0 ^ 2)
    - (27 / 512 * l : k) • (A * C0 * G0)
    + (35 / 512 * beta : k) • (A * C0 * E0)
    + (9 / 64 * gamma : k) • (A * C0 * D0)
    + (45 / 512 * delta : k) • (A * C0 ^ 2)
    + (7 / 128 * beta : k) • (A * B * F0)
    + (15 / 128 * gamma : k) • (A * B * E0)
    + (45 / 256 * delta : k) • (A * B * D0)
    + (3 / 16 * epsilon : k) • (A * B * C0)
    + (45 / 512 * zeta : k) • (A * B ^ 2)
    + (15 / 512 * gamma : k) • (A ^ 2 * F0)
    + (15 / 256 * delta : k) • (A ^ 2 * E0)
    + (21 / 256 * epsilon : k) • (A ^ 2 * D0)
    + (81 / 1024 * zeta : k) • (A ^ 2 * C0)

def degreeZeroOmicronNoD03G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (33 / 512 * eta : k) • (A ^ 2 * B)
    + (11 / 1024 * theta : k) • A ^ 3
    + (5 / 16 : k) • (F0 * G0)
    + (9 / 128 * l : k) • F0 ^ 2
    + (9 / 64 * l : k) • (E0 * G0)
    - (7 / 128 * beta : k) • E0 ^ 2
    - (7 / 64 * beta : k) • (D0 * F0)
    - (3 / 16 * gamma : k) • (D0 * E0)
    - (15 / 128 * delta : k) • D0 ^ 2
    - (3 / 32 * gamma : k) • (C0 * F0)
    - (5 / 32 * delta : k) • (C0 * E0)
    - (3 / 16 * epsilon : k) • (C0 * D0)
    - (9 / 128 * zeta : k) • C0 ^ 2
    - (5 / 64 * delta : k) • (B * F0)
    - (1 / 8 * epsilon : k) • (B * E0)

def degreeZeroOmicronNoD03G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(9 / 64 * zeta : k) • (B * D0)
    - (3 / 32 * eta : k) • (B * C0)
    - (3 / 128 * theta : k) • B ^ 2
    - (1 / 16 * epsilon : k) • (A * F0)
    - (3 / 32 * zeta : k) • (A * E0)
    - (3 / 32 * eta : k) • (A * D0)
    - (3 / 64 * theta : k) • (A * C0)
    + (3 / 8 * zeta : k) • G0
    + (1 / 4 * eta : k) • F0
    + (1 / 8 * theta : k) • E0

set_option maxHeartbeats 16000000 in
theorem degreeZeroOmicronNoD03Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoD03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroOmicronNoD03G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronNoD03Polynomial810,
    degreeZeroOmicronNoD03G1,
    degreeZeroOmicronNoD03G2,
    degreeZeroOmicronNoD03G3,
    degreeZeroOmicronNoD03G4,
    degreeZeroOmicronNoD03G5,
    degreeZeroOmicronNoD03G6,
    degreeZeroOmicronNoD03G7,
    degreeZeroOmicronNoD03G8]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoD03G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroOmicronNoD03G1, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoD03G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroOmicronNoD03G2, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoD03G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroOmicronNoD03G3, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoD03G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroOmicronNoD03G4, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoD03G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroOmicronNoD03G5, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoD03G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroOmicronNoD03G6, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoD03G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroOmicronNoD03G7, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem degreeZeroOmicronNoD03G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  simp only [degreeZeroOmicronNoD03G8, zero_mul, mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five, zero_pow_six, zero_pow_seven, hA0, hB0]
  compute_degree
  omega

theorem degreeZeroOmicronNoD03Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rw [degreeZeroOmicronNoD03Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroOmicronNoD03G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

end DefectGroups810

/-! ## Unique weighted faces -/

section DefectUniqueFaces810

variable {k : Type*} [Field k] [CharZero k]

theorem xi_A7_impossible_of_A_maximal
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (-(165 / 65536 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(165 / 65536 : k)) • A ^ 7).natDegree = 7 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroXiNoA7Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroXiPolynomial810_eq_A7_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

theorem omicron_B5_impossible_of_B_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨⟨hBpos, _⟩, _⟩
    simp [hB0] at hBpos
  have hc : (-(21 / 4096 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(21 / 4096 : k)) • B ^ 5).natDegree = 5 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroOmicronNoB5Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroOmicronPolynomial810_eq_B5_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hBpos, _⟩, _⟩
  omega

theorem mu_B4_impossible_of_B_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨⟨hBpos, _⟩, _⟩
    simp [hB0] at hBpos
  have hc : (35 / 2048 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((35 / 2048 : k) • B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoB4Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_B4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hBpos, _⟩, _⟩
  omega

theorem mu_C03_impossible_of_C0_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨⟨hCpos, _⟩, _⟩
    simp [hC0] at hCpos
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 128 : k)) • C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoC03Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_C03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hCpos, _⟩, _⟩
  omega

theorem omicron_D03_impossible_of_D0_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hD : D0 ≠ 0 := by
    intro hD0
    rcases hcone with ⟨⟨hDpos, _⟩, _⟩
    simp [hD0] at hDpos
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 128 : k)) • D0 ^ 3).natDegree = 3 * D0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroOmicronNoD03Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroOmicronPolynomial810_eq_D03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨⟨hDpos, _⟩, _⟩
  omega

theorem mu_E02_impossible_of_E0_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hE : E0 ≠ 0 := by
    intro hE0
    rcases hcone with ⟨hEpos, _⟩
    simp [hE0] at hEpos
  have hc : (5 / 32 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((5 / 32 : k) • E0 ^ 2).natDegree = 2 * E0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoE02Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_E02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, _⟩
  omega

theorem xi_F02_impossible_of_F0_leads
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hF : F0 ≠ 0 := by
    intro hF0
    rcases hcone with ⟨hFpos, _⟩
    simp [hF0] at hFpos
  have hc : (5 / 32 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((5 / 32 : k) • F0 ^ 2).natDegree = 2 * F0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroXiNoF02Polynomial810_natDegree_lt_of_groups l beta gamma
      delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroXiPolynomial810_eq_F02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hFpos, _⟩
  omega

end DefectUniqueFaces810

/-! ## Algebra map of the polynomial first integrals -/

section DefectAlgebraMap810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000 in
/-- Field-level integrated `ξ`. -/
def degreeZeroXiIntegrated810
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 beta gamma delta epsilon zeta eta theta : F) : F :=
  -(165 / 65536 : F) * A ^ 7
    + (1925 / 32768 : F) * (A ^ 4 * B ^ 2)
    + (385 / 16384 : F) * (A ^ 5 * C0)
    + (7245 / 524288 : F) * L * (A ^ 5 * B)
    - (35 / 1024 : F) * (A * B ^ 4)
    - (105 / 512 : F) * (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 : F) * L * (A ^ 2 * B ^ 3)
    - (35 / 512 : F) * (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : F) * (A ^ 3 * B * D0)
    - (315 / 4096 : F) * L * (A ^ 3 * B * C0)
    - (245 / 8192 : F) * (A ^ 4 * E0)
    - (4725 / 262144 : F) * L * (A ^ 4 * D0)
    + (357 / 16384 : F) * beta * (A ^ 4 * B)
    + (9 / 1024 : F) * gamma * A ^ 5
    + (45 / 512 : F) * (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : F) * (B ^ 3 * D0)
    + (63 / 2048 : F) * L * (B ^ 3 * C0)
    + (15 / 256 : F) * (A * C0 ^ 3)
    + (165 / 512 : F) * (A * B * C0 * D0)
    + (189 / 2048 : F) * L * (A * B * C0 ^ 2)
    + (75 / 512 : F) * (A * B ^ 2 * E0)
    + (693 / 8192 : F) * L * (A * B ^ 2 * D0)
    - (63 / 2048 : F) * beta * (A * B ^ 3)
    + (75 / 1024 : F) * (A ^ 2 * D0 ^ 2)
    + (75 / 512 : F) * (A ^ 2 * C0 * E0)
    + (693 / 8192 : F) * L * (A ^ 2 * C0 * D0)
    + (135 / 1024 : F) * (A ^ 2 * B * F0)
    + (315 / 4096 : F) * L * (A ^ 2 * B * E0)
    - (189 / 2048 : F) * beta * (A ^ 2 * B * C0)
    - (45 / 512 : F) * gamma * (A ^ 2 * B ^ 2)
    + (5 / 128 : F) * (A ^ 3 * G0)
    + (189 / 8192 : F) * L * (A ^ 3 * F0)
    - (231 / 8192 : F) * beta * (A ^ 3 * D0)
    - (15 / 256 : F) * gamma * (A ^ 3 * C0)
    - (165 / 2048 : F) * delta * (A ^ 3 * B)
    - (3 / 128 : F) * epsilon * A ^ 4
    - (15 / 128 : F) * (C0 * D0 ^ 2)
    - (15 / 128 : F) * (C0 ^ 2 * E0)
    - (63 / 1024 : F) * L * (C0 ^ 2 * D0)
    - (25 / 128 : F) * (B * D0 * E0)
    - (27 / 512 : F) * L * (B * D0 ^ 2)
    - (25 / 128 : F) * (B * C0 * F0)
    - (27 / 256 : F) * L * (B * C0 * E0)
    + (7 / 128 : F) * beta * (B * C0 ^ 2)
    - (5 / 64 : F) * (B ^ 2 * G0)
    - (45 / 1024 : F) * L * (B ^ 2 * F0)
    + (49 / 1024 : F) * beta * (B ^ 2 * D0)
    + (3 / 32 : F) * gamma * (B ^ 2 * C0)
    + (5 / 128 : F) * delta * B ^ 3
    - (5 / 64 : F) * (A * E0 ^ 2)
    - (5 / 32 : F) * (A * D0 * F0)
    - (45 / 512 : F) * L * (A * D0 * E0)
    - (5 / 32 : F) * (A * C0 * G0)
    - (45 / 512 : F) * L * (A * C0 * F0)
    + (49 / 512 : F) * beta * (A * C0 * D0)
    + (3 / 32 : F) * gamma * (A * C0 ^ 2)
    - (9 / 128 : F) * L * (A * B * G0)
    + (21 / 256 : F) * beta * (A * B * E0)
    + (21 / 128 : F) * gamma * (A * B * D0)
    + (15 / 64 : F) * delta * (A * B * C0)
    + (1 / 8 : F) * epsilon * (A * B ^ 2)
    + (35 / 1024 : F) * beta * (A ^ 2 * F0)
    + (9 / 128 : F) * gamma * (A ^ 2 * E0)
    + (105 / 1024 : F) * delta * (A ^ 2 * D0)
    + (1 / 8 : F) * epsilon * (A ^ 2 * C0)
    + (15 / 128 : F) * zeta * (A ^ 2 * B)
    + (1 / 32 : F) * eta * A ^ 3
    + (5 / 32 : F) * F0 ^ 2
    + (5 / 16 : F) * (E0 * G0)
    + (9 / 64 : F) * L * (E0 * F0)
    + (9 / 64 : F) * L * (D0 * G0)
    - (7 / 64 : F) * beta * (D0 * E0)
    - (3 / 32 : F) * gamma * D0 ^ 2
    - (7 / 64 : F) * beta * (C0 * F0)
    - (3 / 16 : F) * gamma * (C0 * E0)
    - (15 / 64 : F) * delta * (C0 * D0)
    - (1 / 8 : F) * epsilon * C0 ^ 2
    - (3 / 32 : F) * gamma * (B * F0)
    - (5 / 32 : F) * delta * (B * E0)
    - (3 / 16 : F) * epsilon * (B * D0)
    - (3 / 16 : F) * zeta * (B * C0)
    - (1 / 16 : F) * eta * B ^ 2
    - (5 / 64 : F) * delta * (A * F0)
    - (1 / 8 : F) * epsilon * (A * E0)
    - (9 / 64 : F) * zeta * (A * D0)
    - (1 / 8 : F) * eta * (A * C0)
    - (1 / 16 : F) * theta * (A * B)
    + (1 / 2 : F) * epsilon * G0
    + (3 / 8 : F) * zeta * F0
    + (1 / 4 : F) * eta * E0
    + (1 / 8 : F) * theta * D0

set_option maxHeartbeats 8000000 in
/-- Field-level integrated `μ`. -/
def degreeZeroMuIntegrated810
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 beta gamma delta epsilon zeta eta theta : F) : F :=
  (385 / 65536 : F) * A ^ 6
    - (385 / 4096 : F) * (A ^ 3 * B ^ 2)
    - (385 / 8192 : F) * (A ^ 4 * C0)
    - (7245 / 262144 : F) * L * (A ^ 4 * B)
    + (35 / 2048 : F) * B ^ 4
    + (105 / 512 : F) * (A * B ^ 2 * C0)
    + (315 / 8192 : F) * L * (A * B ^ 3)
    + (105 / 1024 : F) * (A ^ 2 * C0 ^ 2)
    + (105 / 512 : F) * (A ^ 2 * B * D0)
    + (945 / 8192 : F) * L * (A ^ 2 * B * C0)
    + (35 / 512 : F) * (A ^ 3 * E0)
    + (315 / 8192 : F) * L * (A ^ 3 * D0)
    - (357 / 8192 : F) * beta * (A ^ 3 * B)
    - (45 / 2048 : F) * gamma * A ^ 4
    - (5 / 128 : F) * C0 ^ 3
    - (15 / 64 : F) * (B * C0 * D0)
    - (63 / 1024 : F) * L * (B * C0 ^ 2)
    - (15 / 128 : F) * (B ^ 2 * E0)
    - (63 / 1024 : F) * L * (B ^ 2 * D0)
    + (21 / 1024 : F) * beta * B ^ 3
    - (15 / 128 : F) * (A * D0 ^ 2)
    - (15 / 64 : F) * (A * C0 * E0)
    - (63 / 512 : F) * L * (A * C0 * D0)
    - (15 / 64 : F) * (A * B * F0)
    - (63 / 512 : F) * L * (A * B * E0)
    + (63 / 512 : F) * beta * (A * B * C0)
    + (15 / 128 : F) * gamma * (A * B ^ 2)
    - (15 / 128 : F) * (A ^ 2 * G0)
    - (63 / 1024 : F) * L * (A ^ 2 * F0)
    + (63 / 1024 : F) * beta * (A ^ 2 * D0)
    + (15 / 128 : F) * gamma * (A ^ 2 * C0)
    + (165 / 1024 : F) * delta * (A ^ 2 * B)
    + (1 / 16 : F) * epsilon * A ^ 3
    + (5 / 32 : F) * E0 ^ 2
    + (5 / 16 : F) * (D0 * F0)
    + (9 / 64 : F) * L * (D0 * E0)
    + (5 / 16 : F) * (C0 * G0)
    + (9 / 64 : F) * L * (C0 * F0)
    - (7 / 64 : F) * beta * (C0 * D0)
    - (3 / 32 : F) * gamma * C0 ^ 2
    + (9 / 64 : F) * L * (B * G0)
    - (7 / 64 : F) * beta * (B * E0)
    - (3 / 16 : F) * gamma * (B * D0)
    - (15 / 64 : F) * delta * (B * C0)
    - (1 / 8 : F) * epsilon * B ^ 2
    - (7 / 64 : F) * beta * (A * F0)
    - (3 / 16 : F) * gamma * (A * E0)
    - (15 / 64 : F) * delta * (A * D0)
    - (1 / 4 : F) * epsilon * (A * C0)
    - (15 / 64 : F) * zeta * (A * B)
    - (3 / 32 : F) * eta * A ^ 2
    + (3 / 4 : F) * gamma * G0
    + (5 / 8 : F) * delta * F0
    + (1 / 2 : F) * epsilon * E0
    + (3 / 8 : F) * zeta * D0
    + (1 / 4 : F) * eta * C0
    + (1 / 8 : F) * theta * B

set_option maxHeartbeats 8000000 in
/-- Field-level integrated `ο`. -/
def degreeZeroOmicronIntegrated810
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 beta gamma delta epsilon zeta eta theta : F) : F :=
  -(12705 / 1048576 : F) * (A ^ 6 * B)
    - (34155 / 33554432 : F) * L * A ^ 7
    + (3745 / 65536 : F) * (A ^ 3 * B ^ 3)
    + (1365 / 16384 : F) * (A ^ 4 * B * C0)
    + (103005 / 4194304 : F) * L * (A ^ 4 * B ^ 2)
    + (525 / 32768 : F) * (A ^ 5 * D0)
    + (19845 / 2097152 : F) * L * (A ^ 5 * C0)
    - (3927 / 2097152 : F) * beta * A ^ 6
    - (21 / 4096 : F) * B ^ 5
    - (105 / 1024 : F) * (A * B ^ 3 * C0)
    - (945 / 65536 : F) * L * (A * B ^ 4)
    - (2475 / 16384 : F) * (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : F) * (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 : F) * L * (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : F) * (A ^ 3 * C0 * D0)
    - (3591 / 131072 : F) * L * (A ^ 3 * C0 ^ 2)
    - (725 / 8192 : F) * (A ^ 3 * B * E0)
    - (3591 / 65536 : F) * L * (A ^ 3 * B * D0)
    + (4095 / 131072 : F) * beta * (A ^ 3 * B ^ 2)
    - (305 / 16384 : F) * (A ^ 4 * F0)
    - (3087 / 262144 : F) * L * (A ^ 4 * E0)
    + (1953 / 131072 : F) * beta * (A ^ 4 * C0)
    + (495 / 16384 : F) * gamma * (A ^ 4 * B)
    + (1089 / 131072 : F) * delta * A ^ 5
    + (45 / 1024 : F) * (B * C0 ^ 3)
    + (135 / 1024 : F) * (B ^ 2 * C0 * D0)
    + (567 / 16384 : F) * L * (B ^ 2 * C0 ^ 2)
    + (5 / 128 : F) * (B ^ 3 * E0)
    + (189 / 8192 : F) * L * (B ^ 3 * D0)
    - (189 / 32768 : F) * beta * B ^ 4
    + (135 / 1024 : F) * (A * C0 ^ 2 * D0)
    + (189 / 8192 : F) * L * (A * C0 ^ 3)
    + (135 / 1024 : F) * (A * B * D0 ^ 2)
    + (15 / 64 : F) * (A * B * C0 * E0)
    + (567 / 4096 : F) * L * (A * B * C0 * D0)
    + (105 / 1024 : F) * (A * B ^ 2 * F0)
    + (63 / 1024 : F) * L * (A * B ^ 2 * E0)
    - (567 / 8192 : F) * beta * (A * B ^ 2 * C0)
    - (45 / 1024 : F) * gamma * (A * B ^ 3)
    + (225 / 2048 : F) * (A ^ 2 * D0 * E0)
    + (135 / 4096 : F) * L * (A ^ 2 * D0 ^ 2)
    + (195 / 2048 : F) * (A ^ 2 * C0 * F0)
    + (477 / 8192 : F) * L * (A ^ 2 * C0 * E0)
    - (273 / 8192 : F) * beta * (A ^ 2 * C0 ^ 2)
    + (165 / 2048 : F) * (A ^ 2 * B * G0)
    + (207 / 4096 : F) * L * (A ^ 2 * B * F0)
    - (273 / 4096 : F) * beta * (A ^ 2 * B * D0)
    - (261 / 2048 : F) * gamma * (A ^ 2 * B * C0)
    - (45 / 512 : F) * delta * (A ^ 2 * B ^ 2)
    + (99 / 8192 : F) * L * (A ^ 3 * G0)
    - (147 / 8192 : F) * beta * (A ^ 3 * E0)
    - (81 / 2048 : F) * gamma * (A ^ 3 * D0)
    - (225 / 4096 : F) * delta * (A ^ 3 * C0)
    - (33 / 512 : F) * epsilon * (A ^ 3 * B)
    - (495 / 32768 : F) * zeta * A ^ 4
    - (5 / 128 : F) * D0 ^ 3
    - (25 / 128 : F) * (C0 * D0 * E0)
    - (27 / 512 : F) * L * (C0 * D0 ^ 2)
    - (5 / 64 : F) * (C0 ^ 2 * F0)
    - (45 / 1024 : F) * L * (C0 ^ 2 * E0)
    + (7 / 512 : F) * beta * C0 ^ 3
    - (5 / 64 : F) * (B * E0 ^ 2)
    - (5 / 32 : F) * (B * D0 * F0)
    - (45 / 512 : F) * L * (B * D0 * E0)
    - (15 / 128 : F) * (B * C0 * G0)
    - (9 / 128 : F) * L * (B * C0 * F0)
    + (21 / 256 : F) * beta * (B * C0 * D0)
    + (9 / 128 : F) * gamma * (B * C0 ^ 2)
    - (27 / 1024 : F) * L * (B ^ 2 * G0)
    + (35 / 1024 : F) * beta * (B ^ 2 * E0)
    + (9 / 128 : F) * gamma * (B ^ 2 * D0)
    + (45 / 512 : F) * delta * (B ^ 2 * C0)
    + (1 / 32 : F) * epsilon * B ^ 3
    - (15 / 128 : F) * (A * E0 * F0)
    - (9 / 256 : F) * L * (A * E0 ^ 2)
    - (15 / 128 : F) * (A * D0 * G0)
    - (9 / 128 : F) * L * (A * D0 * F0)
    + (21 / 512 : F) * beta * (A * D0 ^ 2)
    - (27 / 512 : F) * L * (A * C0 * G0)
    + (35 / 512 : F) * beta * (A * C0 * E0)
    + (9 / 64 : F) * gamma * (A * C0 * D0)
    + (45 / 512 : F) * delta * (A * C0 ^ 2)
    + (7 / 128 : F) * beta * (A * B * F0)
    + (15 / 128 : F) * gamma * (A * B * E0)
    + (45 / 256 : F) * delta * (A * B * D0)
    + (3 / 16 : F) * epsilon * (A * B * C0)
    + (45 / 512 : F) * zeta * (A * B ^ 2)
    + (15 / 512 : F) * gamma * (A ^ 2 * F0)
    + (15 / 256 : F) * delta * (A ^ 2 * E0)
    + (21 / 256 : F) * epsilon * (A ^ 2 * D0)
    + (81 / 1024 : F) * zeta * (A ^ 2 * C0)
    + (33 / 512 : F) * eta * (A ^ 2 * B)
    + (11 / 1024 : F) * theta * A ^ 3
    + (5 / 16 : F) * (F0 * G0)
    + (9 / 128 : F) * L * F0 ^ 2
    + (9 / 64 : F) * L * (E0 * G0)
    - (7 / 128 : F) * beta * E0 ^ 2
    - (7 / 64 : F) * beta * (D0 * F0)
    - (3 / 16 : F) * gamma * (D0 * E0)
    - (15 / 128 : F) * delta * D0 ^ 2
    - (3 / 32 : F) * gamma * (C0 * F0)
    - (5 / 32 : F) * delta * (C0 * E0)
    - (3 / 16 : F) * epsilon * (C0 * D0)
    - (9 / 128 : F) * zeta * C0 ^ 2
    - (5 / 64 : F) * delta * (B * F0)
    - (1 / 8 : F) * epsilon * (B * E0)
    - (9 / 64 : F) * zeta * (B * D0)
    - (3 / 32 : F) * eta * (B * C0)
    - (3 / 128 : F) * theta * B ^ 2
    - (1 / 16 : F) * epsilon * (A * F0)
    - (3 / 32 : F) * zeta * (A * E0)
    - (3 / 32 : F) * eta * (A * D0)
    - (3 / 64 : F) * theta * (A * C0)
    + (3 / 8 : F) * zeta * G0
    + (1 / 4 : F) * eta * F0
    + (1 / 8 : F) * theta * E0

set_option maxHeartbeats 32000000 in
theorem xiResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    xiResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroXiIntegrated810 L A B C0 D0 E0 F0 G0 beta gamma delta
        epsilon zeta eta theta := by
  simp only [xiResidual810, degreeZeroXiIntegrated810, hbeta, hgamma,
    hdelta, hepsilon, hzeta, heta, htheta]
  ring

set_option maxHeartbeats 32000000 in
theorem omicronResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    omicronResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroOmicronIntegrated810 L A B C0 D0 E0 F0 G0 beta gamma delta
        epsilon zeta eta theta := by
  simp only [omicronResidual810, degreeZeroOmicronIntegrated810, hbeta,
    hgamma, hdelta, hepsilon, hzeta, heta, htheta]
  ring

set_option maxHeartbeats 64000000 in
theorem muResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    muResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroMuIntegrated810 L A B C0 D0 E0 F0 G0 beta gamma delta
        epsilon zeta eta theta := by
  have hW :
      W0 =
        theta +
          ((9 / 8 : F) * L * G0 +
            alphaResidual810 A P * F0 +
            (7 / 8 : F) * betaResidual810 L A B Q * E0 +
            (3 / 4 : F) * gammaResidual810 L A B C0 P R * D0 +
            (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * C0 +
            (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * B +
            (3 / 8 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 *
              A +
            (5 / 16 : F) * A * F0 + (5 / 16 : F) * B * E0 +
            (5 / 16 : F) * C0 * D0 - (5 / 128 : F) * B ^ 3 -
            (15 / 64 : F) * A * B * C0 - (15 / 128 : F) * A ^ 2 * D0 +
            (35 / 512 : F) * A ^ 3 * B +
            (9 / 64 : F) * L * A * E0 + (9 / 64 : F) * L * B * D0 +
            (9 / 128 : F) * L * C0 ^ 2 - (63 / 1024 : F) * L * A ^ 2 * C0 -
            (63 / 1024 : F) * L * A * B ^ 2 +
            (315 / 32768 : F) * L * A ^ 4 -
            (7 / 128 : F) * betaResidual810 L A B Q * B ^ 2 -
            (7 / 64 : F) * betaResidual810 L A B Q * A * C0 +
            (21 / 1024 : F) * betaResidual810 L A B Q * A ^ 3 -
            (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * B -
            (15 / 128 : F) * deltaResidual810 L A B C0 D0 P Q S0 *
              A ^ 2) := by
    have h := htheta
    simp only [thetaResidual810] at h
    linear_combination h
  simp only [muResidual810, degreeZeroMuIntegrated810, hW, hbeta, hgamma,
    hdelta, hepsilon, hzeta, heta, alphaResidual810]
  ring

set_option maxHeartbeats 32000000 in
theorem algebraMap_degreeZeroXiPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0) =
      degreeZeroXiIntegrated810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroXiPolynomial810, degreeZeroXiIntegrated810,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  try ring

set_option maxHeartbeats 32000000 in
theorem algebraMap_degreeZeroMuPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0) =
      degreeZeroMuIntegrated810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuIntegrated810,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  try ring

set_option maxHeartbeats 32000000 in
theorem algebraMap_degreeZeroOmicronPolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0) =
      degreeZeroOmicronIntegrated810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroOmicronPolynomial810,
    degreeZeroOmicronIntegrated810, map_add, map_sub, map_neg, map_mul,
    map_pow, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_one]
  try ring

theorem degreeZeroXiPolynomial810_eq_C_of_ratFuncDeriv
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0)) =
        0) :
    ∃ c : k,
      degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c := by
  let I :=
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
      A B C0 D0 E0 F0 G0
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa only [I] using hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

theorem degreeZeroMuPolynomial810_eq_C_of_ratFuncDeriv
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0)) =
        0) :
    ∃ c : k,
      degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c := by
  let I :=
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
      A B C0 D0 E0 F0 G0
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa only [I] using hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

theorem degreeZeroOmicronPolynomial810_eq_C_of_ratFuncDeriv
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hderiv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon
              zeta eta theta A B C0 D0 E0 F0 G0)) =
        0) :
    ∃ c : k,
      degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c := by
  let I :=
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa only [I] using hderiv
  have hd : I.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hdmap
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

theorem degreeZeroXiPolynomial810_natDegree_eq_zero_of_eq_C
    {l beta gamma delta epsilon zeta eta theta : k}
    {A B C0 D0 E0 F0 G0 : k[X]} {c : k}
    (h :
      degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c) :
    (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree =
      0 := by
  rw [h, natDegree_C]

theorem degreeZeroMuPolynomial810_natDegree_eq_zero_of_eq_C
    {l beta gamma delta epsilon zeta eta theta : k}
    {A B C0 D0 E0 F0 G0 : k[X]} {c : k}
    (h :
      degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c) :
    (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree =
      0 := by
  rw [h, natDegree_C]

theorem degreeZeroOmicronPolynomial810_natDegree_eq_zero_of_eq_C
    {l beta gamma delta epsilon zeta eta theta : k}
    {A B C0 D0 E0 F0 G0 : k[X]} {c : k}
    (h :
      degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C c) :
    (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree =
      0 := by
  rw [h, natDegree_C]

end DefectAlgebraMap810

/-! ## Source-facing constant first integrals -/

section SourceDefects810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 80000000 in
/-- Source-facing packet: the affine-depressed core has integrated `ξ`,
`μ`, and `ο` polynomials equal to ground constants. -/
theorem normalized810ScaleZero_defectPolynomials_eq_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 ∧
      degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C cXi ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C cMu ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C cOm ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, A, B, C0p, D0, E0, F0, G0, ht, hj, hjdiv, hHsq, hrowSrc, _hX,
      hcore⟩ :=
    normalized810ScaleZero_exists_primitivePolynomial hsource
  obtain ⟨hA, hB, hC, hD0, hE, hF, hG, hl, hder, hdeg⟩ := hcore
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hDjac : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    obtain ⟨j0, _hj0, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
    have hrow0 :
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j0 :=
      degreeZeroCoefficientJacobianRow_810 hp hq hjac
    have hj0 : j0 = j :=
      Polynomial.C_injective (hrow0.symm.trans (by simpa [p, q] using hrowSrc))
    simpa [hj0, bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  let hRF : RatFunc k := RatFunc.C t
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 q)
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hh : hRF ≠ 0 := by
    intro hzero
    apply ht
    apply RatFunc.C_injective
    simpa only [hRF, map_zero] using hzero
  have hp8' : p.coeff 8 = H ^ 4 := by simpa [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa [q] using hq10
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 8) = hRF ^ 8 := by
    have hpow : (C t ^ 2) ^ 4 = (C t : k[X]) ^ 8 := by
      rw [← pow_mul]
    simp only [hp8', hHsq, hpow, hRF, map_pow, RatFunc.algebraMap_C]
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    have hpow : (C t ^ 2) ^ 5 = (C t : k[X]) ^ 10 := by
      rw [← pow_mul]
    simp only [hq10', hHsq, hpow, hRF, map_pow, RatFunc.algebraMap_C]
  have hpDep := affineDepress_sourceOctic68 p hRF
    (octicDepressionR810 hRF a7) hp hh hpTop
  have hL0 : depressedL68 hRF (octicDepressionR810 hRF a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter hRF a7 hh
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]; rw [hpDep, coeff_depressedOctic68_seven, hL0]
  have hf8 : f.coeff 8 = 1 := by
    dsimp only [f]; rw [hpDep, coeff_depressedOctic68_eight]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n →
      (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, _hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (octicDepressionR810 hRF a7) hh hgTop hg_high_src
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (octicDepressionR810 hRF a7) hh hDjac
  have hdiv : RatFunc.C j / hRF = RatFunc.C (j / t) := by
    simp only [hRF, map_div₀]
  have hjacC : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C (j / t)) := by
    have hbr : differentialJacobian ratFuncDerivation68 f g =
        Polynomial.C (RatFunc.C j / hRF) := by
      simpa only [f, g] using hbracket
    simpa [hdiv] using hbr
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian ratFuncDerivation68 f g).coeff n = 0 := by
    rw [hjacC]
    simp [Polynomial.coeff_C, hn]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [show g.coeff 9 = RatFunc.C l from hl]
    exact ratFuncDerivation68_C l
  have h8 := (differentialJacobian_coeff_8_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 8 (by norm_num))
  have h7 := (differentialJacobian_coeff_7_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 7 (by norm_num))
  have h6 := (differentialJacobian_coeff_6_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 6 (by norm_num))
  have h5 := (differentialJacobian_coeff_5_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 5 (by norm_num))
  have h4 := (differentialJacobian_coeff_4_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 4 (by norm_num))
  have h3 := (differentialJacobian_coeff_3_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 3 (by norm_num))
  have h2 := (differentialJacobian_coeff_2_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 2 (by norm_num))
  obtain ⟨l', beta', gamma', delta', epsilon', zeta', eta', theta', hl',
      hbeta', hgamma', hdelta', hepsilon', hzeta', heta', htheta'⟩ :=
    monicOcticDecic_rhoLoads_exist_ground810 f g (j / t) hf_high hf8 hf7
      hg_high hg10 hLconst hjacC
  let d := ratFuncDerivation68 (k := k)
  have h15 := (differentialJacobian_coeff_15_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 15 (by norm_num))
  have h14 := (differentialJacobian_coeff_14_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 14 (by norm_num))
  have h13 := (differentialJacobian_coeff_13_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 9 (by norm_num))
  have halpha := alphaResidual810_deriv_zero d (f.coeff 6) (g.coeff 8)
    (by linear_combination h15)
  have hbeta0 := betaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (g.coeff 7) hLconst (by linear_combination h14)
  have hgamma0 := gammaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (g.coeff 8) (g.coeff 6) hLconst halpha
    (by linear_combination h13)
  have hdelta0 := deltaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
    (g.coeff 5) hLconst halpha hbeta0 (by linear_combination h12)
  have hepsilon0 := epsilonResidual810_deriv_zero d (g.coeff 9)
    (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha hbeta0
    hgamma0 (by linear_combination h11)
  have hzeta0 := zetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) hLconst
    halpha hbeta0 hgamma0 hdelta0 (by linear_combination h10)
  have heta0 := etaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 2) hLconst halpha hbeta0 hgamma0 hdelta0
    hepsilon0 (by linear_combination h9)
  have htheta0 := thetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 1) hLconst halpha hbeta0 hgamma0
    hdelta0 hepsilon0 hzeta0 (by linear_combination h8)
  have hiota0 := iotaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 0) hLconst halpha hbeta0
    hgamma0 hdelta0 hepsilon0 hzeta0 heta0 (by linear_combination h7)
  have hxi0 := xiResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h6) (by linear_combination h5)
    (by linear_combination h3)
  have hmu0 := muResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h5)
  have hom0 := omicronResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h6) (by linear_combination h5)
    (by linear_combination h4) (by linear_combination h2)
  have hkappa0 := kappaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) hLconst halpha hbeta0
    hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0
    (by linear_combination h8) (by linear_combination h6)
  have hnu0 := nuResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h6) (by linear_combination h4)
  have hxi_res :
      xiResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroXiIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact xiResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hmu_res :
      muResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroMuIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact muResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hom_res :
      omicronResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroOmicronIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact omicronResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hxi_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroXiPolynomial810 l' beta' gamma' delta' epsilon' zeta'
            eta' theta' A B C0p D0 E0 F0 G0) =
        xiResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hxi_res]
    exact algebraMap_degreeZeroXiPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hmu_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroMuPolynomial810 l' beta' gamma' delta' epsilon' zeta'
            eta' theta' A B C0p D0 E0 F0 G0) =
        muResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hmu_res]
    exact algebraMap_degreeZeroMuPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hom_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroOmicronPolynomial810 l' beta' gamma' delta' epsilon'
            zeta' eta' theta' A B C0p D0 E0 F0 G0) =
        omicronResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hom_res]
    exact algebraMap_degreeZeroOmicronPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hxi_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroXiPolynomial810 l' beta' gamma' delta' epsilon'
              zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hxi_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hxi0
  have hmu_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroMuPolynomial810 l' beta' gamma' delta' epsilon'
              zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hmu_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hmu0
  have hom_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroOmicronPolynomial810 l' beta' gamma' delta'
              epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hom_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hom0
  obtain ⟨cXi, hcXi⟩ :=
    degreeZeroXiPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hxi_deriv
  obtain ⟨cMu, hcMu⟩ :=
    degreeZeroMuPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hmu_deriv
  obtain ⟨cOm, hcOm⟩ :=
    degreeZeroOmicronPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma'
      delta' epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hom_deriv
  have hrho :
      rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroIntegratedPrimitive810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact rhoResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  let prim : k[X] :=
    degreeZeroPrimitivePolynomial810 l' beta' gamma' delta' epsilon' zeta'
      eta' theta' A B C0p D0 E0 F0 G0
  have hmap_prim :
      algebraMap k[X] (RatFunc k) prim =
        rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hrho]
    exact algebraMap_degreeZeroPrimitivePolynomial810 l' beta' gamma'
      delta' epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hder_prim :
      algebraMap k[X] (RatFunc k) (derivative prim) =
        algebraMap k[X] (RatFunc k) (C (j / t)) := by
    rw [← ratFuncDerivation46_polynomial]
    have hderiv' :
        ratFuncDerivation68 (algebraMap k[X] (RatFunc k) prim) =
          RatFunc.C (j / t) := by
      rw [hmap_prim]
      have hd_rho :
          d (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
              (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
              (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
              (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
              (g.coeff 1)) =
            g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) :=
        rhoResidual810_deriv_eq_row d (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst halpha
          hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
          hkappa0 hmu0 hnu0 hxi0 hom0
      have hrow0 :
          g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) =
            RatFunc.C (j / t) :=
        degreeZeroRow_eq_constant_of_monic_differentialJacobian d f g
          (RatFunc.C (j / t)) hf_high hf8 hf7 hg_high hg10 hLconst hjacC
      have := hd_rho.trans hrow0
      simpa [d] using this
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply,
      RatFunc.algebraMap_C] using hderiv'
  have hpolyder : derivative prim = C (j / t) :=
    (RatFunc.algebraMap_injective k) hder_prim
  have hdeg' : prim.natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 prim (j / t)
      (div_ne_zero hj ht) hpolyder
  exact ⟨t, j, lambda, cleared, l', beta', gamma', delta', epsilon', zeta',
    eta', theta', cXi, cMu, cOm, A, B, C0p, D0, E0, F0, G0, ht, hj, hjdiv,
    hHsq, hpolyder, hdeg', hcXi,
    degreeZeroXiPolynomial810_natDegree_eq_zero_of_eq_C hcXi, hcMu,
    degreeZeroMuPolynomial810_natDegree_eq_zero_of_eq_C hcMu, hcOm,
    degreeZeroOmicronPolynomial810_natDegree_eq_zero_of_eq_C hcOm⟩

end SourceDefects810

/-! ## Scale-zero faces and residual -/

section DefectFacesClosed810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Source-facing packet: `ξ`, `μ`, and `ο` are ground constants on the
free core, and every unique weighted face named above is empty. -/
theorem normalized810ScaleZero_defectFaces_closed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        Polynomial.C (j / t) ∧
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      ¬ AMaximalCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ E0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ F0LeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
          G0.natDegree = 0) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
      hder, hdeg, hcXi, hxi, hcMu, hmu, hcOm, hom⟩ :=
    normalized810ScaleZero_defectPolynomials_eq_C hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
    hder, hdeg, hxi, hmu, hom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hAmax
    exact xi_A7_impossible_of_A_maximal l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hAmax hxi
  · intro hBleads
    exact omicron_B5_impossible_of_B_leads l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hBleads hom
  · intro hCleads
    exact mu_C03_impossible_of_C0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hCleads hmu
  · intro hDleads
    exact omicron_D03_impossible_of_D0_leads l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hDleads hom
  · intro hEleads
    exact mu_E02_impossible_of_E0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hEleads hmu
  · intro hFleads
    exact xi_F02_impossible_of_F0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hFleads hxi
  · intro hconst
    exact degreeZeroPrimitivePolynomial810_false_of_constant_core l beta
      gamma delta epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0
      hjdiv hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1
      hconst.2.2.2.2.1 hconst.2.2.2.2.2.1 hconst.2.2.2.2.2.2 hder

/-- Remaining cones after every unique weighted `ξ`/`μ`/`ο` face named
above.  Unique-`G₀` of degree one with vanishing `G₀`-linear
coefficients of `ξ`, `μ`, and `ο` (CAS: those coefficients reduce to
`(1/2) ε`, `(3/4) γ`, and `(3/8) ζ` when the other letters vanish) is
the next comparison, together with the pair-ratio ties in which no
load-free face strictly leads.  The unused first integrals `κ` and `ν`
are available on that unique-`G₀` chamber. -/
theorem normalized810ScaleZero_coneDefectFacesResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      ¬ AMaximalCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ E0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ F0LeadsXiCone810 A B C0 D0 E0 F0 G0 := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
      hder, hdeg, hxi, hmu, hom, hAmax, hBleads, hCleads, hDleads, hEleads,
      hFleads, _hconst⟩ :=
    normalized810ScaleZero_defectFaces_closed hsource
  exact ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
    hder, hxi, hmu, hom, hAmax, hBleads, hCleads, hDleads, hEleads, hFleads⟩

/-- Glue of the two constant faces through the defect-face residual: the
scale-zero source is empty once the named leftover cones are excluded.
Neither leftover cone is claimed empty here. -/
theorem normalized810ScaleZero_impossible_of_defectFacesResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hres :
      (∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
          cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
        t ≠ 0 ∧ j ≠ 0 ∧ j / t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
          derivative
              (degreeZeroPrimitivePolynomial810 l beta gamma delta
                epsilon zeta eta theta A B C0 D0 E0 F0 G0) =
            Polynomial.C (j / t) ∧
          (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          ¬ AMaximalCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ E0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ F0LeadsXiCone810 A B C0 D0 E0 F0 G0) →
        False) :
    False :=
  hres (normalized810ScaleZero_coneDefectFacesResidual hsource)

end DefectFacesClosed810

#print axioms AMaximalCone810
#print axioms UniqueHighBCone810
#print axioms BLeadsOmicronCone810
#print axioms UniqueHighC0Cone810
#print axioms C0LeadsMuCone810
#print axioms UniqueHighD0Cone810
#print axioms D0LeadsOmicronCone810
#print axioms E0LeadsMuCone810
#print axioms F0LeadsXiCone810
#print axioms UniqueHighG0DegOneCone810
#print axioms degreeZeroXiPolynomial810
#print axioms degreeZeroMuPolynomial810
#print axioms degreeZeroOmicronPolynomial810
#print axioms xiResidual810_eq_integrated
#print axioms muResidual810_eq_integrated
#print axioms omicronResidual810_eq_integrated
#print axioms algebraMap_degreeZeroXiPolynomial810
#print axioms algebraMap_degreeZeroMuPolynomial810
#print axioms algebraMap_degreeZeroOmicronPolynomial810
#print axioms xi_A7_impossible_of_A_maximal
#print axioms omicron_B5_impossible_of_B_leads
#print axioms mu_C03_impossible_of_C0_leads
#print axioms omicron_D03_impossible_of_D0_leads
#print axioms mu_E02_impossible_of_E0_leads
#print axioms xi_F02_impossible_of_F0_leads
#print axioms normalized810ScaleZero_defectPolynomials_eq_C
#print axioms normalized810ScaleZero_defectFaces_closed
#print axioms normalized810ScaleZero_coneDefectFacesResidual
#print axioms normalized810ScaleZero_impossible_of_defectFacesResidual

end Max11DegreeRoutes
