import Grok810ScaleZeroConeEliminationScratch
import Max11SpeedReflectDegLibScratch

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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
/-- Unique-`B`: `B` strictly outranks the other six free letters. -/
def UniqueHighBCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    A.natDegree < B.natDegree ∧
    C0.natDegree < B.natDegree ∧
    D0.natDegree < B.natDegree ∧
    E0.natDegree < B.natDegree ∧
    F0.natDegree < B.natDegree ∧
    G0.natDegree < B.natDegree

set_option maxHeartbeats 64000000 in
/-- Unique-`B` with `A` of degree zero (the parent leftover unique-`B`
chamber).  On this cone the face `B⁵` of `ο` is unique of degree
`5 deg B ≥ 5`. -/
def BLeadsOmicronCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  UniqueHighBCone810 A B C0 D0 E0 F0 G0 ∧
    A.natDegree = 0

set_option maxHeartbeats 64000000 in
/-- Unique-`C₀`. -/
def UniqueHighC0Cone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    A.natDegree < C0.natDegree ∧
    B.natDegree < C0.natDegree ∧
    D0.natDegree < C0.natDegree ∧
    E0.natDegree < C0.natDegree ∧
    F0.natDegree < C0.natDegree ∧
    G0.natDegree < C0.natDegree

set_option maxHeartbeats 64000000 in
/-- Unique-`C₀` with `A` and `B` of degree zero. -/
def C0LeadsMuCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  UniqueHighC0Cone810 A B C0 D0 E0 F0 G0 ∧
    A.natDegree = 0 ∧
    B.natDegree = 0

set_option maxHeartbeats 64000000 in
/-- Unique-`D₀`. -/
def UniqueHighD0Cone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < D0.natDegree ∧
    A.natDegree < D0.natDegree ∧
    B.natDegree < D0.natDegree ∧
    C0.natDegree < D0.natDegree ∧
    E0.natDegree < D0.natDegree ∧
    F0.natDegree < D0.natDegree ∧
    G0.natDegree < D0.natDegree

set_option maxHeartbeats 64000000 in
/-- Unique-`D₀` with `A` and `B` of degree zero. -/
def D0LeadsOmicronCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  UniqueHighD0Cone810 A B C0 D0 E0 F0 G0 ∧
    A.natDegree = 0 ∧
    B.natDegree = 0

set_option maxHeartbeats 64000000 in
/-- Unique nonconstant `E₀` with the other six letters of degree zero. -/
def E0LeadsMuCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    F0.natDegree = 0 ∧
    G0.natDegree = 0

set_option maxHeartbeats 64000000 in
/-- Unique nonconstant `F₀` with the other six letters of degree zero. -/
def F0LeadsXiCone810 (A B C0 D0 E0 F0 G0 : k[X]) : Prop :=
  0 < F0.natDegree ∧
    A.natDegree = 0 ∧
    B.natDegree = 0 ∧
    C0.natDegree = 0 ∧
    D0.natDegree = 0 ∧
    E0.natDegree = 0 ∧
    G0.natDegree = 0

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
private theorem zero_pow_two {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

set_option maxHeartbeats 64000000 in
private theorem zero_pow_three {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

set_option maxHeartbeats 64000000 in
private theorem zero_pow_four {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

set_option maxHeartbeats 64000000 in
private theorem zero_pow_five {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

set_option maxHeartbeats 64000000 in
private theorem zero_pow_six {R : Type*} [Semiring R] : (0 : R) ^ 6 = 0 :=
  zero_pow (by decide : (6 : ℕ) ≠ 0)

set_option maxHeartbeats 64000000 in
private theorem zero_pow_seven {R : Type*} [Semiring R] : (0 : R) ^ 7 = 0 :=
  zero_pow (by decide : (7 : ℕ) ≠ 0)

end DefectCones810

/-! ## Polynomial pullbacks of the first integrals -/

section FirstIntegralPolynomials810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
/-- `G₀`-linear coefficient of `μ`. -/
def muG0Coefficient810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 128 : k) • A ^ 2
    + (5 / 16 : k) • C0
    + (9 / 64 * l : k) • B
    + (3 / 4 * gamma : k) • 1

set_option maxHeartbeats 64000000 in
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


#print axioms AMaximalCone810.eq_1
#print axioms UniqueHighBCone810.eq_1
#print axioms BLeadsOmicronCone810.eq_1
#print axioms UniqueHighC0Cone810.eq_1
#print axioms C0LeadsMuCone810.eq_1
#print axioms UniqueHighD0Cone810.eq_1
#print axioms D0LeadsOmicronCone810.eq_1
#print axioms E0LeadsMuCone810.eq_1
#print axioms F0LeadsXiCone810.eq_1
#print axioms UniqueHighG0DegOneCone810.eq_1
#print axioms degreeZeroXiPolynomial810.eq_1
#print axioms degreeZeroMuPolynomial810.eq_1
#print axioms degreeZeroOmicronPolynomial810.eq_1
#print axioms degreeZeroXiNoA7Polynomial810.eq_1
#print axioms degreeZeroXiNoF02Polynomial810.eq_1
#print axioms degreeZeroMuNoB4Polynomial810.eq_1
#print axioms degreeZeroMuNoC03Polynomial810.eq_1
#print axioms degreeZeroMuNoE02Polynomial810.eq_1
#print axioms degreeZeroOmicronNoB5Polynomial810.eq_1
#print axioms degreeZeroOmicronNoD03Polynomial810.eq_1
#print axioms xiG0Coefficient810.eq_1
#print axioms muG0Coefficient810.eq_1
#print axioms omicronG0Coefficient810.eq_1

end Max11DegreeRoutes
