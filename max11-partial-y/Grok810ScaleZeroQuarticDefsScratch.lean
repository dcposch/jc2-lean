import Grok810ScaleZeroSevenIntegralPacketScratch

/-! # Scale-zero quartic coordinates, Stage A, for normalized `(8,10)`, `H = 0`

Continuation of `Grok810ScaleZeroSevenIntegralPacketScratch`.  That file
supplies `t ≠ 0`, `j/t ≠ 0`, `H = (C t)²`,
`derivative (degreeZeroPrimitivePolynomial810 …) = C (j/t)` and
`natDegree = 0` for `ξ, μ, ο, κ, ν, π` as
`normalized810ScaleZero_sevenIntegralPacket`.

CAS jobs `scripts/derive_810_scale_zero_quartic_coordinates.py` and
`scripts/derive_810_scale_zero_quartic_cones.py` transcribe the seven
isobaric pullbacks, substitute the graded triangular automorphism
`C0 = C + (3/8)A^2`, `D0 = D + (1/2)AB`,
`E0 = E + (1/2)AC + (1/16)A^3`, `F0 = F + (1/4)AD + (1/16)A^2 B`,
`G0 = G + (1/4)AE + (1/16)A^2 C + (1/256)A^4`, and test every nonempty
argmax cone `R ⊆ {A,B,C,D,E,F,G}` by saturated Gröbner.  Saturated
Gröbner shows every cone except `R = {A}` is empty.  Lean certificates
close 125 of those; the full cone `R = {A,B,C,D,E,F,G}` has no
transcribed weighted-homogeneous certificate and remains a residual
disjunct.

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


/-! ## Quartic coordinates -/

section QuarticCoordinates810

variable {k : Type*} [Field k] [CharZero k]

def quarticC810 (A C0 : k[X]) : k[X] :=
  C0 - (3 / 8 : k) • A ^ 2

def quarticD810 (A B D0 : k[X]) : k[X] :=
  D0 - (1 / 2 : k) • (A * B)

def quarticE810 (A C0 E0 : k[X]) : k[X] :=
  E0 - (1 / 2 : k) • (A * C0) + (1 / 8 : k) • A ^ 3

def quarticF810 (A B D0 F0 : k[X]) : k[X] :=
  F0 - (1 / 4 : k) • (A * D0) + (1 / 16 : k) • (A ^ 2 * B)

def quarticG810 (A C0 E0 G0 : k[X]) : k[X] :=
  G0 - (1 / 4 : k) • (A * E0) + (1 / 16 : k) • (A ^ 2 * C0) -
    (3 / 256 : k) • A ^ 4

theorem quarticC810_add (A C0 : k[X]) :
    quarticC810 A C0 + (3 / 8 : k) • A ^ 2 = C0 := by
  simp only [quarticC810]
  exact sub_add_cancel _ _

theorem quarticD810_add (A B D0 : k[X]) :
    quarticD810 A B D0 + (1 / 2 : k) • (A * B) = D0 := by
  simp only [quarticD810]
  exact sub_add_cancel _ _

set_option maxHeartbeats 8000000 in
theorem quarticE810_inv (A C0 E0 : k[X]) :
    E0 =
      quarticE810 A C0 E0 + (1 / 2 : k) • (A * quarticC810 A C0) +
        (1 / 16 : k) • A ^ 3 := by
  simp only [quarticC810, quarticE810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem quarticF810_inv (A B D0 F0 : k[X]) :
    F0 =
      quarticF810 A B D0 F0 + (1 / 4 : k) • (A * quarticD810 A B D0) +
        (1 / 16 : k) • (A ^ 2 * B) := by
  simp only [quarticD810, quarticF810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticG810_inv (A C0 E0 G0 : k[X]) :
    G0 =
      quarticG810 A C0 E0 G0 + (1 / 4 : k) • (A * quarticE810 A C0 E0) +
        (1 / 16 : k) • (A ^ 2 * quarticC810 A C0) +
        (1 / 256 : k) • A ^ 4 := by
  simp only [quarticC810, quarticE810, quarticG810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

end QuarticCoordinates810


/-! ## Quartic first integrals -/

section QuarticIntegrals810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (5 / 1024 * delta : k) • A ^ 3
  + (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A


set_option maxHeartbeats 32000000 in
def degreeZeroMuQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2
  - (45 / 262144 * l : k) • (A ^ 4 * B)
  - (9 / 8192 * l : k) • (A ^ 3 * D)
  - (9 / 8192 * l : k) • (A ^ 2 * B * C)
  + (63 / 8192 * l : k) • (A * B ^ 3)
  - (9 / 1024 * l : k) • (A ^ 2 * F)
  - (9 / 512 * l : k) • (A * B * E)
  - (9 / 512 * l : k) • (A * C * D)
  - (63 / 1024 * l : k) • (B ^ 2 * D)
  - (63 / 1024 * l : k) • (B * C ^ 2)
  + (9 / 64 * l : k) • (B * G)
  + (9 / 64 * l : k) • (C * F)
  + (9 / 64 * l : k) • (D * E)
  - (7 / 8192 * beta : k) • (A ^ 3 * B)
  - (7 / 1024 * beta : k) • (A ^ 2 * D)
  + (7 / 512 * beta : k) • (A * B * C)
  + (21 / 1024 * beta : k) • B ^ 3
  - (7 / 64 * beta : k) • (A * F)
  - (7 / 64 * beta : k) • (B * E)
  - (7 / 64 * beta : k) • (C * D)
  + (3 / 128 * gamma : k) • (A * B ^ 2)
  - (3 / 16 * gamma : k) • (B * D)
  - (3 / 32 * gamma : k) • C ^ 2
  + (3 / 4 * gamma : k) • G
  - (5 / 1024 * delta : k) • (A ^ 2 * B)
  - (5 / 64 * delta : k) • (A * D)
  - (15 / 64 * delta : k) • (B * C)
  + (5 / 8 * delta : k) • F
  - (1 / 8 * epsilon : k) • B ^ 2
  + (1 / 2 * epsilon : k) • E
  - (3 / 64 * zeta : k) • (A * B)
  + (3 / 8 * zeta : k) • D
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B


set_option maxHeartbeats 32000000 in
def degreeZeroNuQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)
  + (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 4096 * l : k) • (A ^ 3 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * F)
  - (9 / 512 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2
  + (7 / 65536 * beta : k) • A ^ 5
  + (7 / 4096 * beta : k) • (A ^ 3 * C)
  - (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * D)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2
  + (3 / 128 * gamma : k) • (A * B * C)
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 32 * gamma : k) • (A * F)
  - (3 / 16 * gamma : k) • (B * E)
  - (3 / 16 * gamma : k) • (C * D)
  + (15 / 32768 * delta : k) • A ^ 4
  + (5 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 512 * delta : k) • (A * B ^ 2)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G
  - (1 / 16 * epsilon : k) • (A * D)
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (1 / 512 * zeta : k) • A ^ 3
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  - (1 / 32 * eta : k) • (A * B)
  + (1 / 4 * eta : k) • D
  + (1 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C


set_option maxHeartbeats 32000000 in
def degreeZeroXiQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2
  - (45 / 262144 * l : k) • (A ^ 4 * D)
  + (9 / 16384 * l : k) • (A ^ 3 * B * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 3)
  - (9 / 8192 * l : k) • (A ^ 3 * F)
  + (9 / 4096 * l : k) • (A ^ 2 * B * E)
  - (9 / 8192 * l : k) • (A ^ 2 * C * D)
  + (171 / 8192 * l : k) • (A * B ^ 2 * D)
  + (9 / 1024 * l : k) • (A * B * C ^ 2)
  + (63 / 2048 * l : k) • (B ^ 3 * C)
  - (9 / 512 * l : k) • (A * C * F)
  - (9 / 512 * l : k) • (A * D * E)
  - (45 / 1024 * l : k) • (B ^ 2 * F)
  - (27 / 256 * l : k) • (B * C * E)
  - (27 / 512 * l : k) • (B * D ^ 2)
  - (63 / 1024 * l : k) • (C ^ 2 * D)
  + (9 / 64 * l : k) • (D * G)
  + (9 / 64 * l : k) • (E * F)
  - (7 / 8192 * beta : k) • (A ^ 3 * D)
  + (7 / 2048 * beta : k) • (A ^ 2 * B * C)
  - (7 / 1024 * beta : k) • (A * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 2 * F)
  + (7 / 256 * beta : k) • (A * B * E)
  + (7 / 512 * beta : k) • (A * C * D)
  + (49 / 1024 * beta : k) • (B ^ 2 * D)
  + (7 / 128 * beta : k) • (B * C ^ 2)
  - (7 / 64 * beta : k) • (C * F)
  - (7 / 64 * beta : k) • (D * E)
  + (3 / 64 * gamma : k) • (A * B * D)
  + (3 / 32 * gamma : k) • (B ^ 2 * C)
  - (3 / 32 * gamma : k) • (B * F)
  - (3 / 16 * gamma : k) • (C * E)
  - (3 / 32 * gamma : k) • D ^ 2
  - (5 / 1024 * delta : k) • (A ^ 2 * D)
  + (5 / 128 * delta : k) • (A * B * C)
  + (5 / 128 * delta : k) • B ^ 3
  - (5 / 64 * delta : k) • (A * F)
  - (5 / 32 * delta : k) • (B * E)
  - (15 / 64 * delta : k) • (C * D)
  + (1 / 32 * epsilon : k) • (A * B ^ 2)
  - (3 / 16 * epsilon : k) • (B * D)
  - (1 / 8 * epsilon : k) • C ^ 2
  + (1 / 2 * epsilon : k) • G
  - (3 / 64 * zeta : k) • (A * D)
  - (3 / 16 * zeta : k) • (B * C)
  + (3 / 8 * zeta : k) • F
  - (1 / 16 * eta : k) • B ^ 2
  + (1 / 4 * eta : k) • E
  + (1 / 8 * theta : k) • D


set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)
  + (135 / 33554432 * l : k) • A ^ 7
  + (225 / 2097152 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (81 / 262144 * l : k) • (A ^ 4 * E)
  - (9 / 65536 * l : k) • (A ^ 3 * B * D)
  + (99 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  - (45 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (189 / 65536 * l : k) • (A * B ^ 4)
  + (9 / 8192 * l : k) • (A ^ 3 * G)
  - (9 / 4096 * l : k) • (A ^ 2 * B * F)
  + (27 / 8192 * l : k) • (A ^ 2 * C * E)
  + (45 / 4096 * l : k) • (A * B ^ 2 * E)
  + (99 / 4096 * l : k) • (A * B * C * D)
  + (9 / 8192 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 512 * l : k) • (A * C * G)
  - (9 / 256 * l : k) • (A * D * F)
  - (27 / 1024 * l : k) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)
  - (45 / 512 * l : k) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)
  - (27 / 512 * l : k) • (C * D ^ 2)
  + (9 / 64 * l : k) • (E * G)
  + (9 / 128 * l : k) • F ^ 2
  + (35 / 2097152 * beta : k) • A ^ 6
  + (49 / 131072 * beta : k) • (A ^ 4 * C)
  - (35 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 4096 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  - (91 / 8192 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (7 / 512 * beta : k) • (A * C * E)
  + (7 / 512 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2
  + (3 / 2048 * gamma : k) • (A ^ 2 * B * C)
  - (9 / 1024 * gamma : k) • (A * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 2 * F)
  + (3 / 128 * gamma : k) • (A * B * E)
  + (3 / 128 * gamma : k) • (A * C * D)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)
  + (9 / 131072 * delta : k) • A ^ 5
  + (5 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 4096 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 128 * delta : k) • (A * B * D)
  + (5 / 512 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2
  - (1 / 256 * epsilon : k) • (A ^ 2 * D)
  + (1 / 32 * epsilon : k) • (A * B * C)
  + (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 16 * epsilon : k) • (A * F)
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (9 / 32768 * zeta : k) • A ^ 4
  + (3 / 1024 * zeta : k) • (A ^ 2 * C)
  + (9 / 512 * zeta : k) • (A * B ^ 2)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (1 / 512 * eta : k) • (A ^ 2 * B)
  - (1 / 32 * eta : k) • (A * D)
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (1 / 1024 * theta : k) • A ^ 3
  + (1 / 64 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E


set_option maxHeartbeats 32000000 in
def piBaseGroupQuartic810
    (l : k) (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2
  + (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)


set_option maxHeartbeats 16000000 in
def piBetaGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (7 / 4096 : k) • (A ^ 3 * B * C)
  + (7 / 4096 : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 : k) • (A ^ 3 * F)
  + (7 / 512 : k) • (A ^ 2 * B * E)
  + (7 / 512 : k) • (A ^ 2 * C * D)
  - (21 / 256 : k) • (A * B ^ 2 * D)
  - (7 / 256 : k) • (A * B * C ^ 2)
  - (63 / 512 : k) • (B ^ 3 * C)
  - (7 / 64 : k) • (A * C * F)
  + (7 / 32 : k) • (A * D * E)
  + (21 / 128 : k) • (B ^ 2 * F)
  + (7 / 16 : k) • (B * C * E)
  + (7 / 32 : k) • (B * D ^ 2)
  + (7 / 32 : k) • (C ^ 2 * D)
  - (7 / 8 : k) • (E * F)


set_option maxHeartbeats 16000000 in
def piGammaGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (-(3 / 32 : k)) • (A * B ^ 2 * C)
  - (15 / 256 : k) • B ^ 4
  + (3 / 16 : k) • (A * D ^ 2)
  + (3 / 8 : k) • (B ^ 2 * E)
  + (3 / 4 : k) • (B * C * D)
  + (1 / 8 : k) • C ^ 3
  - (3 / 4 : k) • (D * F)
  - (3 / 4 : k) • E ^ 2


set_option maxHeartbeats 16000000 in
def piDeltaGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (5 / 512 : k) • (A ^ 2 * B * C)
  - (15 / 256 : k) • (A * B ^ 3)
  - (5 / 128 : k) • (A ^ 2 * F)
  + (5 / 32 : k) • (A * B * E)
  + (5 / 32 : k) • (A * C * D)
  + (15 / 32 : k) • (B ^ 2 * D)
  + (15 / 32 : k) • (B * C ^ 2)
  - (5 / 8 : k) • (C * F)
  - (5 / 4 : k) • (D * E)


set_option maxHeartbeats 16000000 in
def piEpsilonGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (1 / 4 : k) • (A * B * D)
  + (1 / 2 : k) • (B ^ 2 * C)
  - (1 / 2 : k) • (B * F)
  - (1 : k) • (C * E)
  - (1 / 2 : k) • D ^ 2


set_option maxHeartbeats 16000000 in
def piZetaGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (3 / 32 : k) • (A * B * C)
  + (5 / 32 : k) • B ^ 3
  - (3 / 8 : k) • (A * F)
  - (3 / 4 : k) • (B * E)
  - (3 / 4 : k) • (C * D)


set_option maxHeartbeats 16000000 in
def piEtaGroupQuartic810
    (A B C D E G : k[X]) : k[X] :=
  (1 / 16 : k) • (A * B ^ 2)
  - (1 / 2 : k) • (B * D)
  - (1 / 4 : k) • C ^ 2
  + (2 : k) • G


set_option maxHeartbeats 16000000 in
def piThetaGroupQuartic810
    (A B C D F : k[X]) : k[X] :=
  (-(1 / 4 : k)) • (B * C)
  + (1 : k) • F


def degreeZeroPiQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piBaseGroupQuartic810 l A B C D E F G +
    beta • piBetaGroupQuartic810 A B C D E F +
    gamma • piGammaGroupQuartic810 A B C D E F +
    delta • piDeltaGroupQuartic810 A B C D E F +
    epsilon • piEpsilonGroupQuartic810 A B C D E F +
    zeta • piZetaGroupQuartic810 A B C D E F +
    eta • piEtaGroupQuartic810 A B C D E G +
    theta • piThetaGroupQuartic810 A B C D F


set_option maxHeartbeats 32000000 in
def rhoBaseGroupQuartic810
    (l : k) (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  - (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)
  + (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * B * F)
  + (99 / 8192 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (9 / 4096 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (243 / 8192 * l : k) • (A * B ^ 3 * D)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)
  - (9 / 512 * l : k) • (A ^ 2 * D * F)
  + (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)
  + (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (9 / 256 * l : k) • (A * B * C * F)
  + (45 / 512 * l : k) • (A * B * D * E)
  + (9 / 1024 * l : k) • (A * C ^ 2 * E)
  + (9 / 256 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 64 * l : k) • (A * E * G)
  - (9 / 64 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2


set_option maxHeartbeats 16000000 in
def rhoBetaGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (25 / 1048576 : k) • A ^ 7
  + (21 / 32768 : k) • (A ^ 5 * C)
  - (119 / 262144 : k) • (A ^ 4 * B ^ 2)
  + (35 / 16384 : k) • (A ^ 4 * E)
  - (7 / 2048 : k) • (A ^ 3 * B * D)
  + (21 / 4096 : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 : k) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 : k) • (A * B ^ 4)
  + (21 / 512 : k) • (A ^ 2 * C * E)
  - (7 / 512 : k) • (A ^ 2 * D ^ 2)
  - (21 / 512 : k) • (A * B ^ 2 * E)
  - (7 / 128 : k) • (A * B * C * D)
  - (7 / 128 : k) • (B ^ 3 * D)
  - (91 / 1024 : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 : k) • (A * E ^ 2)
  + (7 / 32 : k) • (B * C * F)
  + (7 / 32 : k) • (B * D * E)
  + (7 / 64 : k) • (C ^ 2 * E)
  + (7 / 64 : k) • (C * D ^ 2)
  - (7 / 16 : k) • F ^ 2


set_option maxHeartbeats 16000000 in
def rhoGammaGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (3 / 2048 : k) • (A ^ 3 * B * C)
  + (3 / 2048 : k) • (A ^ 2 * B ^ 3)
  - (3 / 512 : k) • (A ^ 3 * F)
  + (3 / 256 : k) • (A ^ 2 * B * E)
  + (3 / 256 : k) • (A ^ 2 * C * D)
  - (9 / 128 : k) • (A * B ^ 2 * D)
  - (3 / 128 : k) • (A * B * C ^ 2)
  - (27 / 256 : k) • (B ^ 3 * C)
  - (3 / 32 : k) • (A * C * F)
  + (3 / 16 : k) • (A * D * E)
  + (9 / 64 : k) • (B ^ 2 * F)
  + (3 / 8 : k) • (B * C * E)
  + (3 / 16 : k) • (B * D ^ 2)
  + (3 / 16 : k) • (C ^ 2 * D)
  - (3 / 4 : k) • (E * F)


set_option maxHeartbeats 16000000 in
def rhoDeltaGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (25 / 262144 : k) • A ^ 6
  + (35 / 16384 : k) • (A ^ 4 * C)
  - (25 / 16384 : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 : k) • (A ^ 3 * E)
  - (5 / 512 : k) • (A ^ 2 * B * D)
  + (15 / 1024 : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 : k) • (A * B ^ 2 * C)
  - (135 / 4096 : k) • B ^ 4
  + (5 / 64 : k) • (A * C * E)
  + (5 / 64 : k) • (A * D ^ 2)
  + (25 / 128 : k) • (B ^ 2 * E)
  + (15 / 32 : k) • (B * C * D)
  + (5 / 64 : k) • C ^ 3
  - (5 / 8 : k) • (D * F)
  - (5 / 16 : k) • E ^ 2


set_option maxHeartbeats 16000000 in
def rhoEpsilonGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (-(1 / 256 : k)) • (A ^ 3 * D)
  + (1 / 64 : k) • (A ^ 2 * B * C)
  - (1 / 32 : k) • (A * B ^ 3)
  - (1 / 32 : k) • (A ^ 2 * F)
  + (1 / 8 : k) • (A * B * E)
  + (1 / 16 : k) • (A * C * D)
  + (7 / 32 : k) • (B ^ 2 * D)
  + (1 / 4 : k) • (B * C ^ 2)
  - (1 / 2 : k) • (C * F)
  - (1 / 2 : k) • (D * E)


set_option maxHeartbeats 16000000 in
def rhoZetaGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (3 / 8192 : k) • A ^ 5
  + (3 / 512 : k) • (A ^ 3 * C)
  - (3 / 2048 : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 : k) • (A ^ 2 * E)
  + (3 / 32 : k) • (A * B * D)
  + (27 / 128 : k) • (B ^ 2 * C)
  - (3 / 8 : k) • (B * F)
  - (3 / 8 : k) • (C * E)
  - (3 / 16 : k) • D ^ 2


set_option maxHeartbeats 16000000 in
def rhoEtaGroupQuartic810
    (A B C D E F : k[X]) : k[X] :=
  (-(1 / 512 : k)) • (A ^ 3 * B)
  - (1 / 64 : k) • (A ^ 2 * D)
  + (1 / 32 : k) • (A * B * C)
  + (3 / 64 : k) • B ^ 3
  - (1 / 4 : k) • (A * F)
  - (1 / 4 : k) • (B * E)
  - (1 / 4 : k) • (C * D)


set_option maxHeartbeats 16000000 in
def rhoThetaGroupQuartic810
    (A B C D E G : k[X]) : k[X] :=
  (5 / 4096 : k) • A ^ 4
  + (3 / 128 : k) • (A ^ 2 * C)
  + (1 / 128 : k) • (A * B ^ 2)
  + (1 / 8 : k) • (A * E)
  - (1 / 8 : k) • (B * D)
  - (1 / 16 : k) • C ^ 2
  + (1 : k) • G


def degreeZeroPrimitiveQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  rhoBaseGroupQuartic810 l A B C D E F G +
    beta • rhoBetaGroupQuartic810 A B C D E F +
    gamma • rhoGammaGroupQuartic810 A B C D E F +
    delta • rhoDeltaGroupQuartic810 A B C D E F +
    epsilon • rhoEpsilonGroupQuartic810 A B C D E F +
    zeta • rhoZetaGroupQuartic810 A B C D E F +
    eta • rhoEtaGroupQuartic810 A B C D E F +
    theta • rhoThetaGroupQuartic810 A B C D E G


end QuarticIntegrals810


/-! ## Transport identities -/

section QuarticTransport810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaPolynomial810_eq_quartic
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B))
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G := by
  simp only [degreeZeroKappaPolynomial810, degreeZeroKappaQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_eq_quartic
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B))
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuPolynomial810_eq_quartic
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B))
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G := by
  simp only [degreeZeroNuPolynomial810, degreeZeroNuQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiPolynomial810_eq_quartic
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B))
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G := by
  simp only [degreeZeroXiPolynomial810, degreeZeroXiQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronPolynomial810_eq_quartic
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B))
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G := by
  simp only [degreeZeroOmicronPolynomial810, degreeZeroOmicronQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem piBaseGroupPolynomial810_eq_quartic
    (l : k) (A B C D E F G : k[X]) :
    piBaseGroupPolynomial810 l A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B))
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      piBaseGroupQuartic810 l A B C D E F G := by
  simp only [piBaseGroupPolynomial810, piBaseGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem piBetaGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    piBetaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      piBetaGroupQuartic810 A B C D E F := by
  simp only [piBetaGroupPolynomial810, piBetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem piGammaGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    piGammaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      piGammaGroupQuartic810 A B C D E F := by
  simp only [piGammaGroupPolynomial810, piGammaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem piDeltaGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    piDeltaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      piDeltaGroupQuartic810 A B C D E F := by
  simp only [piDeltaGroupPolynomial810, piDeltaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem piEpsilonGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    piEpsilonGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      piEpsilonGroupQuartic810 A B C D E F := by
  simp only [piEpsilonGroupPolynomial810, piEpsilonGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem piZetaGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    piZetaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      piZetaGroupQuartic810 A B C D E F := by
  simp only [piZetaGroupPolynomial810, piZetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem piEtaGroupPolynomial810_eq_quartic
    (A B C D E G : k[X]) :
    piEtaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      piEtaGroupQuartic810 A B C D E G := by
  simp only [piEtaGroupPolynomial810, piEtaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem piThetaGroupPolynomial810_eq_quartic
    (A B C D F : k[X]) :
    piThetaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      piThetaGroupQuartic810 A B C D F := by
  simp only [piThetaGroupPolynomial810, piThetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem degreeZeroPiPolynomial810_eq_quartic
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B))
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G := by
  simp only [degreeZeroPiPolynomial810, degreeZeroPiQuartic810,
    piBaseGroupPolynomial810_eq_quartic, piBetaGroupPolynomial810_eq_quartic,
    piGammaGroupPolynomial810_eq_quartic, piDeltaGroupPolynomial810_eq_quartic,
    piEpsilonGroupPolynomial810_eq_quartic, piZetaGroupPolynomial810_eq_quartic,
    piEtaGroupPolynomial810_eq_quartic, piThetaGroupPolynomial810_eq_quartic]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem rhoBaseGroupPolynomial810_eq_quartic
    (l : k) (A B C D E F G : k[X]) :
    rhoBaseGroupPolynomial810 l A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B))
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      rhoBaseGroupQuartic810 l A B C D E F G := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem rhoBetaGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    rhoBetaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      rhoBetaGroupQuartic810 A B C D E F := by
  simp only [rhoBetaGroupPolynomial810, rhoBetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem rhoGammaGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    rhoGammaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      rhoGammaGroupQuartic810 A B C D E F := by
  simp only [rhoGammaGroupPolynomial810, rhoGammaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem rhoDeltaGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    rhoDeltaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      rhoDeltaGroupQuartic810 A B C D E F := by
  simp only [rhoDeltaGroupPolynomial810, rhoDeltaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem rhoEpsilonGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    rhoEpsilonGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      rhoEpsilonGroupQuartic810 A B C D E F := by
  simp only [rhoEpsilonGroupPolynomial810, rhoEpsilonGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem rhoZetaGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    rhoZetaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      rhoZetaGroupQuartic810 A B C D E F := by
  simp only [rhoZetaGroupPolynomial810, rhoZetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem rhoEtaGroupPolynomial810_eq_quartic
    (A B C D E F : k[X]) :
    rhoEtaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B)) =
      rhoEtaGroupQuartic810 A B C D E F := by
  simp only [rhoEtaGroupPolynomial810, rhoEtaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 32000000 in
theorem rhoThetaGroupPolynomial810_eq_quartic
    (A B C D E G : k[X]) :
    rhoThetaGroupPolynomial810 A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      rhoThetaGroupQuartic810 A B C D E G := by
  simp only [rhoThetaGroupPolynomial810, rhoThetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitivePolynomial810_eq_quartic
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta eta theta
        A B (C + (3 / 8 : k) • A ^ 2) (D + (1 / 2 : k) • (A * B))
        (E + (1 / 2 : k) • (A * C) + (1 / 16 : k) • A ^ 3)
        (F + (1 / 4 : k) • (A * D) + (1 / 16 : k) • (A ^ 2 * B))
        (G + (1 / 4 : k) • (A * E) + (1 / 16 : k) • (A ^ 2 * C) +
          (1 / 256 : k) • A ^ 4) =
      degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G := by
  simp only [degreeZeroPrimitivePolynomial810,
    degreeZeroPrimitiveQuartic810,
    rhoBaseGroupPolynomial810_eq_quartic, rhoBetaGroupPolynomial810_eq_quartic,
    rhoGammaGroupPolynomial810_eq_quartic, rhoDeltaGroupPolynomial810_eq_quartic,
    rhoEpsilonGroupPolynomial810_eq_quartic, rhoZetaGroupPolynomial810_eq_quartic,
    rhoEtaGroupPolynomial810_eq_quartic, rhoThetaGroupPolynomial810_eq_quartic]
  all_goals module


end QuarticTransport810


/-! ## Residual in quartic letters -/

section QuarticResidual810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 32000000 in
theorem normalized810ScaleZero_quarticResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0 := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
      hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg⟩ :=
    normalized810ScaleZero_sevenIntegralPacket hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, cXi, cMu, cOm, A, B, quarticC810 A C0, quarticD810 A B D0,
    quarticE810 A C0 E0, quarticF810 A B D0 F0, quarticG810 A C0 E0 G0,
    ht, hj, hjdiv, hHsq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hC0 := (quarticC810_add A C0).symm
    have hD0 := (quarticD810_add A B D0).symm
    have hE0 := quarticE810_inv A C0 E0
    have hF0 := quarticF810_inv A B D0 F0
    have hG0 := quarticG810_inv A C0 E0 G0
    rw [hC0, hD0, hE0, hF0, hG0] at hder
    rw [degreeZeroPrimitivePolynomial810_eq_quartic] at hder
    exact hder
  · have hC0 := (quarticC810_add A C0).symm
    have hD0 := (quarticD810_add A B D0).symm
    have hE0 := quarticE810_inv A C0 E0
    have hF0 := quarticF810_inv A B D0 F0
    have hG0 := quarticG810_inv A C0 E0 G0
    rw [hC0, hD0, hE0, hF0, hG0] at hxiDeg
    rw [degreeZeroXiPolynomial810_eq_quartic] at hxiDeg
    exact hxiDeg
  · have hC0 := (quarticC810_add A C0).symm
    have hD0 := (quarticD810_add A B D0).symm
    have hE0 := quarticE810_inv A C0 E0
    have hF0 := quarticF810_inv A B D0 F0
    have hG0 := quarticG810_inv A C0 E0 G0
    rw [hC0, hD0, hE0, hF0, hG0] at hmuDeg
    rw [degreeZeroMuPolynomial810_eq_quartic] at hmuDeg
    exact hmuDeg
  · have hC0 := (quarticC810_add A C0).symm
    have hD0 := (quarticD810_add A B D0).symm
    have hE0 := quarticE810_inv A C0 E0
    have hF0 := quarticF810_inv A B D0 F0
    have hG0 := quarticG810_inv A C0 E0 G0
    rw [hC0, hD0, hE0, hF0, hG0] at homiDeg
    rw [degreeZeroOmicronPolynomial810_eq_quartic] at homiDeg
    exact homiDeg
  · have hC0 := (quarticC810_add A C0).symm
    have hD0 := (quarticD810_add A B D0).symm
    have hE0 := quarticE810_inv A C0 E0
    have hF0 := quarticF810_inv A B D0 F0
    have hG0 := quarticG810_inv A C0 E0 G0
    rw [hC0, hD0, hE0, hF0, hG0] at hkapDeg
    rw [degreeZeroKappaPolynomial810_eq_quartic] at hkapDeg
    exact hkapDeg
  · have hC0 := (quarticC810_add A C0).symm
    have hD0 := (quarticD810_add A B D0).symm
    have hE0 := quarticE810_inv A C0 E0
    have hF0 := quarticF810_inv A B D0 F0
    have hG0 := quarticG810_inv A C0 E0 G0
    rw [hC0, hD0, hE0, hF0, hG0] at hnuDeg
    rw [degreeZeroNuPolynomial810_eq_quartic] at hnuDeg
    exact hnuDeg
  · have hC0 := (quarticC810_add A C0).symm
    have hD0 := (quarticD810_add A B D0).symm
    have hE0 := quarticE810_inv A C0 E0
    have hF0 := quarticF810_inv A B D0 F0
    have hG0 := quarticG810_inv A C0 E0 G0
    rw [hC0, hD0, hE0, hF0, hG0] at hpiDeg
    rw [degreeZeroPiPolynomial810_eq_quartic] at hpiDeg
    exact hpiDeg

end QuarticResidual810


/-! ## The 127 argmax cones -/

section QuarticCones810

variable {k : Type*} [Field k] [CharZero k]


def QuarticRatioConeA810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 3 * A.natDegree > 2 * B.natDegree
    ∧ 2 * A.natDegree > C.natDegree
    ∧ 5 * A.natDegree > 2 * D.natDegree
    ∧ 3 * A.natDegree > E.natDegree
    ∧ 7 * A.natDegree > 2 * F.natDegree
    ∧ 4 * A.natDegree > G.natDegree


def QuarticRatioConeB810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeC810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * D.natDegree < 5 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree
    ∧ 4 * F.natDegree < 7 * C.natDegree
    ∧ G.natDegree < 2 * C.natDegree


def QuarticRatioConeD810 (A B C D E F G : k[X]) : Prop :=
  0 < D.natDegree
    ∧ 5 * A.natDegree < 2 * D.natDegree
    ∧ 5 * B.natDegree < 3 * D.natDegree
    ∧ 5 * C.natDegree < 4 * D.natDegree
    ∧ 5 * E.natDegree < 6 * D.natDegree
    ∧ 5 * F.natDegree < 7 * D.natDegree
    ∧ 5 * G.natDegree < 8 * D.natDegree


def QuarticRatioConeE810 (A B C D E F G : k[X]) : Prop :=
  0 < E.natDegree
    ∧ 3 * A.natDegree < E.natDegree
    ∧ 2 * B.natDegree < E.natDegree
    ∧ 3 * C.natDegree < 2 * E.natDegree
    ∧ 6 * D.natDegree < 5 * E.natDegree
    ∧ 6 * F.natDegree < 7 * E.natDegree
    ∧ 3 * G.natDegree < 4 * E.natDegree


def QuarticRatioConeF810 (A B C D E F G : k[X]) : Prop :=
  0 < F.natDegree
    ∧ 7 * A.natDegree < 2 * F.natDegree
    ∧ 7 * B.natDegree < 3 * F.natDegree
    ∧ 7 * C.natDegree < 4 * F.natDegree
    ∧ 7 * D.natDegree < 5 * F.natDegree
    ∧ 7 * E.natDegree < 6 * F.natDegree
    ∧ 7 * G.natDegree < 8 * F.natDegree


def QuarticRatioConeG810 (A B C D E F G : k[X]) : Prop :=
  0 < G.natDegree
    ∧ 4 * A.natDegree < G.natDegree
    ∧ 8 * B.natDegree < 3 * G.natDegree
    ∧ 2 * C.natDegree < G.natDegree
    ∧ 8 * D.natDegree < 5 * G.natDegree
    ∧ 4 * E.natDegree < 3 * G.natDegree
    ∧ 8 * F.natDegree < 7 * G.natDegree


def QuarticRatioConeAB810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeAC810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeAD810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < D.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeAE810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < E.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeAF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeAG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < G.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeBC810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBD810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBE810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBF810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < F.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree


def QuarticRatioConeCD810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 4 * D.natDegree = 5 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree
    ∧ 4 * F.natDegree < 7 * C.natDegree
    ∧ G.natDegree < 2 * C.natDegree


def QuarticRatioConeCE810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * E.natDegree = 3 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * D.natDegree < 5 * C.natDegree
    ∧ 4 * F.natDegree < 7 * C.natDegree
    ∧ G.natDegree < 2 * C.natDegree


def QuarticRatioConeCF810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < F.natDegree
    ∧ 4 * F.natDegree = 7 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * D.natDegree < 5 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree
    ∧ G.natDegree < 2 * C.natDegree


def QuarticRatioConeCG810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < G.natDegree
    ∧ G.natDegree = 2 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * D.natDegree < 5 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree
    ∧ 4 * F.natDegree < 7 * C.natDegree


def QuarticRatioConeDE810 (A B C D E F G : k[X]) : Prop :=
  0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 5 * E.natDegree = 6 * D.natDegree
    ∧ 5 * A.natDegree < 2 * D.natDegree
    ∧ 5 * B.natDegree < 3 * D.natDegree
    ∧ 5 * C.natDegree < 4 * D.natDegree
    ∧ 5 * F.natDegree < 7 * D.natDegree
    ∧ 5 * G.natDegree < 8 * D.natDegree


def QuarticRatioConeDF810 (A B C D E F G : k[X]) : Prop :=
  0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 5 * F.natDegree = 7 * D.natDegree
    ∧ 5 * A.natDegree < 2 * D.natDegree
    ∧ 5 * B.natDegree < 3 * D.natDegree
    ∧ 5 * C.natDegree < 4 * D.natDegree
    ∧ 5 * E.natDegree < 6 * D.natDegree
    ∧ 5 * G.natDegree < 8 * D.natDegree


def QuarticRatioConeDG810 (A B C D E F G : k[X]) : Prop :=
  0 < D.natDegree
    ∧ 0 < G.natDegree
    ∧ 5 * G.natDegree = 8 * D.natDegree
    ∧ 5 * A.natDegree < 2 * D.natDegree
    ∧ 5 * B.natDegree < 3 * D.natDegree
    ∧ 5 * C.natDegree < 4 * D.natDegree
    ∧ 5 * E.natDegree < 6 * D.natDegree
    ∧ 5 * F.natDegree < 7 * D.natDegree


def QuarticRatioConeEF810 (A B C D E F G : k[X]) : Prop :=
  0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 6 * F.natDegree = 7 * E.natDegree
    ∧ 3 * A.natDegree < E.natDegree
    ∧ 2 * B.natDegree < E.natDegree
    ∧ 3 * C.natDegree < 2 * E.natDegree
    ∧ 6 * D.natDegree < 5 * E.natDegree
    ∧ 3 * G.natDegree < 4 * E.natDegree


def QuarticRatioConeEG810 (A B C D E F G : k[X]) : Prop :=
  0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * G.natDegree = 4 * E.natDegree
    ∧ 3 * A.natDegree < E.natDegree
    ∧ 2 * B.natDegree < E.natDegree
    ∧ 3 * C.natDegree < 2 * E.natDegree
    ∧ 6 * D.natDegree < 5 * E.natDegree
    ∧ 6 * F.natDegree < 7 * E.natDegree


def QuarticRatioConeFG810 (A B C D E F G : k[X]) : Prop :=
  0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 7 * G.natDegree = 8 * F.natDegree
    ∧ 7 * A.natDegree < 2 * F.natDegree
    ∧ 7 * B.natDegree < 3 * F.natDegree
    ∧ 7 * C.natDegree < 4 * F.natDegree
    ∧ 7 * D.natDegree < 5 * F.natDegree
    ∧ 7 * E.natDegree < 6 * F.natDegree


def QuarticRatioConeABC810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABD810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABE810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeACD810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeACE810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeACF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < F.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeACG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < G.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeADE810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeADF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeADG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeAEF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeAEG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeAFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def QuarticRatioConeBCD810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBCE810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBCF810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < F.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBCG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree


def QuarticRatioConeBDE810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBDF810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBDG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree


def QuarticRatioConeBEF810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBEG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree


def QuarticRatioConeBFG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree


def QuarticRatioConeCDE810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 4 * D.natDegree = 5 * C.natDegree
    ∧ 2 * E.natDegree = 3 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * F.natDegree < 7 * C.natDegree
    ∧ G.natDegree < 2 * C.natDegree


def QuarticRatioConeCDF810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 4 * D.natDegree = 5 * C.natDegree
    ∧ 4 * F.natDegree = 7 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree
    ∧ G.natDegree < 2 * C.natDegree


def QuarticRatioConeCDG810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < G.natDegree
    ∧ 4 * D.natDegree = 5 * C.natDegree
    ∧ G.natDegree = 2 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree
    ∧ 4 * F.natDegree < 7 * C.natDegree


def QuarticRatioConeCEF810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * E.natDegree = 3 * C.natDegree
    ∧ 4 * F.natDegree = 7 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * D.natDegree < 5 * C.natDegree
    ∧ G.natDegree < 2 * C.natDegree


def QuarticRatioConeCEG810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * E.natDegree = 3 * C.natDegree
    ∧ G.natDegree = 2 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * D.natDegree < 5 * C.natDegree
    ∧ 4 * F.natDegree < 7 * C.natDegree


def QuarticRatioConeCFG810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 4 * F.natDegree = 7 * C.natDegree
    ∧ G.natDegree = 2 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * D.natDegree < 5 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree


def QuarticRatioConeDEF810 (A B C D E F G : k[X]) : Prop :=
  0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 5 * E.natDegree = 6 * D.natDegree
    ∧ 5 * F.natDegree = 7 * D.natDegree
    ∧ 5 * A.natDegree < 2 * D.natDegree
    ∧ 5 * B.natDegree < 3 * D.natDegree
    ∧ 5 * C.natDegree < 4 * D.natDegree
    ∧ 5 * G.natDegree < 8 * D.natDegree


def QuarticRatioConeDEG810 (A B C D E F G : k[X]) : Prop :=
  0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 5 * E.natDegree = 6 * D.natDegree
    ∧ 5 * G.natDegree = 8 * D.natDegree
    ∧ 5 * A.natDegree < 2 * D.natDegree
    ∧ 5 * B.natDegree < 3 * D.natDegree
    ∧ 5 * C.natDegree < 4 * D.natDegree
    ∧ 5 * F.natDegree < 7 * D.natDegree


def QuarticRatioConeDFG810 (A B C D E F G : k[X]) : Prop :=
  0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 5 * F.natDegree = 7 * D.natDegree
    ∧ 5 * G.natDegree = 8 * D.natDegree
    ∧ 5 * A.natDegree < 2 * D.natDegree
    ∧ 5 * B.natDegree < 3 * D.natDegree
    ∧ 5 * C.natDegree < 4 * D.natDegree
    ∧ 5 * E.natDegree < 6 * D.natDegree


def QuarticRatioConeEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 6 * F.natDegree = 7 * E.natDegree
    ∧ 3 * G.natDegree = 4 * E.natDegree
    ∧ 3 * A.natDegree < E.natDegree
    ∧ 2 * B.natDegree < E.natDegree
    ∧ 3 * C.natDegree < 2 * E.natDegree
    ∧ 6 * D.natDegree < 5 * E.natDegree


def QuarticRatioConeABCD810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABCE810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABCF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABCG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeABDE810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABDF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABDG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeABEF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABEG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeABFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def QuarticRatioConeACDE810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeACDF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeACDG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < G.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeACEF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeACEG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeACFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def QuarticRatioConeADEF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeADEG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeADFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def QuarticRatioConeAEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree


def QuarticRatioConeBCDE810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBCDF810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBCDG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree


def QuarticRatioConeBCEF810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBCEG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree


def QuarticRatioConeBCFG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree


def QuarticRatioConeBDEF810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBDEG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree


def QuarticRatioConeBDFG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree


def QuarticRatioConeBEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree


def QuarticRatioConeCDEF810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 4 * D.natDegree = 5 * C.natDegree
    ∧ 2 * E.natDegree = 3 * C.natDegree
    ∧ 4 * F.natDegree = 7 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ G.natDegree < 2 * C.natDegree


def QuarticRatioConeCDEG810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 4 * D.natDegree = 5 * C.natDegree
    ∧ 2 * E.natDegree = 3 * C.natDegree
    ∧ G.natDegree = 2 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * F.natDegree < 7 * C.natDegree


def QuarticRatioConeCDFG810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 4 * D.natDegree = 5 * C.natDegree
    ∧ 4 * F.natDegree = 7 * C.natDegree
    ∧ G.natDegree = 2 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 2 * E.natDegree < 3 * C.natDegree


def QuarticRatioConeCEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * E.natDegree = 3 * C.natDegree
    ∧ 4 * F.natDegree = 7 * C.natDegree
    ∧ G.natDegree = 2 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree
    ∧ 4 * D.natDegree < 5 * C.natDegree


def QuarticRatioConeDEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 5 * E.natDegree = 6 * D.natDegree
    ∧ 5 * F.natDegree = 7 * D.natDegree
    ∧ 5 * G.natDegree = 8 * D.natDegree
    ∧ 5 * A.natDegree < 2 * D.natDegree
    ∧ 5 * B.natDegree < 3 * D.natDegree
    ∧ 5 * C.natDegree < 4 * D.natDegree


def QuarticRatioConeABCDE810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABCDF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABCDG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeABCEF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABCEG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeABCFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def QuarticRatioConeABDEF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABDEG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeABDFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def QuarticRatioConeABEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree


def QuarticRatioConeACDEF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeACDEG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeACDFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def QuarticRatioConeACEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree


def QuarticRatioConeADEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree


def QuarticRatioConeBCDEF810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * G.natDegree < 8 * B.natDegree


def QuarticRatioConeBCDEG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * F.natDegree < 7 * B.natDegree


def QuarticRatioConeBCDFG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ E.natDegree < 2 * B.natDegree


def QuarticRatioConeBCEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * D.natDegree < 5 * B.natDegree


def QuarticRatioConeBDEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree
    ∧ 3 * C.natDegree < 4 * B.natDegree


def QuarticRatioConeCDEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 4 * D.natDegree = 5 * C.natDegree
    ∧ 2 * E.natDegree = 3 * C.natDegree
    ∧ 4 * F.natDegree = 7 * C.natDegree
    ∧ G.natDegree = 2 * C.natDegree
    ∧ 2 * A.natDegree < C.natDegree
    ∧ 4 * B.natDegree < 3 * C.natDegree


def QuarticRatioConeABCDEF810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree < 4 * A.natDegree


def QuarticRatioConeABCDEG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * F.natDegree < 7 * A.natDegree


def QuarticRatioConeABCDFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree


def QuarticRatioConeABCEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree


def QuarticRatioConeABDEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree


def QuarticRatioConeACDEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree


def QuarticRatioConeBCDEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 3 * C.natDegree = 4 * B.natDegree
    ∧ 3 * D.natDegree = 5 * B.natDegree
    ∧ E.natDegree = 2 * B.natDegree
    ∧ 3 * F.natDegree = 7 * B.natDegree
    ∧ 3 * G.natDegree = 8 * B.natDegree
    ∧ 3 * A.natDegree < 2 * B.natDegree


def QuarticRatioConeABCDEFG810 (A B C D E F G : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 0 < B.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < D.natDegree
    ∧ 0 < E.natDegree
    ∧ 0 < F.natDegree
    ∧ 0 < G.natDegree
    ∧ 2 * B.natDegree = 3 * A.natDegree
    ∧ C.natDegree = 2 * A.natDegree
    ∧ 2 * D.natDegree = 5 * A.natDegree
    ∧ E.natDegree = 3 * A.natDegree
    ∧ 2 * F.natDegree = 7 * A.natDegree
    ∧ G.natDegree = 4 * A.natDegree


end QuarticCones810

end Max11DegreeRoutes
