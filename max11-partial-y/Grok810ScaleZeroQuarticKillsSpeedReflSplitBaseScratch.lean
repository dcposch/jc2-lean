import Grok810ScaleZeroQuarticDefsScratch
import Max11SpeedReflectDegLibScratch

/-! # Quartic Stage A cone kills (monomial + multi certificates) -/

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

/-! ## Split lemmas, rest bounds, and cone kills -/

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
def muQuarticFaceB810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2
  - (45 / 262144 * l : k) • (A ^ 4 * B)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–42, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoB810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_B_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceB810 A B C D E F G +
        degreeZeroMuQuarticNoB810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceB810, degreeZeroMuQuarticNoB810,
    killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk01,
    killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk02,
    killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk03,
    killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk04,
    killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk05]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticFaceC810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2
  - (45 / 262144 * l : k) • (A ^ 4 * B)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–42, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoC810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_C_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceC810 A B C D E F G +
        degreeZeroMuQuarticNoC810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceC810, degreeZeroMuQuarticNoC810,
    killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk01,
    killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk02,
    killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk03,
    killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk04,
    killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk05]
  all_goals module

set_option maxHeartbeats 64000000 in
def omicronQuarticFaceD810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • D ^ 3

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk01
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

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  + (5 / 16 : k) • (F * G)
  + (135 / 33554432 * l : k) • A ^ 7
  + (225 / 2097152 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (81 / 262144 * l : k) • (A ^ 4 * E)
  - (9 / 65536 * l : k) • (A ^ 3 * B * D)
  + (99 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  - (45 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–50, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 51–60, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk06 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 61–70, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk07 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 71–80, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk08 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 81–90, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk09 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 91–100, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk10 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 101–101, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk11 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronQuarticNoD810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk11
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk10
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk09
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk08
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk07
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk06
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk05
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk04
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk03
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk02
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronQuartic810_eq_D_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceD810 A B C D E F G +
        degreeZeroOmicronQuarticNoD810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceD810, degreeZeroOmicronQuarticNoD810,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk01,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk02,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk03,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk04,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk05,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk06,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk07,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk08,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk09,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk10,
    killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk11]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticFaceE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk01
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
  - (45 / 262144 * l : k) • (A ^ 4 * B)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–42, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_E_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceE810 A B C D E F G +
        degreeZeroMuQuarticNoE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceE810, degreeZeroMuQuarticNoE810,
    killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk01,
    killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk02,
    killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk03,
    killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk04,
    killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk05]
  all_goals module

set_option maxHeartbeats 64000000 in
def xiQuarticFaceF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk01
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

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  - (45 / 262144 * l : k) • (A ^ 4 * D)
  + (9 / 16384 * l : k) • (A ^ 3 * B * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 3)
  - (9 / 8192 * l : k) • (A ^ 3 * F)
  + (9 / 4096 * l : k) • (A ^ 2 * B * E)
  - (9 / 8192 * l : k) • (A ^ 2 * C * D)
  + (171 / 8192 * l : k) • (A * B ^ 2 * D)
  + (9 / 1024 * l : k) • (A * B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–50, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 51–60, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk06 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
def degreeZeroXiQuarticNoF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk06
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk05
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk04
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk03
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk02
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_F_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceF810 A B C D E F G +
        degreeZeroXiQuarticNoF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceF810, degreeZeroXiQuarticNoF810,
    killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk01,
    killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk02,
    killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk03,
    killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk04,
    killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk05,
    killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk06]
  all_goals module

set_option maxHeartbeats 64000000 in
def piQuarticFaceG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
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

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–50, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)

set_option maxHeartbeats 64000000 in
/-- Original terms 51–60, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk06 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 61–70, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk07 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)

set_option maxHeartbeats 64000000 in
/-- Original terms 71–80, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk08 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Original terms 81–90, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk09 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 91–94, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk10 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 64000000 in
def degreeZeroPiQuarticNoG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk10
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk09
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk08
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk07
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk06
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk05
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk04
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk03
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk02
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPiQuartic810_eq_G_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceG810 A B C D E F G +
        degreeZeroPiQuarticNoG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceG810, degreeZeroPiQuarticNoG810,
    killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk01,
    killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk02,
    killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk03,
    killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk04,
    killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk05,
    killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk06,
    killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk07,
    killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk08,
    killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk09,
    killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk10]
  all_goals module

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceAB810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–34, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoAB810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_AB_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceAB810 A B C D E F G +
        degreeZeroKappaQuarticNoAB810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceAB810, degreeZeroKappaQuarticNoAB810,
    killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk01,
    killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk02,
    killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk03,
    killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk04]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticFaceAC810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoAC810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_AC_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAC810 A B C D E F G +
        degreeZeroMuQuarticNoAC810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_C_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def muQuarticFaceAD810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2
  - (45 / 262144 * l : k) • (A ^ 4 * B)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–42, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoAD810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_AD_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAD810 A B C D E F G +
        degreeZeroMuQuarticNoAD810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceAD810, degreeZeroMuQuarticNoAD810,
    killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk01,
    killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk02,
    killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk03,
    killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk04,
    killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk05]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticFaceAE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoAE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_AE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAE810 A B C D E F G +
        degreeZeroMuQuarticNoAE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_E_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def xiQuarticFaceAF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroXiQuarticNoAF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk06
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk05
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk04
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk03
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk02
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_AF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceAF810 A B C D E F G +
        degreeZeroXiQuarticNoAF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroXiQuartic810_eq_F_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def piQuarticFaceAG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroPiQuarticNoAG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk10
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk09
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk08
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk07
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk06
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk05
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk04
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk03
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk02
    (killsBaseSpeedT_degreeZeroPiQuarticNoG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPiQuartic810_eq_AG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceAG810 A B C D E F G +
        degreeZeroPiQuarticNoAG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroPiQuartic810_eq_G_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceBC810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–34, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoBC810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_BC_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBC810 A B C D E F G +
        degreeZeroKappaQuarticNoBC810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBC810, degreeZeroKappaQuarticNoBC810,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk01,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk02,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk03,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk04]
  all_goals module

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceBD810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–34, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoBD810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_BD_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBD810 A B C D E F G +
        degreeZeroKappaQuarticNoBD810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBD810, degreeZeroKappaQuarticNoBD810,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk01,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk02,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk03,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk04]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticFaceBF810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoBF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_BF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBF810 A B C D E F G +
        degreeZeroMuQuarticNoBF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_B_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceBG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–34, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoBG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_BG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBG810 A B C D E F G +
        degreeZeroKappaQuarticNoBG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBG810, degreeZeroKappaQuarticNoBG810,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk01,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk02,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk03,
    killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk04]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticFaceCD810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoCD810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoC810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_CD_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceCD810 A B C D E F G +
        degreeZeroMuQuarticNoCD810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_C_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def xiQuarticFaceCE810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk01
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
  - (15 / 128 : k) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–50, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 51–60, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk06 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
def degreeZeroXiQuarticNoCE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk06
    (killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk05
    (killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk04
    (killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk03
    (killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk02
    (killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_CE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceCE810 A B C D E F G +
        degreeZeroXiQuarticNoCE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceCE810, degreeZeroXiQuarticNoCE810,
    killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk01,
    killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk02,
    killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk03,
    killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk04,
    killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk05,
    killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk06]
  all_goals module

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceCF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–34, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoCF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_CF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCF810 A B C D E F G +
        degreeZeroKappaQuarticNoCF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCF810, degreeZeroKappaQuarticNoCF810,
    killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01,
    killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02,
    killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03,
    killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04]
  all_goals module

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceDE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–34, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoDE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_DE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceDE810 A B C D E F G +
        degreeZeroKappaQuarticNoDE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceDE810, degreeZeroKappaQuarticNoDE810,
    killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01,
    killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02,
    killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03,
    killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticFaceDF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk01
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
  + (5 / 32 : k) • E ^ 2
  - (45 / 262144 * l : k) • (A ^ 4 * B)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–42, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoDF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_DF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceDF810 A B C D E F G +
        degreeZeroMuQuarticNoDF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceDF810, degreeZeroMuQuarticNoDF810,
    killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk01,
    killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk02,
    killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk03,
    killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk04,
    killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk05]
  all_goals module

set_option maxHeartbeats 64000000 in
def nuQuarticFaceDG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk01
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

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)
  + (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 4096 * l : k) • (A ^ 3 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–50, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 51–58, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk06 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 2 * epsilon : k) • F
  + (1 / 512 * zeta : k) • A ^ 3
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  - (1 / 32 * eta : k) • (A * B)
  + (1 / 4 * eta : k) • D
  + (1 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
def degreeZeroNuQuarticNoDG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk06
    (killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk05
    (killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk04
    (killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk03
    (killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk02
    (killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_DG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceDG810 A B C D E F G +
        degreeZeroNuQuarticNoDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceDG810, degreeZeroNuQuarticNoDG810,
    killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk01,
    killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk02,
    killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk03,
    killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk04,
    killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk05,
    killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk06]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticFaceEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_EF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceEF810 A B C D E F G +
        degreeZeroMuQuarticNoEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_E_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def muQuarticFaceEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_EG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceEG810 A B C D E F G +
        degreeZeroMuQuarticNoEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_E_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def xiQuarticFaceFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroXiQuarticNoFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk06
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk05
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk04
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk03
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk02
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_FG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceFG810 A B C D E F G +
        degreeZeroXiQuarticNoFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroXiQuartic810_eq_F_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceABE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoABE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ABE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABE810 A B C D E F G +
        degreeZeroKappaQuarticNoABE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_AB_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceABF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoABF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ABF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABF810 A B C D E F G +
        degreeZeroKappaQuarticNoABF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_AB_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def muQuarticFaceABG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoABG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_ABG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceABG810 A B C D E F G +
        degreeZeroMuQuarticNoABG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_B_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def nuQuarticFaceACD810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk01
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

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–50, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 51–58, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk06 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 2 * epsilon : k) • F
  + (1 / 512 * zeta : k) • A ^ 3
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  - (1 / 32 * eta : k) • (A * B)
  + (1 / 4 * eta : k) • D
  + (1 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
def degreeZeroNuQuarticNoACD810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk06
    (killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk05
    (killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk04
    (killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk03
    (killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk02
    (killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_ACD_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceACD810 A B C D E F G +
        degreeZeroNuQuarticNoACD810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceACD810, degreeZeroNuQuarticNoACD810,
    killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk01,
    killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk02,
    killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk03,
    killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk04,
    killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk05,
    killsBaseSpeedT_degreeZeroNuQuarticNoACD810_chunk06]
  all_goals module

set_option maxHeartbeats 64000000 in
def xiQuarticFaceACE810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
def degreeZeroXiQuarticNoACE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk06
    (killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk05
    (killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk04
    (killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk03
    (killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk02
    (killsBaseSpeedT_degreeZeroXiQuarticNoCE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_ACE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceACE810 A B C D E F G +
        degreeZeroXiQuarticNoACE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroXiQuartic810_eq_CE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceACF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoACF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ACF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACF810 A B C D E F G +
        degreeZeroKappaQuarticNoACF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceADE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoADE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ADE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceADE810 A B C D E F G +
        degreeZeroKappaQuarticNoADE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def omicronQuarticFaceADF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • D ^ 3

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronQuarticNoADF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk11
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk10
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk09
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk08
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk07
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk06
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk05
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk04
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk03
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk02
    (killsBaseSpeedT_degreeZeroOmicronQuarticNoD810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronQuartic810_eq_ADF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceADF810 A B C D E F G +
        degreeZeroOmicronQuarticNoADF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroOmicronQuartic810_eq_D_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def muQuarticFaceADG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoADG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoAD810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_ADG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceADG810 A B C D E F G +
        degreeZeroMuQuarticNoADG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_AD_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def muQuarticFaceAEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoAEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_AEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAEF810 A B C D E F G +
        degreeZeroMuQuarticNoAEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_E_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def muQuarticFaceAEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoAEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_AEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAEG810 A B C D E F G +
        degreeZeroMuQuarticNoAEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_E_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def xiQuarticFaceAFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroXiQuarticNoAFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk06
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk05
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk04
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk03
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk02
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_AFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceAFG810 A B C D E F G +
        degreeZeroXiQuarticNoAFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroXiQuartic810_eq_F_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceBCE810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoBCE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBC810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_BCE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBCE810 A B C D E F G +
        degreeZeroKappaQuarticNoBCE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_BC_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def nuQuarticFaceBCG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–50, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 51–58, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk06 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 2 * epsilon : k) • F
  + (1 / 512 * zeta : k) • A ^ 3
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  - (1 / 32 * eta : k) • (A * B)
  + (1 / 4 * eta : k) • D
  + (1 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
def degreeZeroNuQuarticNoBCG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk06
    (killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk05
    (killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk04
    (killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk03
    (killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk02
    (killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_BCG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBCG810 A B C D E F G +
        degreeZeroNuQuarticNoBCG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBCG810, degreeZeroNuQuarticNoBCG810,
    killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk01,
    killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk02,
    killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk03,
    killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk04,
    killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk05,
    killsBaseSpeedT_degreeZeroNuQuarticNoBCG810_chunk06]
  all_goals module

set_option maxHeartbeats 64000000 in
def nuQuarticFaceBDE810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk01
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
  - (15 / 128 : k) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–50, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 51–58, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk06 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 2 * epsilon : k) • F
  + (1 / 512 * zeta : k) • A ^ 3
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  - (1 / 32 * eta : k) • (A * B)
  + (1 / 4 * eta : k) • D
  + (1 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
def degreeZeroNuQuarticNoBDE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk06
    (killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk05
    (killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk04
    (killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk03
    (killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk02
    (killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_BDE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBDE810 A B C D E F G +
        degreeZeroNuQuarticNoBDE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBDE810, degreeZeroNuQuarticNoBDE810,
    killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk01,
    killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk02,
    killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk03,
    killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk04,
    killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk05,
    killsBaseSpeedT_degreeZeroNuQuarticNoBDE810_chunk06]
  all_goals module

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceBDF810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoBDF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBD810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_BDF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBDF810 A B C D E F G +
        degreeZeroKappaQuarticNoBDF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_BD_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def muQuarticFaceBDG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoBDG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoB810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_BDG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBDG810 A B C D E F G +
        degreeZeroMuQuarticNoBDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_B_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def xiQuarticFaceBEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroXiQuarticNoBEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk06
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk05
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk04
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk03
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk02
    (killsBaseSpeedT_degreeZeroXiQuarticNoF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_BEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceBEF810 A B C D E F G +
        degreeZeroXiQuarticNoBEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroXiQuartic810_eq_F_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceBEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoBEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_BEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBEG810 A B C D E F G +
        degreeZeroKappaQuarticNoBEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_BG_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceBFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoBFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_BFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBFG810 A B C D E F G +
        degreeZeroKappaQuarticNoBFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_BG_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceCDE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoCDE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_CDE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCDE810 A B C D E F G +
        degreeZeroKappaQuarticNoCDE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceCDF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoCDF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_CDF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCDF810 A B C D E F G +
        degreeZeroKappaQuarticNoCDF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def xiQuarticFaceCDG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Original terms 1–10, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk01
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

set_option maxHeartbeats 64000000 in
/-- Original terms 11–20, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 21–30, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 31–40, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 41–50, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
/-- Original terms 51–60, preserving signs and association. -/
private abbrev killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk06 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
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

set_option maxHeartbeats 64000000 in
def degreeZeroXiQuarticNoCDG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk06
    (killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk05
    (killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk04
    (killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk03
    (killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk02
    (killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_CDG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceCDG810 A B C D E F G +
        degreeZeroXiQuarticNoCDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceCDG810, degreeZeroXiQuarticNoCDG810,
    killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk01,
    killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk02,
    killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk03,
    killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk04,
    killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk05,
    killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk06]
  all_goals module

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceCEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoCEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_CEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCEF810 A B C D E F G +
        degreeZeroKappaQuarticNoCEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceCFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoCFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_CFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCFG810 A B C D E F G +
        degreeZeroKappaQuarticNoCFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceDEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_DEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceDEF810 A B C D E F G +
        degreeZeroKappaQuarticNoDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceDEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_DEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceDEG810 A B C D E F G +
        degreeZeroKappaQuarticNoDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def muQuarticFaceDFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoDF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_DFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceDFG810 A B C D E F G +
        degreeZeroMuQuarticNoDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_DF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def muQuarticFaceEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_EFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceEFG810 A B C D E F G +
        degreeZeroMuQuarticNoEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_E_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceABEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoABEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoAB810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ABEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABEF810 A B C D E F G +
        degreeZeroKappaQuarticNoABEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_AB_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceACDE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoACDE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ACDE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDE810 A B C D E F G +
        degreeZeroKappaQuarticNoACDE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceACDF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoACDF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ACDF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDF810 A B C D E F G +
        degreeZeroKappaQuarticNoACDF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def xiQuarticFaceACDG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
def degreeZeroXiQuarticNoACDG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk06
    (killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk05
    (killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk04
    (killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk03
    (killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk02
    (killsBaseSpeedT_degreeZeroXiQuarticNoCDG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_ACDG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceACDG810 A B C D E F G +
        degreeZeroXiQuarticNoACDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroXiQuartic810_eq_CDG_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceACEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoACEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ACEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACEF810 A B C D E F G +
        degreeZeroKappaQuarticNoACEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceACFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoACFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ACFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACFG810 A B C D E F G +
        degreeZeroKappaQuarticNoACFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceADEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoADEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ADEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceADEF810 A B C D E F G +
        degreeZeroKappaQuarticNoADEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceADEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoADEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ADEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceADEG810 A B C D E F G +
        degreeZeroKappaQuarticNoADEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def nuQuarticFaceADFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
def degreeZeroNuQuarticNoADFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk06
    (killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk05
    (killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk04
    (killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk03
    (killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk02
    (killsBaseSpeedT_degreeZeroNuQuarticNoDG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_ADFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceADFG810 A B C D E F G +
        degreeZeroNuQuarticNoADFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroNuQuartic810_eq_DG_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def muQuarticFaceAEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoAEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk05
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk04
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk03
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk02
    (killsBaseSpeedT_degreeZeroMuQuarticNoE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_AEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAEFG810 A B C D E F G +
        degreeZeroMuQuarticNoAEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroMuQuartic810_eq_E_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceBEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoBEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoBG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_BEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoBEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_BG_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_CDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCDEG810 A B C D E F G +
        degreeZeroKappaQuarticNoCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_CDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCDFG810 A B C D E F G +
        degreeZeroKappaQuarticNoCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_CEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_DEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceDEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceACDEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoACDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ACDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDEG810 A B C D E F G +
        degreeZeroKappaQuarticNoACDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceACDFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoACDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ACDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDFG810 A B C D E F G +
        degreeZeroKappaQuarticNoACDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceACEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoACEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoCF810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ACEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoACEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_CF_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceADEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoADEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk04
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk03
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk02
    (killsBaseSpeedT_degreeZeroKappaQuarticNoDE810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ADEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceADEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoADEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  exact degreeZeroKappaQuartic810_eq_DE_add_rest l beta gamma delta epsilon zeta eta theta A B C D E F G

end QuarticKills810

end Max11DegreeRoutes

