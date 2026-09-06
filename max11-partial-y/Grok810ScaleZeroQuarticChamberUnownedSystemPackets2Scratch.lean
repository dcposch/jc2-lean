import Grok810ScaleZeroQuarticChamberN7LadderScratch
import Grok810ScaleZeroQuarticChamberInfraN2Scratch
import Grok810ScaleZeroQuarticChamberInfraN3Scratch
import Grok810ScaleZeroQuarticChamberInfraN4Scratch
import Grok810ScaleZeroQuarticChamberInfraN5Scratch
import Grok810ScaleZeroQuarticChamberInfraN6Scratch
import Grok810ScaleZeroQuarticChamberInfraN7Scratch
import Grok810ScaleZeroQuarticChamberInfraOmicronScratch
import Grok810ScaleZeroQuarticChamberInfraPrimitiveScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberN7BandsScratch

/-! # UnownedSystem face packets, part 2/2

Face, load-free rest, packet split identity, combined rest and
carrier split identity for the packets the kills use.
Untracked working note.
-/

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

section QuarticChamberUnownedSystemPackets2810

set_option maxHeartbeats 64000000 in
/-- Face of `N₃` on unowned packet 6001 (2 monomial, top degree `A.natDegree + D.natDegree + G.natDegree`). -/
def n3QuarticChamberFace6001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 256 : k)) • (A * D * G)
  - (15 / 256 : k) • (A * E * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₃` off packet 6001 (17 monomials). -/
def n3QuarticChamberRestLF6001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 8192 : k)) • (A ^ 2 * B ^ 2 * D)
  - (175 / 8192 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (65 / 2048 : k) • (A * B ^ 2 * F)
  + (45 / 1024 : k) • (A * B * C * E)
  + (85 / 2048 : k) • (A * B * D ^ 2)
  + (45 / 2048 : k) • (A * C ^ 2 * D)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem n3QuarticLoadFree810_eq_face6001_add_rest
    (A B C D E F G : k[X]) :
    n3QuarticLoadFree810 A B C D E F G =
      n3QuarticChamberFace6001810 A B C D E F G + n3QuarticChamberRestLF6001810 A B C D E F G := by
  simp only [n3QuarticLoadFree810, n3QuarticChamberFace6001810, n3QuarticChamberRestLF6001810]
  module

set_option maxHeartbeats 64000000 in
def n3QuarticChamberRest6001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n3QuarticChamberRestLF6001810 A B C D E F G +
    n3QuarticColumnL1810 l A B C D E F G +
    n3QuarticColumnL2810 l A B C D E F G +
    n3QuarticColumnBeta810 beta A B C D E F G +
    n3QuarticColumnGamma810 gamma A B C D E F G +
    n3QuarticColumnDelta810 delta A B C D E F G +
    n3QuarticColumnEpsilon810 epsilon A B C D E F G +
    n3QuarticColumnZeta810 zeta A B C D E F G +
    n3QuarticColumnEta810 eta A B C D E F G +
    n3QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN3Quartic810_eq_face6001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n3QuarticChamberFace6001810 A B C D E F G +
        n3QuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN3Quartic810_eq_chamberSplit,
    n3QuarticLoadFree810_eq_face6001_add_rest]
  simp only [n3QuarticChamberRest6001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₄` on unowned packet 6001 (2 monomial, top degree `2 * A.natDegree + D.natDegree + G.natDegree`). -/
def n4QuarticChamberFace6001810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 256 : k) • (A ^ 2 * D * G)
  + (5 / 256 : k) • (A ^ 2 * E * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₄` off packet 6001 (31 monomials). -/
def n4QuarticChamberRestLF6001810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 8192 : k) • (A ^ 3 * B ^ 2 * D)
  + (155 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (107 / 8192 : k) • (A * B ^ 5)
  - (55 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  - (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (95 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (45 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 512 : k) • (A * B ^ 2 * C * D)
  - (15 / 256 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (5 / 32 : k) • (A * B * C * G)
  + (5 / 16 : k) • (A * B * D * F)
  + (5 / 32 : k) • (A * B * E ^ 2)
  + (5 / 64 : k) • (A * C ^ 2 * F)
  + (5 / 16 : k) • (A * C * D * E)
  + (5 / 64 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 8 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem n4QuarticLoadFree810_eq_face6001_add_rest
    (A B C D E F G : k[X]) :
    n4QuarticLoadFree810 A B C D E F G =
      n4QuarticChamberFace6001810 A B C D E F G + n4QuarticChamberRestLF6001810 A B C D E F G := by
  simp only [n4QuarticLoadFree810, n4QuarticChamberFace6001810, n4QuarticChamberRestLF6001810]
  module

set_option maxHeartbeats 64000000 in
def n4QuarticChamberRest6001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n4QuarticChamberRestLF6001810 A B C D E F G +
    n4QuarticColumnL1810 l A B C D E F G +
    n4QuarticColumnL2810 l A B C D E F G +
    n4QuarticColumnBeta1810 beta A B C D E F G +
    n4QuarticColumnBeta2810 beta A B C D E F G +
    n4QuarticColumnGamma810 gamma A B C D E F G +
    n4QuarticColumnDelta810 delta A B C D E F G +
    n4QuarticColumnEpsilon810 epsilon A B C D E F G +
    n4QuarticColumnZeta810 zeta A B C D E F G +
    n4QuarticColumnEta810 eta A B C D E F G +
    n4QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN4Quartic810_eq_face6001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n4QuarticChamberFace6001810 A B C D E F G +
        n4QuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN4Quartic810_eq_chamberSplit,
    n4QuarticLoadFree810_eq_face6001_add_rest]
  simp only [n4QuarticChamberRest6001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 6004 (3 monomial, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace6004810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6004 (3 monomials). -/
def kappaQuarticChamberRestLF6004810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6004_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6004810 A B C D E F G + kappaQuarticChamberRestLF6004810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6004810, kappaQuarticChamberRestLF6004810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest6004810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF6004810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face6004_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace6004810 A B C D E F G +
        kappaQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face6004_add_rest]
  simp only [kappaQuarticChamberRest6004810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on unowned packet 6004 (5 monomial, top degree `A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def nuQuarticChamberFace6004810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 6004 (8 monomials). -/
def nuQuarticChamberRestLF6004810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * C * F)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticLoadFree810_eq_face6004_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace6004810 A B C D E F G + nuQuarticChamberRestLF6004810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace6004810, nuQuarticChamberRestLF6004810]
  module

set_option maxHeartbeats 64000000 in
def nuQuarticChamberRest6004810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  nuQuarticChamberRestLF6004810 A B C D E F G +
    nuQuarticColumnL810 l A B C D E F G +
    nuQuarticColumnBeta810 beta A B C D E F G +
    nuQuarticColumnGamma810 gamma A B C D E F G +
    nuQuarticColumnDelta810 delta A B C D E F G +
    nuQuarticColumnEpsilon810 epsilon A B C D E F G +
    nuQuarticColumnZeta810 zeta A B C D E F G +
    nuQuarticColumnEta810 eta A B C D E F G +
    nuQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_face6004_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticChamberFace6004810 A B C D E F G +
        nuQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroNuQuartic810_eq_chamberSplit,
    nuQuarticLoadFree810_eq_face6004_add_rest]
  simp only [nuQuarticChamberRest6004810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 6002 (4 monomial, top degree `A.natDegree + B.natDegree + C.natDegree + D.natDegree`). -/
def xiQuarticChamberFace6002810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 6002 (9 monomials). -/
def xiQuarticChamberRestLF6002810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face6002_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace6002810 A B C D E F G + xiQuarticChamberRestLF6002810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace6002810, xiQuarticChamberRestLF6002810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest6002810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF6002810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face6002_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace6002810 A B C D E F G +
        xiQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face6002_add_rest]
  simp only [xiQuarticChamberRest6002810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ο` on unowned packet 6004 (5 monomial, top degree `2 * A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def omicronQuarticChamberFace6004810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  - (5 / 128 : k) • (A * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ο` off packet 6004 (19 monomials). -/
def omicronQuarticChamberRestLF6004810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * C * F)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticLoadFree810_eq_face6004_add_rest
    (A B C D E F G : k[X]) :
    omicronQuarticLoadFree810 A B C D E F G =
      omicronQuarticChamberFace6004810 A B C D E F G + omicronQuarticChamberRestLF6004810 A B C D E F G := by
  simp only [omicronQuarticLoadFree810, omicronQuarticChamberFace6004810, omicronQuarticChamberRestLF6004810]
  module

set_option maxHeartbeats 64000000 in
def omicronQuarticChamberRest6004810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  omicronQuarticChamberRestLF6004810 A B C D E F G +
    omicronQuarticColumnL1810 l A B C D E F G +
    omicronQuarticColumnL2810 l A B C D E F G +
    omicronQuarticColumnBeta810 beta A B C D E F G +
    omicronQuarticColumnGamma810 gamma A B C D E F G +
    omicronQuarticColumnDelta810 delta A B C D E F G +
    omicronQuarticColumnEpsilon810 epsilon A B C D E F G +
    omicronQuarticColumnZeta810 zeta A B C D E F G +
    omicronQuarticColumnEta810 eta A B C D E F G +
    omicronQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronQuartic810_eq_face6004_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticChamberFace6004810 A B C D E F G +
        omicronQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroOmicronQuartic810_eq_chamberSplit,
    omicronQuarticLoadFree810_eq_face6004_add_rest]
  simp only [omicronQuarticChamberRest6004810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `Π` on unowned packet 6004 (5 monomial, top degree `3 * A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def primitiveQuarticChamberFace6004810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (5 / 256 : k) • (A ^ 2 * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `Π` off packet 6004 (32 monomials). -/
def primitiveQuarticChamberRestLF6004810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
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

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticLoadFree810_eq_face6004_add_rest
    (A B C D E F G : k[X]) :
    primitiveQuarticLoadFree810 A B C D E F G =
      primitiveQuarticChamberFace6004810 A B C D E F G + primitiveQuarticChamberRestLF6004810 A B C D E F G := by
  simp only [primitiveQuarticLoadFree810, primitiveQuarticChamberFace6004810, primitiveQuarticChamberRestLF6004810]
  module

set_option maxHeartbeats 64000000 in
def primitiveQuarticChamberRest6004810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  primitiveQuarticChamberRestLF6004810 A B C D E F G +
    primitiveQuarticColumnL1810 l A B C D E F G +
    primitiveQuarticColumnL2810 l A B C D E F G +
    primitiveQuarticColumnBeta810 beta A B C D E F G +
    primitiveQuarticColumnGamma810 gamma A B C D E F G +
    primitiveQuarticColumnDelta810 delta A B C D E F G +
    primitiveQuarticColumnEpsilon810 epsilon A B C D E F G +
    primitiveQuarticColumnZeta810 zeta A B C D E F G +
    primitiveQuarticColumnEta810 eta A B C D E F G +
    primitiveQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuartic810_eq_face6004_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticChamberFace6004810 A B C D E F G +
        primitiveQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPrimitiveQuartic810_eq_chamberSplit,
    primitiveQuarticLoadFree810_eq_face6004_add_rest]
  simp only [primitiveQuarticChamberRest6004810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 6005 (4 monomial, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace6005810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6005 (2 monomials). -/
def kappaQuarticChamberRestLF6005810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6005_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6005810 A B C D E F G + kappaQuarticChamberRestLF6005810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6005810, kappaQuarticChamberRestLF6005810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest6005810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF6005810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face6005_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace6005810 A B C D E F G +
        kappaQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face6005_add_rest]
  simp only [kappaQuarticChamberRest6005810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 6005 (4 monomial, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace6005810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 6005 (6 monomials). -/
def muQuarticChamberRestLF6005810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face6005_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace6005810 A B C D E F G + muQuarticChamberRestLF6005810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace6005810, muQuarticChamberRestLF6005810]
  module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest6005810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF6005810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face6005_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace6005810 A B C D E F G +
        muQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face6005_add_rest]
  simp only [muQuarticChamberRest6005810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on unowned packet 6005 (4 monomial, top degree `2 * A.natDegree + 3 * B.natDegree`). -/
def nuQuarticChamberFace6005810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 6005 (9 monomials). -/
def nuQuarticChamberRestLF6005810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticLoadFree810_eq_face6005_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace6005810 A B C D E F G + nuQuarticChamberRestLF6005810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace6005810, nuQuarticChamberRestLF6005810]
  module

set_option maxHeartbeats 64000000 in
def nuQuarticChamberRest6005810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  nuQuarticChamberRestLF6005810 A B C D E F G +
    nuQuarticColumnL810 l A B C D E F G +
    nuQuarticColumnBeta810 beta A B C D E F G +
    nuQuarticColumnGamma810 gamma A B C D E F G +
    nuQuarticColumnDelta810 delta A B C D E F G +
    nuQuarticColumnEpsilon810 epsilon A B C D E F G +
    nuQuarticColumnZeta810 zeta A B C D E F G +
    nuQuarticColumnEta810 eta A B C D E F G +
    nuQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_face6005_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticChamberFace6005810 A B C D E F G +
        nuQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroNuQuartic810_eq_chamberSplit,
    nuQuarticLoadFree810_eq_face6005_add_rest]
  simp only [nuQuarticChamberRest6005810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 6003 (5 monomial, top degree `A.natDegree + 4 * B.natDegree`). -/
def xiQuarticChamberFace6003810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 6003 (8 monomials). -/
def xiQuarticChamberRestLF6003810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face6003_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace6003810 A B C D E F G + xiQuarticChamberRestLF6003810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace6003810, xiQuarticChamberRestLF6003810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest6003810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF6003810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face6003_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace6003810 A B C D E F G +
        xiQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face6003_add_rest]
  simp only [xiQuarticChamberRest6003810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ο` on unowned packet 6005 (4 monomial, top degree `3 * A.natDegree + 3 * B.natDegree`). -/
def omicronQuarticChamberFace6005810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ο` off packet 6005 (20 monomials). -/
def omicronQuarticChamberRestLF6005810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 16384 : k)) • (A ^ 2 * B ^ 2 * D)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
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

set_option maxHeartbeats 64000000 in
theorem omicronQuarticLoadFree810_eq_face6005_add_rest
    (A B C D E F G : k[X]) :
    omicronQuarticLoadFree810 A B C D E F G =
      omicronQuarticChamberFace6005810 A B C D E F G + omicronQuarticChamberRestLF6005810 A B C D E F G := by
  simp only [omicronQuarticLoadFree810, omicronQuarticChamberFace6005810, omicronQuarticChamberRestLF6005810]
  module

set_option maxHeartbeats 64000000 in
def omicronQuarticChamberRest6005810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  omicronQuarticChamberRestLF6005810 A B C D E F G +
    omicronQuarticColumnL1810 l A B C D E F G +
    omicronQuarticColumnL2810 l A B C D E F G +
    omicronQuarticColumnBeta810 beta A B C D E F G +
    omicronQuarticColumnGamma810 gamma A B C D E F G +
    omicronQuarticColumnDelta810 delta A B C D E F G +
    omicronQuarticColumnEpsilon810 epsilon A B C D E F G +
    omicronQuarticColumnZeta810 zeta A B C D E F G +
    omicronQuarticColumnEta810 eta A B C D E F G +
    omicronQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronQuartic810_eq_face6005_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticChamberFace6005810 A B C D E F G +
        omicronQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroOmicronQuartic810_eq_chamberSplit,
    omicronQuarticLoadFree810_eq_face6005_add_rest]
  simp only [omicronQuarticChamberRest6005810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 6007 (8 monomial, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace6007810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 6007 (13 monomials). -/
def piQuarticChamberRestLF6007810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face6007_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace6007810 A B C D E F G + piQuarticChamberRestLF6007810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace6007810, piQuarticChamberRestLF6007810]
  module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest6007810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF6007810 A B C D E F G +
    piQuarticColumnL1810 l A B C D E F G +
    piQuarticColumnL2810 l A B C D E F G +
    piQuarticColumnBeta810 beta A B C D E F G +
    piQuarticColumnGamma810 gamma A B C D E F G +
    piQuarticColumnDelta810 delta A B C D E F G +
    piQuarticColumnEpsilon810 epsilon A B C D E F G +
    piQuarticColumnZeta810 zeta A B C D E F G +
    piQuarticColumnEta810 eta A B C D E F G +
    piQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPiQuartic810_eq_face6007_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace6007810 A B C D E F G +
        piQuarticChamberRest6007810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face6007_add_rest]
  simp only [piQuarticChamberRest6007810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `Π` on unowned packet 6005 (4 monomial, top degree `4 * A.natDegree + 3 * B.natDegree`). -/
def primitiveQuarticChamberFace6005810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `Π` off packet 6005 (33 monomials). -/
def primitiveQuarticChamberRestLF6005810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 16384 : k)) • (A ^ 3 * B ^ 2 * D)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
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

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticLoadFree810_eq_face6005_add_rest
    (A B C D E F G : k[X]) :
    primitiveQuarticLoadFree810 A B C D E F G =
      primitiveQuarticChamberFace6005810 A B C D E F G + primitiveQuarticChamberRestLF6005810 A B C D E F G := by
  simp only [primitiveQuarticLoadFree810, primitiveQuarticChamberFace6005810, primitiveQuarticChamberRestLF6005810]
  module

set_option maxHeartbeats 64000000 in
def primitiveQuarticChamberRest6005810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  primitiveQuarticChamberRestLF6005810 A B C D E F G +
    primitiveQuarticColumnL1810 l A B C D E F G +
    primitiveQuarticColumnL2810 l A B C D E F G +
    primitiveQuarticColumnBeta810 beta A B C D E F G +
    primitiveQuarticColumnGamma810 gamma A B C D E F G +
    primitiveQuarticColumnDelta810 delta A B C D E F G +
    primitiveQuarticColumnEpsilon810 epsilon A B C D E F G +
    primitiveQuarticColumnZeta810 zeta A B C D E F G +
    primitiveQuarticColumnEta810 eta A B C D E F G +
    primitiveQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuartic810_eq_face6005_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticChamberFace6005810 A B C D E F G +
        primitiveQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPrimitiveQuartic810_eq_chamberSplit,
    primitiveQuarticLoadFree810_eq_face6005_add_rest]
  simp only [primitiveQuarticChamberRest6005810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 6006 (3 monomial, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace6006810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6006 (3 monomials). -/
def kappaQuarticChamberRestLF6006810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6006_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6006810 A B C D E F G + kappaQuarticChamberRestLF6006810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6006810, kappaQuarticChamberRestLF6006810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest6006810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF6006810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face6006_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace6006810 A B C D E F G +
        kappaQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face6006_add_rest]
  simp only [kappaQuarticChamberRest6006810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on unowned packet 6006 (5 monomial, top degree `A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def nuQuarticChamberFace6006810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 6006 (8 monomials). -/
def nuQuarticChamberRestLF6006810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticLoadFree810_eq_face6006_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace6006810 A B C D E F G + nuQuarticChamberRestLF6006810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace6006810, nuQuarticChamberRestLF6006810]
  module

set_option maxHeartbeats 64000000 in
def nuQuarticChamberRest6006810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  nuQuarticChamberRestLF6006810 A B C D E F G +
    nuQuarticColumnL810 l A B C D E F G +
    nuQuarticColumnBeta810 beta A B C D E F G +
    nuQuarticColumnGamma810 gamma A B C D E F G +
    nuQuarticColumnDelta810 delta A B C D E F G +
    nuQuarticColumnEpsilon810 epsilon A B C D E F G +
    nuQuarticColumnZeta810 zeta A B C D E F G +
    nuQuarticColumnEta810 eta A B C D E F G +
    nuQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_face6006_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticChamberFace6006810 A B C D E F G +
        nuQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroNuQuartic810_eq_chamberSplit,
    nuQuarticLoadFree810_eq_face6006_add_rest]
  simp only [nuQuarticChamberRest6006810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 6004 (3 monomial, top degree `A.natDegree + B.natDegree + C.natDegree + D.natDegree`). -/
def xiQuarticChamberFace6004810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)
  - (5 / 64 : k) • (A * D * F)
  - (15 / 128 : k) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 6004 (10 monomials). -/
def xiQuarticChamberRestLF6004810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face6004_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace6004810 A B C D E F G + xiQuarticChamberRestLF6004810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace6004810, xiQuarticChamberRestLF6004810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest6004810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF6004810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face6004_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace6004810 A B C D E F G +
        xiQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face6004_add_rest]
  simp only [xiQuarticChamberRest6004810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ο` on unowned packet 6006 (5 monomial, top degree `2 * A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def omicronQuarticChamberFace6006810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  - (5 / 128 : k) • (A * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ο` off packet 6006 (19 monomials). -/
def omicronQuarticChamberRestLF6006810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticLoadFree810_eq_face6006_add_rest
    (A B C D E F G : k[X]) :
    omicronQuarticLoadFree810 A B C D E F G =
      omicronQuarticChamberFace6006810 A B C D E F G + omicronQuarticChamberRestLF6006810 A B C D E F G := by
  simp only [omicronQuarticLoadFree810, omicronQuarticChamberFace6006810, omicronQuarticChamberRestLF6006810]
  module

set_option maxHeartbeats 64000000 in
def omicronQuarticChamberRest6006810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  omicronQuarticChamberRestLF6006810 A B C D E F G +
    omicronQuarticColumnL1810 l A B C D E F G +
    omicronQuarticColumnL2810 l A B C D E F G +
    omicronQuarticColumnBeta810 beta A B C D E F G +
    omicronQuarticColumnGamma810 gamma A B C D E F G +
    omicronQuarticColumnDelta810 delta A B C D E F G +
    omicronQuarticColumnEpsilon810 epsilon A B C D E F G +
    omicronQuarticColumnZeta810 zeta A B C D E F G +
    omicronQuarticColumnEta810 eta A B C D E F G +
    omicronQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronQuartic810_eq_face6006_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticChamberFace6006810 A B C D E F G +
        omicronQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroOmicronQuartic810_eq_chamberSplit,
    omicronQuarticLoadFree810_eq_face6006_add_rest]
  simp only [omicronQuarticChamberRest6006810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `Π` on unowned packet 6006 (5 monomial, top degree `3 * A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def primitiveQuarticChamberFace6006810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (5 / 256 : k) • (A ^ 2 * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `Π` off packet 6006 (32 monomials). -/
def primitiveQuarticChamberRestLF6006810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
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

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticLoadFree810_eq_face6006_add_rest
    (A B C D E F G : k[X]) :
    primitiveQuarticLoadFree810 A B C D E F G =
      primitiveQuarticChamberFace6006810 A B C D E F G + primitiveQuarticChamberRestLF6006810 A B C D E F G := by
  simp only [primitiveQuarticLoadFree810, primitiveQuarticChamberFace6006810, primitiveQuarticChamberRestLF6006810]
  module

set_option maxHeartbeats 64000000 in
def primitiveQuarticChamberRest6006810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  primitiveQuarticChamberRestLF6006810 A B C D E F G +
    primitiveQuarticColumnL1810 l A B C D E F G +
    primitiveQuarticColumnL2810 l A B C D E F G +
    primitiveQuarticColumnBeta810 beta A B C D E F G +
    primitiveQuarticColumnGamma810 gamma A B C D E F G +
    primitiveQuarticColumnDelta810 delta A B C D E F G +
    primitiveQuarticColumnEpsilon810 epsilon A B C D E F G +
    primitiveQuarticColumnZeta810 zeta A B C D E F G +
    primitiveQuarticColumnEta810 eta A B C D E F G +
    primitiveQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuartic810_eq_face6006_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticChamberFace6006810 A B C D E F G +
        primitiveQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPrimitiveQuartic810_eq_chamberSplit,
    primitiveQuarticLoadFree810_eq_face6006_add_rest]
  simp only [primitiveQuarticChamberRest6006810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 6007 (2 monomial, top degree `C.natDegree + F.natDegree`). -/
def kappaQuarticChamberFace6007810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6007 (4 monomials). -/
def kappaQuarticChamberRestLF6007810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6007_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6007810 A B C D E F G + kappaQuarticChamberRestLF6007810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6007810, kappaQuarticChamberRestLF6007810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest6007810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF6007810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face6007_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace6007810 A B C D E F G +
        kappaQuarticChamberRest6007810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face6007_add_rest]
  simp only [kappaQuarticChamberRest6007810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on unowned packet 6007 (4 monomial, top degree `A.natDegree + C.natDegree + F.natDegree`). -/
def nuQuarticChamberFace6007810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 6007 (9 monomials). -/
def nuQuarticChamberRestLF6007810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticLoadFree810_eq_face6007_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace6007810 A B C D E F G + nuQuarticChamberRestLF6007810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace6007810, nuQuarticChamberRestLF6007810]
  module

set_option maxHeartbeats 64000000 in
def nuQuarticChamberRest6007810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  nuQuarticChamberRestLF6007810 A B C D E F G +
    nuQuarticColumnL810 l A B C D E F G +
    nuQuarticColumnBeta810 beta A B C D E F G +
    nuQuarticColumnGamma810 gamma A B C D E F G +
    nuQuarticColumnDelta810 delta A B C D E F G +
    nuQuarticColumnEpsilon810 epsilon A B C D E F G +
    nuQuarticColumnZeta810 zeta A B C D E F G +
    nuQuarticColumnEta810 eta A B C D E F G +
    nuQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_face6007_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticChamberFace6007810 A B C D E F G +
        nuQuarticChamberRest6007810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroNuQuartic810_eq_chamberSplit,
    nuQuarticLoadFree810_eq_face6007_add_rest]
  simp only [nuQuarticChamberRest6007810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 6005 (4 monomial, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace6005810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 6005 (9 monomials). -/
def xiQuarticChamberRestLF6005810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face6005_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace6005810 A B C D E F G + xiQuarticChamberRestLF6005810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace6005810, xiQuarticChamberRestLF6005810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest6005810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF6005810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face6005_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace6005810 A B C D E F G +
        xiQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face6005_add_rest]
  simp only [xiQuarticChamberRest6005810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ο` on unowned packet 6007 (4 monomial, top degree `2 * A.natDegree + C.natDegree + F.natDegree`). -/
def omicronQuarticChamberFace6007810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 2 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  - (5 / 128 : k) • (A * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ο` off packet 6007 (20 monomials). -/
def omicronQuarticChamberRestLF6007810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticLoadFree810_eq_face6007_add_rest
    (A B C D E F G : k[X]) :
    omicronQuarticLoadFree810 A B C D E F G =
      omicronQuarticChamberFace6007810 A B C D E F G + omicronQuarticChamberRestLF6007810 A B C D E F G := by
  simp only [omicronQuarticLoadFree810, omicronQuarticChamberFace6007810, omicronQuarticChamberRestLF6007810]
  module

set_option maxHeartbeats 64000000 in
def omicronQuarticChamberRest6007810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  omicronQuarticChamberRestLF6007810 A B C D E F G +
    omicronQuarticColumnL1810 l A B C D E F G +
    omicronQuarticColumnL2810 l A B C D E F G +
    omicronQuarticColumnBeta810 beta A B C D E F G +
    omicronQuarticColumnGamma810 gamma A B C D E F G +
    omicronQuarticColumnDelta810 delta A B C D E F G +
    omicronQuarticColumnEpsilon810 epsilon A B C D E F G +
    omicronQuarticColumnZeta810 zeta A B C D E F G +
    omicronQuarticColumnEta810 eta A B C D E F G +
    omicronQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronQuartic810_eq_face6007_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticChamberFace6007810 A B C D E F G +
        omicronQuarticChamberRest6007810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroOmicronQuartic810_eq_chamberSplit,
    omicronQuarticLoadFree810_eq_face6007_add_rest]
  simp only [omicronQuarticChamberRest6007810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `Π` on unowned packet 6007 (4 monomial, top degree `3 * A.natDegree + C.natDegree + F.natDegree`). -/
def primitiveQuarticChamberFace6007810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (5 / 256 : k) • (A ^ 2 * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `Π` off packet 6007 (33 monomials). -/
def primitiveQuarticChamberRestLF6007810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
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

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticLoadFree810_eq_face6007_add_rest
    (A B C D E F G : k[X]) :
    primitiveQuarticLoadFree810 A B C D E F G =
      primitiveQuarticChamberFace6007810 A B C D E F G + primitiveQuarticChamberRestLF6007810 A B C D E F G := by
  simp only [primitiveQuarticLoadFree810, primitiveQuarticChamberFace6007810, primitiveQuarticChamberRestLF6007810]
  module

set_option maxHeartbeats 64000000 in
def primitiveQuarticChamberRest6007810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  primitiveQuarticChamberRestLF6007810 A B C D E F G +
    primitiveQuarticColumnL1810 l A B C D E F G +
    primitiveQuarticColumnL2810 l A B C D E F G +
    primitiveQuarticColumnBeta810 beta A B C D E F G +
    primitiveQuarticColumnGamma810 gamma A B C D E F G +
    primitiveQuarticColumnDelta810 delta A B C D E F G +
    primitiveQuarticColumnEpsilon810 epsilon A B C D E F G +
    primitiveQuarticColumnZeta810 zeta A B C D E F G +
    primitiveQuarticColumnEta810 eta A B C D E F G +
    primitiveQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuartic810_eq_face6007_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticChamberFace6007810 A B C D E F G +
        primitiveQuarticChamberRest6007810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPrimitiveQuartic810_eq_chamberSplit,
    primitiveQuarticLoadFree810_eq_face6007_add_rest]
  simp only [primitiveQuarticChamberRest6007810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 6008 (4 monomial, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace6008810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6008 (2 monomials). -/
def kappaQuarticChamberRestLF6008810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6008_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6008810 A B C D E F G + kappaQuarticChamberRestLF6008810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6008810, kappaQuarticChamberRestLF6008810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest6008810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF6008810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face6008_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace6008810 A B C D E F G +
        kappaQuarticChamberRest6008810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face6008_add_rest]
  simp only [kappaQuarticChamberRest6008810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on unowned packet 6008 (6 monomial, top degree `A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def nuQuarticChamberFace6008810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 6008 (7 monomials). -/
def nuQuarticChamberRestLF6008810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticLoadFree810_eq_face6008_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace6008810 A B C D E F G + nuQuarticChamberRestLF6008810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace6008810, nuQuarticChamberRestLF6008810]
  module

set_option maxHeartbeats 64000000 in
def nuQuarticChamberRest6008810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  nuQuarticChamberRestLF6008810 A B C D E F G +
    nuQuarticColumnL810 l A B C D E F G +
    nuQuarticColumnBeta810 beta A B C D E F G +
    nuQuarticColumnGamma810 gamma A B C D E F G +
    nuQuarticColumnDelta810 delta A B C D E F G +
    nuQuarticColumnEpsilon810 epsilon A B C D E F G +
    nuQuarticColumnZeta810 zeta A B C D E F G +
    nuQuarticColumnEta810 eta A B C D E F G +
    nuQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_face6008_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticChamberFace6008810 A B C D E F G +
        nuQuarticChamberRest6008810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroNuQuartic810_eq_chamberSplit,
    nuQuarticLoadFree810_eq_face6008_add_rest]
  simp only [nuQuarticChamberRest6008810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 6006 (5 monomial, top degree `A.natDegree + B.natDegree + C.natDegree + D.natDegree`). -/
def xiQuarticChamberFace6006810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)
  - (5 / 64 : k) • (A * D * F)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 6006 (8 monomials). -/
def xiQuarticChamberRestLF6006810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face6006_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace6006810 A B C D E F G + xiQuarticChamberRestLF6006810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace6006810, xiQuarticChamberRestLF6006810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest6006810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF6006810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face6006_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace6006810 A B C D E F G +
        xiQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face6006_add_rest]
  simp only [xiQuarticChamberRest6006810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ο` on unowned packet 6008 (6 monomial, top degree `2 * A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def omicronQuarticChamberFace6008810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  - (5 / 128 : k) • (A * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ο` off packet 6008 (18 monomials). -/
def omicronQuarticChamberRestLF6008810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticLoadFree810_eq_face6008_add_rest
    (A B C D E F G : k[X]) :
    omicronQuarticLoadFree810 A B C D E F G =
      omicronQuarticChamberFace6008810 A B C D E F G + omicronQuarticChamberRestLF6008810 A B C D E F G := by
  simp only [omicronQuarticLoadFree810, omicronQuarticChamberFace6008810, omicronQuarticChamberRestLF6008810]
  module

set_option maxHeartbeats 64000000 in
def omicronQuarticChamberRest6008810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  omicronQuarticChamberRestLF6008810 A B C D E F G +
    omicronQuarticColumnL1810 l A B C D E F G +
    omicronQuarticColumnL2810 l A B C D E F G +
    omicronQuarticColumnBeta810 beta A B C D E F G +
    omicronQuarticColumnGamma810 gamma A B C D E F G +
    omicronQuarticColumnDelta810 delta A B C D E F G +
    omicronQuarticColumnEpsilon810 epsilon A B C D E F G +
    omicronQuarticColumnZeta810 zeta A B C D E F G +
    omicronQuarticColumnEta810 eta A B C D E F G +
    omicronQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronQuartic810_eq_face6008_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticChamberFace6008810 A B C D E F G +
        omicronQuarticChamberRest6008810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroOmicronQuartic810_eq_chamberSplit,
    omicronQuarticLoadFree810_eq_face6008_add_rest]
  simp only [omicronQuarticChamberRest6008810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `Π` on unowned packet 6008 (6 monomial, top degree `3 * A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def primitiveQuarticChamberFace6008810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (5 / 256 : k) • (A ^ 2 * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `Π` off packet 6008 (31 monomials). -/
def primitiveQuarticChamberRestLF6008810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
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

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticLoadFree810_eq_face6008_add_rest
    (A B C D E F G : k[X]) :
    primitiveQuarticLoadFree810 A B C D E F G =
      primitiveQuarticChamberFace6008810 A B C D E F G + primitiveQuarticChamberRestLF6008810 A B C D E F G := by
  simp only [primitiveQuarticLoadFree810, primitiveQuarticChamberFace6008810, primitiveQuarticChamberRestLF6008810]
  module

set_option maxHeartbeats 64000000 in
def primitiveQuarticChamberRest6008810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  primitiveQuarticChamberRestLF6008810 A B C D E F G +
    primitiveQuarticColumnL1810 l A B C D E F G +
    primitiveQuarticColumnL2810 l A B C D E F G +
    primitiveQuarticColumnBeta810 beta A B C D E F G +
    primitiveQuarticColumnGamma810 gamma A B C D E F G +
    primitiveQuarticColumnDelta810 delta A B C D E F G +
    primitiveQuarticColumnEpsilon810 epsilon A B C D E F G +
    primitiveQuarticColumnZeta810 zeta A B C D E F G +
    primitiveQuarticColumnEta810 eta A B C D E F G +
    primitiveQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuartic810_eq_face6008_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticChamberFace6008810 A B C D E F G +
        primitiveQuarticChamberRest6008810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPrimitiveQuartic810_eq_chamberSplit,
    primitiveQuarticLoadFree810_eq_face6008_add_rest]
  simp only [primitiveQuarticChamberRest6008810]
  ring


end QuarticChamberUnownedSystemPackets2810

end Max11DegreeRoutes
