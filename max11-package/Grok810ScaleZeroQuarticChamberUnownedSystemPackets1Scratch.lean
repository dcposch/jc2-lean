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

/-! # UnownedSystem face packets, part 1/2

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

section QuarticChamberUnownedSystemPackets1810

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 6000 (2 monomial, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace6000810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6000 (4 monomials). -/
def kappaQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6000_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6000810 A B C D E F G + kappaQuarticChamberRestLF6000810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6000810, kappaQuarticChamberRestLF6000810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest6000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF6000810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face6000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace6000810 A B C D E F G +
        kappaQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face6000_add_rest]
  simp only [kappaQuarticChamberRest6000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on unowned packet 6000 (2 monomial, top degree `2 * A.natDegree + 3 * B.natDegree`). -/
def nuQuarticChamberFace6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  - (5 / 128 : k) • (A * B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 6000 (11 monomials). -/
def nuQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticLoadFree810_eq_face6000_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace6000810 A B C D E F G + nuQuarticChamberRestLF6000810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace6000810, nuQuarticChamberRestLF6000810]
  module

set_option maxHeartbeats 64000000 in
def nuQuarticChamberRest6000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  nuQuarticChamberRestLF6000810 A B C D E F G +
    nuQuarticColumnL810 l A B C D E F G +
    nuQuarticColumnBeta810 beta A B C D E F G +
    nuQuarticColumnGamma810 gamma A B C D E F G +
    nuQuarticColumnDelta810 delta A B C D E F G +
    nuQuarticColumnEpsilon810 epsilon A B C D E F G +
    nuQuarticColumnZeta810 zeta A B C D E F G +
    nuQuarticColumnEta810 eta A B C D E F G +
    nuQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_face6000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticChamberFace6000810 A B C D E F G +
        nuQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroNuQuartic810_eq_chamberSplit,
    nuQuarticLoadFree810_eq_face6000_add_rest]
  simp only [nuQuarticChamberRest6000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ο` on unowned packet 6000 (2 monomial, top degree `3 * A.natDegree + 3 * B.natDegree`). -/
def omicronQuarticChamberFace6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (5 / 2048 : k) • (A ^ 2 * B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ο` off packet 6000 (22 monomials). -/
def omicronQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 16384 : k)) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
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

set_option maxHeartbeats 64000000 in
theorem omicronQuarticLoadFree810_eq_face6000_add_rest
    (A B C D E F G : k[X]) :
    omicronQuarticLoadFree810 A B C D E F G =
      omicronQuarticChamberFace6000810 A B C D E F G + omicronQuarticChamberRestLF6000810 A B C D E F G := by
  simp only [omicronQuarticLoadFree810, omicronQuarticChamberFace6000810, omicronQuarticChamberRestLF6000810]
  module

set_option maxHeartbeats 64000000 in
def omicronQuarticChamberRest6000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  omicronQuarticChamberRestLF6000810 A B C D E F G +
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
theorem degreeZeroOmicronQuartic810_eq_face6000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticChamberFace6000810 A B C D E F G +
        omicronQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroOmicronQuartic810_eq_chamberSplit,
    omicronQuarticLoadFree810_eq_face6000_add_rest]
  simp only [omicronQuarticChamberRest6000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 6000 (3 monomial, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace6000810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 6000 (18 monomials). -/
def piQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
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

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face6000_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace6000810 A B C D E F G + piQuarticChamberRestLF6000810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace6000810, piQuarticChamberRestLF6000810]
  module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest6000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF6000810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face6000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace6000810 A B C D E F G +
        piQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face6000_add_rest]
  simp only [piQuarticChamberRest6000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `Π` on unowned packet 6000 (2 monomial, top degree `4 * A.natDegree + 3 * B.natDegree`). -/
def primitiveQuarticChamberFace6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (5 / 2048 : k) • (A ^ 3 * B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `Π` off packet 6000 (35 monomials). -/
def primitiveQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 16384 : k)) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
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

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticLoadFree810_eq_face6000_add_rest
    (A B C D E F G : k[X]) :
    primitiveQuarticLoadFree810 A B C D E F G =
      primitiveQuarticChamberFace6000810 A B C D E F G + primitiveQuarticChamberRestLF6000810 A B C D E F G := by
  simp only [primitiveQuarticLoadFree810, primitiveQuarticChamberFace6000810, primitiveQuarticChamberRestLF6000810]
  module

set_option maxHeartbeats 64000000 in
def primitiveQuarticChamberRest6000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  primitiveQuarticChamberRestLF6000810 A B C D E F G +
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
theorem degreeZeroPrimitiveQuartic810_eq_face6000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticChamberFace6000810 A B C D E F G +
        primitiveQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPrimitiveQuartic810_eq_chamberSplit,
    primitiveQuarticLoadFree810_eq_face6000_add_rest]
  simp only [primitiveQuarticChamberRest6000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 6000 (2 monomial, top degree `3 * C.natDegree`). -/
def muQuarticChamberFace6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 6000 (8 monomials). -/
def muQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face6000_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace6000810 A B C D E F G + muQuarticChamberRestLF6000810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace6000810, muQuarticChamberRestLF6000810]
  module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest6000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF6000810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face6000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace6000810 A B C D E F G +
        muQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face6000_add_rest]
  simp only [muQuarticChamberRest6000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 6001 (3 monomial, top degree `4 * C.natDegree`). -/
def piQuarticChamberFace6001810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 6001 (18 monomials). -/
def piQuarticChamberRestLF6001810
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
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face6001_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace6001810 A B C D E F G + piQuarticChamberRestLF6001810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace6001810, piQuarticChamberRestLF6001810]
  module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest6001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF6001810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face6001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace6001810 A B C D E F G +
        piQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face6001_add_rest]
  simp only [piQuarticChamberRest6001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 6001 (3 monomial, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace6001810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6001 (3 monomials). -/
def kappaQuarticChamberRestLF6001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6001_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6001810 A B C D E F G + kappaQuarticChamberRestLF6001810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6001810, kappaQuarticChamberRestLF6001810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest6001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF6001810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face6001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace6001810 A B C D E F G +
        kappaQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face6001_add_rest]
  simp only [kappaQuarticChamberRest6001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 6001 (3 monomial, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace6001810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 6001 (7 monomials). -/
def muQuarticChamberRestLF6001810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face6001_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace6001810 A B C D E F G + muQuarticChamberRestLF6001810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace6001810, muQuarticChamberRestLF6001810]
  module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest6001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF6001810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face6001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace6001810 A B C D E F G +
        muQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face6001_add_rest]
  simp only [muQuarticChamberRest6001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on unowned packet 6001 (3 monomial, top degree `2 * A.natDegree + 3 * B.natDegree`). -/
def nuQuarticChamberFace6001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 6001 (10 monomials). -/
def nuQuarticChamberRestLF6001810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticLoadFree810_eq_face6001_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace6001810 A B C D E F G + nuQuarticChamberRestLF6001810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace6001810, nuQuarticChamberRestLF6001810]
  module

set_option maxHeartbeats 64000000 in
def nuQuarticChamberRest6001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  nuQuarticChamberRestLF6001810 A B C D E F G +
    nuQuarticColumnL810 l A B C D E F G +
    nuQuarticColumnBeta810 beta A B C D E F G +
    nuQuarticColumnGamma810 gamma A B C D E F G +
    nuQuarticColumnDelta810 delta A B C D E F G +
    nuQuarticColumnEpsilon810 epsilon A B C D E F G +
    nuQuarticColumnZeta810 zeta A B C D E F G +
    nuQuarticColumnEta810 eta A B C D E F G +
    nuQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_face6001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticChamberFace6001810 A B C D E F G +
        nuQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroNuQuartic810_eq_chamberSplit,
    nuQuarticLoadFree810_eq_face6001_add_rest]
  simp only [nuQuarticChamberRest6001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ο` on unowned packet 6001 (3 monomial, top degree `3 * A.natDegree + 3 * B.natDegree`). -/
def omicronQuarticChamberFace6001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 2 * C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ο` off packet 6001 (21 monomials). -/
def omicronQuarticChamberRestLF6001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 16384 : k)) • (A ^ 2 * B ^ 2 * D)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
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
theorem omicronQuarticLoadFree810_eq_face6001_add_rest
    (A B C D E F G : k[X]) :
    omicronQuarticLoadFree810 A B C D E F G =
      omicronQuarticChamberFace6001810 A B C D E F G + omicronQuarticChamberRestLF6001810 A B C D E F G := by
  simp only [omicronQuarticLoadFree810, omicronQuarticChamberFace6001810, omicronQuarticChamberRestLF6001810]
  module

set_option maxHeartbeats 64000000 in
def omicronQuarticChamberRest6001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  omicronQuarticChamberRestLF6001810 A B C D E F G +
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
theorem degreeZeroOmicronQuartic810_eq_face6001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticChamberFace6001810 A B C D E F G +
        omicronQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroOmicronQuartic810_eq_chamberSplit,
    omicronQuarticLoadFree810_eq_face6001_add_rest]
  simp only [omicronQuarticChamberRest6001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 6002 (5 monomial, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace6002810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 32 : k) • (A * B * C * F)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 6002 (16 monomials). -/
def piQuarticChamberRestLF6002810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face6002_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace6002810 A B C D E F G + piQuarticChamberRestLF6002810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace6002810, piQuarticChamberRestLF6002810]
  module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest6002810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF6002810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face6002_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace6002810 A B C D E F G +
        piQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face6002_add_rest]
  simp only [piQuarticChamberRest6002810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `Π` on unowned packet 6001 (3 monomial, top degree `4 * A.natDegree + 3 * B.natDegree`). -/
def primitiveQuarticChamberFace6001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 3 * C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `Π` off packet 6001 (34 monomials). -/
def primitiveQuarticChamberRestLF6001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 16384 : k)) • (A ^ 3 * B ^ 2 * D)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
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
theorem primitiveQuarticLoadFree810_eq_face6001_add_rest
    (A B C D E F G : k[X]) :
    primitiveQuarticLoadFree810 A B C D E F G =
      primitiveQuarticChamberFace6001810 A B C D E F G + primitiveQuarticChamberRestLF6001810 A B C D E F G := by
  simp only [primitiveQuarticLoadFree810, primitiveQuarticChamberFace6001810, primitiveQuarticChamberRestLF6001810]
  module

set_option maxHeartbeats 64000000 in
def primitiveQuarticChamberRest6001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  primitiveQuarticChamberRestLF6001810 A B C D E F G +
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
theorem degreeZeroPrimitiveQuartic810_eq_face6001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticChamberFace6001810 A B C D E F G +
        primitiveQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPrimitiveQuartic810_eq_chamberSplit,
    primitiveQuarticLoadFree810_eq_face6001_add_rest]
  simp only [primitiveQuarticChamberRest6001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 6002 (3 monomial, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace6002810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6002 (3 monomials). -/
def kappaQuarticChamberRestLF6002810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6002_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6002810 A B C D E F G + kappaQuarticChamberRestLF6002810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6002810, kappaQuarticChamberRestLF6002810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest6002810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF6002810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face6002_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace6002810 A B C D E F G +
        kappaQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face6002_add_rest]
  simp only [kappaQuarticChamberRest6002810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 6002 (3 monomial, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace6002810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 6002 (7 monomials). -/
def muQuarticChamberRestLF6002810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face6002_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace6002810 A B C D E F G + muQuarticChamberRestLF6002810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace6002810, muQuarticChamberRestLF6002810]
  module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest6002810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF6002810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face6002_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace6002810 A B C D E F G +
        muQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face6002_add_rest]
  simp only [muQuarticChamberRest6002810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on unowned packet 6002 (3 monomial, top degree `2 * A.natDegree + 3 * B.natDegree`). -/
def nuQuarticChamberFace6002810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 6002 (10 monomials). -/
def nuQuarticChamberRestLF6002810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticLoadFree810_eq_face6002_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace6002810 A B C D E F G + nuQuarticChamberRestLF6002810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace6002810, nuQuarticChamberRestLF6002810]
  module

set_option maxHeartbeats 64000000 in
def nuQuarticChamberRest6002810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  nuQuarticChamberRestLF6002810 A B C D E F G +
    nuQuarticColumnL810 l A B C D E F G +
    nuQuarticColumnBeta810 beta A B C D E F G +
    nuQuarticColumnGamma810 gamma A B C D E F G +
    nuQuarticColumnDelta810 delta A B C D E F G +
    nuQuarticColumnEpsilon810 epsilon A B C D E F G +
    nuQuarticColumnZeta810 zeta A B C D E F G +
    nuQuarticColumnEta810 eta A B C D E F G +
    nuQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_face6002_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticChamberFace6002810 A B C D E F G +
        nuQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroNuQuartic810_eq_chamberSplit,
    nuQuarticLoadFree810_eq_face6002_add_rest]
  simp only [nuQuarticChamberRest6002810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ο` on unowned packet 6002 (3 monomial, top degree `3 * A.natDegree + 3 * B.natDegree`). -/
def omicronQuarticChamberFace6002810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 2 * B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ο` off packet 6002 (21 monomials). -/
def omicronQuarticChamberRestLF6002810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 16384 : k)) • (A ^ 2 * B ^ 2 * D)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
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

set_option maxHeartbeats 64000000 in
theorem omicronQuarticLoadFree810_eq_face6002_add_rest
    (A B C D E F G : k[X]) :
    omicronQuarticLoadFree810 A B C D E F G =
      omicronQuarticChamberFace6002810 A B C D E F G + omicronQuarticChamberRestLF6002810 A B C D E F G := by
  simp only [omicronQuarticLoadFree810, omicronQuarticChamberFace6002810, omicronQuarticChamberRestLF6002810]
  module

set_option maxHeartbeats 64000000 in
def omicronQuarticChamberRest6002810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  omicronQuarticChamberRestLF6002810 A B C D E F G +
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
theorem degreeZeroOmicronQuartic810_eq_face6002_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticChamberFace6002810 A B C D E F G +
        omicronQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroOmicronQuartic810_eq_chamberSplit,
    omicronQuarticLoadFree810_eq_face6002_add_rest]
  simp only [omicronQuarticChamberRest6002810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 6003 (6 monomial, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace6003810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 6003 (15 monomials). -/
def piQuarticChamberRestLF6003810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face6003_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace6003810 A B C D E F G + piQuarticChamberRestLF6003810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace6003810, piQuarticChamberRestLF6003810]
  module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest6003810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF6003810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face6003_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace6003810 A B C D E F G +
        piQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face6003_add_rest]
  simp only [piQuarticChamberRest6003810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `Π` on unowned packet 6002 (3 monomial, top degree `4 * A.natDegree + 3 * B.natDegree`). -/
def primitiveQuarticChamberFace6002810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 3 * B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `Π` off packet 6002 (34 monomials). -/
def primitiveQuarticChamberRestLF6002810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 16384 : k)) • (A ^ 3 * B ^ 2 * D)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
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

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticLoadFree810_eq_face6002_add_rest
    (A B C D E F G : k[X]) :
    primitiveQuarticLoadFree810 A B C D E F G =
      primitiveQuarticChamberFace6002810 A B C D E F G + primitiveQuarticChamberRestLF6002810 A B C D E F G := by
  simp only [primitiveQuarticLoadFree810, primitiveQuarticChamberFace6002810, primitiveQuarticChamberRestLF6002810]
  module

set_option maxHeartbeats 64000000 in
def primitiveQuarticChamberRest6002810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  primitiveQuarticChamberRestLF6002810 A B C D E F G +
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
theorem degreeZeroPrimitiveQuartic810_eq_face6002_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticChamberFace6002810 A B C D E F G +
        primitiveQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPrimitiveQuartic810_eq_chamberSplit,
    primitiveQuarticLoadFree810_eq_face6002_add_rest]
  simp only [primitiveQuarticChamberRest6002810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 6003 (2 monomial, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace6003810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6003 (4 monomials). -/
def kappaQuarticChamberRestLF6003810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6003_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6003810 A B C D E F G + kappaQuarticChamberRestLF6003810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6003810, kappaQuarticChamberRestLF6003810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest6003810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF6003810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face6003_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace6003810 A B C D E F G +
        kappaQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face6003_add_rest]
  simp only [kappaQuarticChamberRest6003810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on unowned packet 6003 (2 monomial, top degree `A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def nuQuarticChamberFace6003810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 6003 (11 monomials). -/
def nuQuarticChamberRestLF6003810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticLoadFree810_eq_face6003_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace6003810 A B C D E F G + nuQuarticChamberRestLF6003810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace6003810, nuQuarticChamberRestLF6003810]
  module

set_option maxHeartbeats 64000000 in
def nuQuarticChamberRest6003810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  nuQuarticChamberRestLF6003810 A B C D E F G +
    nuQuarticColumnL810 l A B C D E F G +
    nuQuarticColumnBeta810 beta A B C D E F G +
    nuQuarticColumnGamma810 gamma A B C D E F G +
    nuQuarticColumnDelta810 delta A B C D E F G +
    nuQuarticColumnEpsilon810 epsilon A B C D E F G +
    nuQuarticColumnZeta810 zeta A B C D E F G +
    nuQuarticColumnEta810 eta A B C D E F G +
    nuQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_face6003_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticChamberFace6003810 A B C D E F G +
        nuQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroNuQuartic810_eq_chamberSplit,
    nuQuarticLoadFree810_eq_face6003_add_rest]
  simp only [nuQuarticChamberRest6003810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ο` on unowned packet 6003 (2 monomial, top degree `2 * A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def omicronQuarticChamberFace6003810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 2 * B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ο` off packet 6003 (22 monomials). -/
def omicronQuarticChamberRestLF6003810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
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

set_option maxHeartbeats 64000000 in
theorem omicronQuarticLoadFree810_eq_face6003_add_rest
    (A B C D E F G : k[X]) :
    omicronQuarticLoadFree810 A B C D E F G =
      omicronQuarticChamberFace6003810 A B C D E F G + omicronQuarticChamberRestLF6003810 A B C D E F G := by
  simp only [omicronQuarticLoadFree810, omicronQuarticChamberFace6003810, omicronQuarticChamberRestLF6003810]
  module

set_option maxHeartbeats 64000000 in
def omicronQuarticChamberRest6003810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  omicronQuarticChamberRestLF6003810 A B C D E F G +
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
theorem degreeZeroOmicronQuartic810_eq_face6003_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticChamberFace6003810 A B C D E F G +
        omicronQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroOmicronQuartic810_eq_chamberSplit,
    omicronQuarticLoadFree810_eq_face6003_add_rest]
  simp only [omicronQuarticChamberRest6003810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `Π` on unowned packet 6003 (2 monomial, top degree `3 * A.natDegree + B.natDegree + 2 * C.natDegree`). -/
def primitiveQuarticChamberFace6003810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 3 * B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `Π` off packet 6003 (35 monomials). -/
def primitiveQuarticChamberRestLF6003810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
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

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticLoadFree810_eq_face6003_add_rest
    (A B C D E F G : k[X]) :
    primitiveQuarticLoadFree810 A B C D E F G =
      primitiveQuarticChamberFace6003810 A B C D E F G + primitiveQuarticChamberRestLF6003810 A B C D E F G := by
  simp only [primitiveQuarticLoadFree810, primitiveQuarticChamberFace6003810, primitiveQuarticChamberRestLF6003810]
  module

set_option maxHeartbeats 64000000 in
def primitiveQuarticChamberRest6003810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  primitiveQuarticChamberRestLF6003810 A B C D E F G +
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
theorem degreeZeroPrimitiveQuartic810_eq_face6003_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticChamberFace6003810 A B C D E F G +
        primitiveQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPrimitiveQuartic810_eq_chamberSplit,
    primitiveQuarticLoadFree810_eq_face6003_add_rest]
  simp only [primitiveQuarticChamberRest6003810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 6003 (3 monomial, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace6003810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 6003 (7 monomials). -/
def muQuarticChamberRestLF6003810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face6003_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace6003810 A B C D E F G + muQuarticChamberRestLF6003810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace6003810, muQuarticChamberRestLF6003810]
  module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest6003810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF6003810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face6003_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace6003810 A B C D E F G +
        muQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face6003_add_rest]
  simp only [muQuarticChamberRest6003810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 6004 (4 monomial, top degree `A.natDegree + C.natDegree + 2 * D.natDegree`). -/
def piQuarticChamberFace6004810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 6004 (17 monomials). -/
def piQuarticChamberRestLF6004810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face6004_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace6004810 A B C D E F G + piQuarticChamberRestLF6004810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace6004810, piQuarticChamberRestLF6004810]
  module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest6004810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF6004810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face6004_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace6004810 A B C D E F G +
        piQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face6004_add_rest]
  simp only [piQuarticChamberRest6004810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₃` on unowned packet 6000 (2 monomial, top degree `A.natDegree + 2 * C.natDegree + D.natDegree`). -/
def n3QuarticChamberFace6000810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 2048 : k) • (A * C ^ 2 * D)
  - (15 / 256 : k) • (A * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₃` off packet 6000 (17 monomials). -/
def n3QuarticChamberRestLF6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 8192 : k)) • (A ^ 2 * B ^ 2 * D)
  - (175 / 8192 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (65 / 2048 : k) • (A * B ^ 2 * F)
  + (45 / 1024 : k) • (A * B * C * E)
  + (85 / 2048 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 256 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem n3QuarticLoadFree810_eq_face6000_add_rest
    (A B C D E F G : k[X]) :
    n3QuarticLoadFree810 A B C D E F G =
      n3QuarticChamberFace6000810 A B C D E F G + n3QuarticChamberRestLF6000810 A B C D E F G := by
  simp only [n3QuarticLoadFree810, n3QuarticChamberFace6000810, n3QuarticChamberRestLF6000810]
  module

set_option maxHeartbeats 64000000 in
def n3QuarticChamberRest6000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n3QuarticChamberRestLF6000810 A B C D E F G +
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
theorem degreeZeroN3Quartic810_eq_face6000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n3QuarticChamberFace6000810 A B C D E F G +
        n3QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN3Quartic810_eq_chamberSplit,
    n3QuarticLoadFree810_eq_face6000_add_rest]
  simp only [n3QuarticChamberRest6000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₄` on unowned packet 6000 (2 monomial, top degree `2 * A.natDegree + 2 * C.natDegree + D.natDegree`). -/
def n4QuarticChamberFace6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A ^ 2 * C ^ 2 * D)
  + (5 / 256 : k) • (A ^ 2 * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₄` off packet 6000 (31 monomials). -/
def n4QuarticChamberRestLF6000810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 8192 : k) • (A ^ 3 * B ^ 2 * D)
  + (155 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (107 / 8192 : k) • (A * B ^ 5)
  - (55 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  - (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (95 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (45 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 512 : k) • (A * B ^ 2 * C * D)
  - (15 / 256 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (5 / 256 : k) • (A ^ 2 * E * F)
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
theorem n4QuarticLoadFree810_eq_face6000_add_rest
    (A B C D E F G : k[X]) :
    n4QuarticLoadFree810 A B C D E F G =
      n4QuarticChamberFace6000810 A B C D E F G + n4QuarticChamberRestLF6000810 A B C D E F G := by
  simp only [n4QuarticLoadFree810, n4QuarticChamberFace6000810, n4QuarticChamberRestLF6000810]
  module

set_option maxHeartbeats 64000000 in
def n4QuarticChamberRest6000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n4QuarticChamberRestLF6000810 A B C D E F G +
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
theorem degreeZeroN4Quartic810_eq_face6000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n4QuarticChamberFace6000810 A B C D E F G +
        n4QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN4Quartic810_eq_chamberSplit,
    n4QuarticLoadFree810_eq_face6000_add_rest]
  simp only [n4QuarticChamberRest6000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 6004 (3 monomial, top degree `3 * C.natDegree`). -/
def muQuarticChamberFace6004810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 6004 (7 monomials). -/
def muQuarticChamberRestLF6004810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face6004_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace6004810 A B C D E F G + muQuarticChamberRestLF6004810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace6004810, muQuarticChamberRestLF6004810]
  module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest6004810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF6004810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face6004_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace6004810 A B C D E F G +
        muQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face6004_add_rest]
  simp only [muQuarticChamberRest6004810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 6000 (2 monomial, top degree `2 * C.natDegree + E.natDegree`). -/
def xiQuarticChamberFace6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 6000 (11 monomials). -/
def xiQuarticChamberRestLF6000810
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
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face6000_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace6000810 A B C D E F G + xiQuarticChamberRestLF6000810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace6000810, xiQuarticChamberRestLF6000810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest6000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF6000810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face6000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace6000810 A B C D E F G +
        xiQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face6000_add_rest]
  simp only [xiQuarticChamberRest6000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 6005 (4 monomial, top degree `4 * C.natDegree`). -/
def piQuarticChamberFace6005810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (C * E ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 6005 (17 monomials). -/
def piQuarticChamberRestLF6005810
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
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face6005_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace6005810 A B C D E F G + piQuarticChamberRestLF6005810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace6005810, piQuarticChamberRestLF6005810]
  module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest6005810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF6005810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face6005_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace6005810 A B C D E F G +
        piQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face6005_add_rest]
  simp only [piQuarticChamberRest6005810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₂` on unowned packet 6000 (2 monomial, top degree `2 * C.natDegree + D.natDegree`). -/
def n2QuarticChamberFace6000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₂` off packet 6000 (6 monomials). -/
def n2QuarticChamberRestLF6000810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem n2QuarticLoadFree810_eq_face6000_add_rest
    (A B C D E F G : k[X]) :
    n2QuarticLoadFree810 A B C D E F G =
      n2QuarticChamberFace6000810 A B C D E F G + n2QuarticChamberRestLF6000810 A B C D E F G := by
  simp only [n2QuarticLoadFree810, n2QuarticChamberFace6000810, n2QuarticChamberRestLF6000810]
  module

set_option maxHeartbeats 64000000 in
def n2QuarticChamberRest6000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticChamberRestLF6000810 A B C D E F G +
    n2QuarticColumnL810 l A B C D E F G +
    n2QuarticColumnBeta810 beta A B C D E F G +
    n2QuarticColumnGamma810 gamma A B C D E F G +
    n2QuarticColumnDelta810 delta A B C D E F G +
    n2QuarticColumnEpsilon810 epsilon A B C D E F G +
    n2QuarticColumnZeta810 zeta A B C D E F G +
    n2QuarticColumnEta810 eta A B C D E F G +
    n2QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_face6000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticChamberFace6000810 A B C D E F G +
        n2QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN2Quartic810_eq_chamberSplit,
    n2QuarticLoadFree810_eq_face6000_add_rest]
  simp only [n2QuarticChamberRest6000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 6001 (2 monomial, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace6001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 6001 (11 monomials). -/
def xiQuarticChamberRestLF6001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face6001_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace6001810 A B C D E F G + xiQuarticChamberRestLF6001810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace6001810, xiQuarticChamberRestLF6001810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest6001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF6001810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face6001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace6001810 A B C D E F G +
        xiQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face6001_add_rest]
  simp only [xiQuarticChamberRest6001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 6006 (2 monomial, top degree `A.natDegree + 2 * F.natDegree`). -/
def piQuarticChamberFace6006810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (A * F ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 6006 (19 monomials). -/
def piQuarticChamberRestLF6006810
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
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face6006_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace6006810 A B C D E F G + piQuarticChamberRestLF6006810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace6006810, piQuarticChamberRestLF6006810]
  module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest6006810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF6006810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face6006_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace6006810 A B C D E F G +
        piQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face6006_add_rest]
  simp only [piQuarticChamberRest6006810]
  ring


end QuarticChamberUnownedSystemPackets1810

end Max11DegreeRoutes
