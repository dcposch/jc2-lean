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

/-! # Unowned face packets, part 1/1

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

section QuarticChamberUnownedPackets810

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 5000 (1 monomial, top degree `3 * C.natDegree`). -/
def muQuarticChamberFace5000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 5000 (9 monomials). -/
def muQuarticChamberRestLF5000810
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

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face5000_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace5000810 A B C D E F G + muQuarticChamberRestLF5000810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace5000810, muQuarticChamberRestLF5000810]
  module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest5000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF5000810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face5000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace5000810 A B C D E F G +
        muQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face5000_add_rest]
  simp only [muQuarticChamberRest5000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 5001 (1 monomial, top degree `2 * E.natDegree`). -/
def muQuarticChamberFace5001810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 5001 (9 monomials). -/
def muQuarticChamberRestLF5001810
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

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face5001_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace5001810 A B C D E F G + muQuarticChamberRestLF5001810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace5001810, muQuarticChamberRestLF5001810]
  module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest5001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF5001810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face5001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace5001810 A B C D E F G +
        muQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face5001_add_rest]
  simp only [muQuarticChamberRest5001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 5000 (1 monomial, top degree `2 * G.natDegree`). -/
def piQuarticChamberFace5000810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 5000 (20 monomials). -/
def piQuarticChamberRestLF5000810
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
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face5000_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace5000810 A B C D E F G + piQuarticChamberRestLF5000810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace5000810, piQuarticChamberRestLF5000810]
  module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest5000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF5000810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face5000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace5000810 A B C D E F G +
        piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face5000_add_rest]
  simp only [piQuarticChamberRest5000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₃` on unowned packet 5000 (1 monomial, top degree `A.natDegree + 2 * C.natDegree + D.natDegree`). -/
def n3QuarticChamberFace5000810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 2048 : k) • (A * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₃` off packet 5000 (18 monomials). -/
def n3QuarticChamberRestLF5000810
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
  - (15 / 256 : k) • (A * D * G)
  - (15 / 256 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem n3QuarticLoadFree810_eq_face5000_add_rest
    (A B C D E F G : k[X]) :
    n3QuarticLoadFree810 A B C D E F G =
      n3QuarticChamberFace5000810 A B C D E F G + n3QuarticChamberRestLF5000810 A B C D E F G := by
  simp only [n3QuarticLoadFree810, n3QuarticChamberFace5000810, n3QuarticChamberRestLF5000810]
  module

set_option maxHeartbeats 64000000 in
def n3QuarticChamberRest5000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n3QuarticChamberRestLF5000810 A B C D E F G +
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
theorem degreeZeroN3Quartic810_eq_face5000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n3QuarticChamberFace5000810 A B C D E F G +
        n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN3Quartic810_eq_chamberSplit,
    n3QuarticLoadFree810_eq_face5000_add_rest]
  simp only [n3QuarticChamberRest5000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 5000 (1 monomial, top degree `2 * C.natDegree + E.natDegree`). -/
def xiQuarticChamberFace5000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 5000 (12 monomials). -/
def xiQuarticChamberRestLF5000810
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
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face5000_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace5000810 A B C D E F G + xiQuarticChamberRestLF5000810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace5000810, xiQuarticChamberRestLF5000810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest5000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF5000810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face5000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace5000810 A B C D E F G +
        xiQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face5000_add_rest]
  simp only [xiQuarticChamberRest5000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 5001 (1 monomial, top degree `A.natDegree + 2 * F.natDegree`). -/
def piQuarticChamberFace5001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 5001 (20 monomials). -/
def piQuarticChamberRestLF5001810
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
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face5001_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace5001810 A B C D E F G + piQuarticChamberRestLF5001810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace5001810, piQuarticChamberRestLF5001810]
  module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest5001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF5001810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face5001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace5001810 A B C D E F G +
        piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face5001_add_rest]
  simp only [piQuarticChamberRest5001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₂` on unowned packet 5000 (1 monomial, top degree `2 * C.natDegree + D.natDegree`). -/
def n2QuarticChamberFace5000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₂` off packet 5000 (7 monomials). -/
def n2QuarticChamberRestLF5000810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem n2QuarticLoadFree810_eq_face5000_add_rest
    (A B C D E F G : k[X]) :
    n2QuarticLoadFree810 A B C D E F G =
      n2QuarticChamberFace5000810 A B C D E F G + n2QuarticChamberRestLF5000810 A B C D E F G := by
  simp only [n2QuarticLoadFree810, n2QuarticChamberFace5000810, n2QuarticChamberRestLF5000810]
  module

set_option maxHeartbeats 64000000 in
def n2QuarticChamberRest5000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticChamberRestLF5000810 A B C D E F G +
    n2QuarticColumnL810 l A B C D E F G +
    n2QuarticColumnBeta810 beta A B C D E F G +
    n2QuarticColumnGamma810 gamma A B C D E F G +
    n2QuarticColumnDelta810 delta A B C D E F G +
    n2QuarticColumnEpsilon810 epsilon A B C D E F G +
    n2QuarticColumnZeta810 zeta A B C D E F G +
    n2QuarticColumnEta810 eta A B C D E F G +
    n2QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_face5000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticChamberFace5000810 A B C D E F G +
        n2QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN2Quartic810_eq_chamberSplit,
    n2QuarticLoadFree810_eq_face5000_add_rest]
  simp only [n2QuarticChamberRest5000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 5001 (1 monomial, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace5001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 5001 (12 monomials). -/
def xiQuarticChamberRestLF5001810
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
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face5001_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace5001810 A B C D E F G + xiQuarticChamberRestLF5001810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace5001810, xiQuarticChamberRestLF5001810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest5001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF5001810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face5001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace5001810 A B C D E F G +
        xiQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face5001_add_rest]
  simp only [xiQuarticChamberRest5001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 5000 (1 monomial, top degree `D.natDegree + E.natDegree`). -/
def kappaQuarticChamberFace5000810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 5000 (5 monomials). -/
def kappaQuarticChamberRestLF5000810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face5000_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace5000810 A B C D E F G + kappaQuarticChamberRestLF5000810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace5000810, kappaQuarticChamberRestLF5000810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest5000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF5000810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face5000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace5000810 A B C D E F G +
        kappaQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face5000_add_rest]
  simp only [kappaQuarticChamberRest5000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₂` on unowned packet 5001 (1 monomial, top degree `D.natDegree + G.natDegree`). -/
def n2QuarticChamberFace5001810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₂` off packet 5001 (7 monomials). -/
def n2QuarticChamberRestLF5001810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem n2QuarticLoadFree810_eq_face5001_add_rest
    (A B C D E F G : k[X]) :
    n2QuarticLoadFree810 A B C D E F G =
      n2QuarticChamberFace5001810 A B C D E F G + n2QuarticChamberRestLF5001810 A B C D E F G := by
  simp only [n2QuarticLoadFree810, n2QuarticChamberFace5001810, n2QuarticChamberRestLF5001810]
  module

set_option maxHeartbeats 64000000 in
def n2QuarticChamberRest5001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticChamberRestLF5001810 A B C D E F G +
    n2QuarticColumnL810 l A B C D E F G +
    n2QuarticColumnBeta810 beta A B C D E F G +
    n2QuarticColumnGamma810 gamma A B C D E F G +
    n2QuarticColumnDelta810 delta A B C D E F G +
    n2QuarticColumnEpsilon810 epsilon A B C D E F G +
    n2QuarticColumnZeta810 zeta A B C D E F G +
    n2QuarticColumnEta810 eta A B C D E F G +
    n2QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_face5001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticChamberFace5001810 A B C D E F G +
        n2QuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN2Quartic810_eq_chamberSplit,
    n2QuarticLoadFree810_eq_face5001_add_rest]
  simp only [n2QuarticChamberRest5001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₆` on unowned packet 5000 (1 monomial, top degree `A.natDegree + F.natDegree + G.natDegree`). -/
def n6QuarticChamberFace5000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(25 / 48 : k)) • (A * F * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₆` off packet 5000 (27 monomials). -/
def n6QuarticChamberRestLF5000810
    (A B C D E F G : k[X]) : k[X] :=
  (145 / 12288 : k) • (A ^ 2 * B ^ 3 * C)
  + (93 / 8192 : k) • (A * B ^ 5)
  - (25 / 1536 : k) • (A ^ 2 * B ^ 2 * F)
  - (25 / 768 : k) • (A ^ 2 * B * D ^ 2)
  - (115 / 1536 : k) • (A * B ^ 3 * E)
  - (225 / 1024 : k) • (A * B ^ 2 * C * D)
  - (45 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (15 / 128 : k) • (A * B * C * G)
  + (25 / 96 : k) • (A * B * D * F)
  + (25 / 192 : k) • (A * B * E ^ 2)
  + (5 / 96 : k) • (A * C ^ 2 * F)
  + (95 / 384 : k) • (A * C * D * E)
  + (25 / 384 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem n6QuarticLoadFree810_eq_face5000_add_rest
    (A B C D E F G : k[X]) :
    n6QuarticLoadFree810 A B C D E F G =
      n6QuarticChamberFace5000810 A B C D E F G + n6QuarticChamberRestLF5000810 A B C D E F G := by
  simp only [n6QuarticLoadFree810, n6QuarticChamberFace5000810, n6QuarticChamberRestLF5000810]
  module

set_option maxHeartbeats 64000000 in
def n6QuarticChamberRest5000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n6QuarticChamberRestLF5000810 A B C D E F G +
    n6QuarticColumnL1810 l A B C D E F G +
    n6QuarticColumnL2810 l A B C D E F G +
    n6QuarticColumnBeta1810 beta A B C D E F G +
    n6QuarticColumnBeta2810 beta A B C D E F G +
    n6QuarticColumnGamma810 gamma A B C D E F G +
    n6QuarticColumnDelta810 delta A B C D E F G +
    n6QuarticColumnEpsilon810 epsilon A B C D E F G +
    n6QuarticColumnZeta810 zeta A B C D E F G +
    n6QuarticColumnEta810 eta A B C D E F G +
    n6QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN6Quartic810_eq_face5000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN6Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n6QuarticChamberFace5000810 A B C D E F G +
        n6QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN6Quartic810_eq_chamberSplit,
    n6QuarticLoadFree810_eq_face5000_add_rest]
  simp only [n6QuarticChamberRest5000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 5001 (1 monomial, top degree `B.natDegree + G.natDegree`). -/
def kappaQuarticChamberFace5001810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 5001 (5 monomials). -/
def kappaQuarticChamberRestLF5001810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face5001_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace5001810 A B C D E F G + kappaQuarticChamberRestLF5001810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace5001810, kappaQuarticChamberRestLF5001810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest5001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF5001810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face5001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace5001810 A B C D E F G +
        kappaQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face5001_add_rest]
  simp only [kappaQuarticChamberRest5001810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 5002 (1 monomial, top degree `E.natDegree + G.natDegree`). -/
def xiQuarticChamberFace5002810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 5002 (12 monomials). -/
def xiQuarticChamberRestLF5002810
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
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face5002_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace5002810 A B C D E F G + xiQuarticChamberRestLF5002810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace5002810, xiQuarticChamberRestLF5002810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest5002810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF5002810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face5002_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace5002810 A B C D E F G +
        xiQuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face5002_add_rest]
  simp only [xiQuarticChamberRest5002810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₂` on unowned packet 5002 (1 monomial, top degree `E.natDegree + F.natDegree`). -/
def n2QuarticChamberFace5002810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₂` off packet 5002 (7 monomials). -/
def n2QuarticChamberRestLF5002810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
theorem n2QuarticLoadFree810_eq_face5002_add_rest
    (A B C D E F G : k[X]) :
    n2QuarticLoadFree810 A B C D E F G =
      n2QuarticChamberFace5002810 A B C D E F G + n2QuarticChamberRestLF5002810 A B C D E F G := by
  simp only [n2QuarticLoadFree810, n2QuarticChamberFace5002810, n2QuarticChamberRestLF5002810]
  module

set_option maxHeartbeats 64000000 in
def n2QuarticChamberRest5002810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticChamberRestLF5002810 A B C D E F G +
    n2QuarticColumnL810 l A B C D E F G +
    n2QuarticColumnBeta810 beta A B C D E F G +
    n2QuarticColumnGamma810 gamma A B C D E F G +
    n2QuarticColumnDelta810 delta A B C D E F G +
    n2QuarticColumnEpsilon810 epsilon A B C D E F G +
    n2QuarticColumnZeta810 zeta A B C D E F G +
    n2QuarticColumnEta810 eta A B C D E F G +
    n2QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_face5002_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticChamberFace5002810 A B C D E F G +
        n2QuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN2Quartic810_eq_chamberSplit,
    n2QuarticLoadFree810_eq_face5002_add_rest]
  simp only [n2QuarticChamberRest5002810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₅` on unowned packet 5000 (1 monomial, top degree `F.natDegree + G.natDegree`). -/
def n5QuarticChamberFace5000810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₅` off packet 5000 (13 monomials). -/
def n5QuarticChamberRestLF5000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3

set_option maxHeartbeats 64000000 in
theorem n5QuarticLoadFree810_eq_face5000_add_rest
    (A B C D E F G : k[X]) :
    n5QuarticLoadFree810 A B C D E F G =
      n5QuarticChamberFace5000810 A B C D E F G + n5QuarticChamberRestLF5000810 A B C D E F G := by
  simp only [n5QuarticLoadFree810, n5QuarticChamberFace5000810, n5QuarticChamberRestLF5000810]
  module

set_option maxHeartbeats 64000000 in
def n5QuarticChamberRest5000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n5QuarticChamberRestLF5000810 A B C D E F G +
    n5QuarticColumnL1810 l A B C D E F G +
    n5QuarticColumnL2810 l A B C D E F G +
    n5QuarticColumnBeta810 beta A B C D E F G +
    n5QuarticColumnGamma810 gamma A B C D E F G +
    n5QuarticColumnDelta810 delta A B C D E F G +
    n5QuarticColumnEpsilon810 epsilon A B C D E F G +
    n5QuarticColumnZeta810 zeta A B C D E F G +
    n5QuarticColumnEta810 eta A B C D E F G +
    n5QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN5Quartic810_eq_face5000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN5Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticChamberFace5000810 A B C D E F G +
        n5QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN5Quartic810_eq_chamberSplit,
    n5QuarticLoadFree810_eq_face5000_add_rest]
  simp only [n5QuarticChamberRest5000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 5002 (1 monomial, top degree `C.natDegree + F.natDegree`). -/
def kappaQuarticChamberFace5002810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 5002 (5 monomials). -/
def kappaQuarticChamberRestLF5002810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face5002_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace5002810 A B C D E F G + kappaQuarticChamberRestLF5002810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace5002810, kappaQuarticChamberRestLF5002810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest5002810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF5002810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face5002_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace5002810 A B C D E F G +
        kappaQuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face5002_add_rest]
  simp only [kappaQuarticChamberRest5002810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 5003 (1 monomial, top degree `C.natDegree + 2 * D.natDegree`). -/
def xiQuarticChamberFace5003810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 5003 (12 monomials). -/
def xiQuarticChamberRestLF5003810
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
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face5003_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace5003810 A B C D E F G + xiQuarticChamberRestLF5003810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace5003810, xiQuarticChamberRestLF5003810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest5003810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF5003810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face5003_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace5003810 A B C D E F G +
        xiQuarticChamberRest5003810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face5003_add_rest]
  simp only [xiQuarticChamberRest5003810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₂` on unowned packet 5003 (1 monomial, top degree `B.natDegree + C.natDegree + E.natDegree`). -/
def n2QuarticChamberFace5003810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 64 : k)) • (B * C * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₂` off packet 5003 (7 monomials). -/
def n2QuarticChamberRestLF5003810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem n2QuarticLoadFree810_eq_face5003_add_rest
    (A B C D E F G : k[X]) :
    n2QuarticLoadFree810 A B C D E F G =
      n2QuarticChamberFace5003810 A B C D E F G + n2QuarticChamberRestLF5003810 A B C D E F G := by
  simp only [n2QuarticLoadFree810, n2QuarticChamberFace5003810, n2QuarticChamberRestLF5003810]
  module

set_option maxHeartbeats 64000000 in
def n2QuarticChamberRest5003810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticChamberRestLF5003810 A B C D E F G +
    n2QuarticColumnL810 l A B C D E F G +
    n2QuarticColumnBeta810 beta A B C D E F G +
    n2QuarticColumnGamma810 gamma A B C D E F G +
    n2QuarticColumnDelta810 delta A B C D E F G +
    n2QuarticColumnEpsilon810 epsilon A B C D E F G +
    n2QuarticColumnZeta810 zeta A B C D E F G +
    n2QuarticColumnEta810 eta A B C D E F G +
    n2QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_face5003_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticChamberFace5003810 A B C D E F G +
        n2QuarticChamberRest5003810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN2Quartic810_eq_chamberSplit,
    n2QuarticLoadFree810_eq_face5003_add_rest]
  simp only [n2QuarticChamberRest5003810]
  ring


end QuarticChamberUnownedPackets810

end Max11DegreeRoutes
