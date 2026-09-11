import Grok810ScaleZeroQuarticChamberNuFacesScratch
import Grok810ScaleZeroQuarticChamberInfraN5Scratch
import Grok810ScaleZeroQuarticChamberInfraPrimitiveScratch
import Grok810ScaleZeroQuarticChamberInfraOmicronScratch
import Grok810ScaleZeroQuarticChamberInfraN7Scratch
import Grok810ScaleZeroQuarticChamberInfraN6Scratch
import Grok810ScaleZeroQuarticChamberInfraN4Scratch
import Grok810ScaleZeroQuarticChamberInfraN3Scratch
import Grok810ScaleZeroQuarticChamberInfraN2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems9Part101Scratch

/-! # UnownedTree face packets, part 1/2

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

section QuarticChamberUnownedTreePackets1810

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 9500 (1 monomial, top degree `2 * F.natDegree`). -/
def xiQuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 9500 (12 monomials). -/
def xiQuarticChamberRestLF9500810
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

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace9500810 A B C D E F G + xiQuarticChamberRestLF9500810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace9500810, xiQuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF9500810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace9500810 A B C D E F G +
        xiQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face9500_add_rest]
  simp only [xiQuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₆` on unowned packet 9500 (1 monomial, top degree `A.natDegree + F.natDegree + G.natDegree`). -/
def n6QuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(25 / 48 : k)) • (A * F * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₆` off packet 9500 (27 monomials). -/
def n6QuarticChamberRestLF9500810
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
theorem n6QuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    n6QuarticLoadFree810 A B C D E F G =
      n6QuarticChamberFace9500810 A B C D E F G + n6QuarticChamberRestLF9500810 A B C D E F G := by
  simp only [n6QuarticLoadFree810, n6QuarticChamberFace9500810, n6QuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n6QuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n6QuarticChamberRestLF9500810 A B C D E F G +
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
theorem degreeZeroN6Quartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN6Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n6QuarticChamberFace9500810 A B C D E F G +
        n6QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN6Quartic810_eq_chamberSplit,
    n6QuarticLoadFree810_eq_face9500_add_rest]
  simp only [n6QuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₄` on unowned packet 9500 (1 monomial, top degree `A.natDegree + F.natDegree + G.natDegree`). -/
def n4QuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 8 : k)) • (A * F * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₄` off packet 9500 (32 monomials). -/
def n4QuarticChamberRestLF9500810
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
  + (5 / 256 : k) • (A ^ 2 * D * G)
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
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem n4QuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    n4QuarticLoadFree810 A B C D E F G =
      n4QuarticChamberFace9500810 A B C D E F G + n4QuarticChamberRestLF9500810 A B C D E F G := by
  simp only [n4QuarticLoadFree810, n4QuarticChamberFace9500810, n4QuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n4QuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n4QuarticChamberRestLF9500810 A B C D E F G +
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
theorem degreeZeroN4Quartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n4QuarticChamberFace9500810 A B C D E F G +
        n4QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN4Quartic810_eq_chamberSplit,
    n4QuarticLoadFree810_eq_face9500_add_rest]
  simp only [n4QuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 9500 (1 monomial, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 9500 (9 monomials). -/
def muQuarticChamberRestLF9500810
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

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace9500810 A B C D E F G + muQuarticChamberRestLF9500810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace9500810, muQuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF9500810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace9500810 A B C D E F G +
        muQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face9500_add_rest]
  simp only [muQuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₃` on unowned packet 9500 (1 monomial, top degree `A.natDegree + D.natDegree + G.natDegree`). -/
def n3QuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 256 : k)) • (A * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₃` off packet 9500 (18 monomials). -/
def n3QuarticChamberRestLF9500810
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
  - (15 / 256 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem n3QuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    n3QuarticLoadFree810 A B C D E F G =
      n3QuarticChamberFace9500810 A B C D E F G + n3QuarticChamberRestLF9500810 A B C D E F G := by
  simp only [n3QuarticLoadFree810, n3QuarticChamberFace9500810, n3QuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n3QuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n3QuarticChamberRestLF9500810 A B C D E F G +
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
theorem degreeZeroN3Quartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n3QuarticChamberFace9500810 A B C D E F G +
        n3QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN3Quartic810_eq_chamberSplit,
    n3QuarticLoadFree810_eq_face9500_add_rest]
  simp only [n3QuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₄` on unowned packet 9501 (1 monomial, top degree `2 * A.natDegree + D.natDegree + G.natDegree`). -/
def n4QuarticChamberFace9501810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 256 : k) • (A ^ 2 * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₄` off packet 9501 (32 monomials). -/
def n4QuarticChamberRestLF9501810
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
theorem n4QuarticLoadFree810_eq_face9501_add_rest
    (A B C D E F G : k[X]) :
    n4QuarticLoadFree810 A B C D E F G =
      n4QuarticChamberFace9501810 A B C D E F G + n4QuarticChamberRestLF9501810 A B C D E F G := by
  simp only [n4QuarticLoadFree810, n4QuarticChamberFace9501810, n4QuarticChamberRestLF9501810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n4QuarticChamberRest9501810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n4QuarticChamberRestLF9501810 A B C D E F G +
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
theorem degreeZeroN4Quartic810_eq_face9501_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n4QuarticChamberFace9501810 A B C D E F G +
        n4QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN4Quartic810_eq_chamberSplit,
    n4QuarticLoadFree810_eq_face9501_add_rest]
  simp only [n4QuarticChamberRest9501810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 9500 (1 monomial, top degree `2 * G.natDegree`). -/
def piQuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 9500 (20 monomials). -/
def piQuarticChamberRestLF9500810
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
theorem piQuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace9500810 A B C D E F G + piQuarticChamberRestLF9500810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace9500810, piQuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF9500810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace9500810 A B C D E F G +
        piQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face9500_add_rest]
  simp only [piQuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₂` on unowned packet 9500 (1 monomial, top degree `D.natDegree + G.natDegree`). -/
def n2QuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₂` off packet 9500 (7 monomials). -/
def n2QuarticChamberRestLF9500810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem n2QuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    n2QuarticLoadFree810 A B C D E F G =
      n2QuarticChamberFace9500810 A B C D E F G + n2QuarticChamberRestLF9500810 A B C D E F G := by
  simp only [n2QuarticLoadFree810, n2QuarticChamberFace9500810, n2QuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n2QuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticChamberRestLF9500810 A B C D E F G +
    n2QuarticColumnL810 l A B C D E F G +
    n2QuarticColumnBeta810 beta A B C D E F G +
    n2QuarticColumnGamma810 gamma A B C D E F G +
    n2QuarticColumnDelta810 delta A B C D E F G +
    n2QuarticColumnEpsilon810 epsilon A B C D E F G +
    n2QuarticColumnZeta810 zeta A B C D E F G +
    n2QuarticColumnEta810 eta A B C D E F G +
    n2QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticChamberFace9500810 A B C D E F G +
        n2QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN2Quartic810_eq_chamberSplit,
    n2QuarticLoadFree810_eq_face9500_add_rest]
  simp only [n2QuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 9500 (4 monomial, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 9500 (2 monomials). -/
def kappaQuarticChamberRestLF9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace9500810 A B C D E F G + kappaQuarticChamberRestLF9500810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace9500810, kappaQuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF9500810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace9500810 A B C D E F G +
        kappaQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face9500_add_rest]
  simp only [kappaQuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 9501 (4 monomial, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace9501810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 9501 (6 monomials). -/
def muQuarticChamberRestLF9501810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face9501_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace9501810 A B C D E F G + muQuarticChamberRestLF9501810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace9501810, muQuarticChamberRestLF9501810]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest9501810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF9501810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face9501_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace9501810 A B C D E F G +
        muQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face9501_add_rest]
  simp only [muQuarticChamberRest9501810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on unowned packet 9500 (4 monomial, top degree `2 * A.natDegree + 3 * B.natDegree`). -/
def nuQuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 9500 (9 monomials). -/
def nuQuarticChamberRestLF9500810
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
theorem nuQuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace9500810 A B C D E F G + nuQuarticChamberRestLF9500810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace9500810, nuQuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def nuQuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  nuQuarticChamberRestLF9500810 A B C D E F G +
    nuQuarticColumnL810 l A B C D E F G +
    nuQuarticColumnBeta810 beta A B C D E F G +
    nuQuarticColumnGamma810 gamma A B C D E F G +
    nuQuarticColumnDelta810 delta A B C D E F G +
    nuQuarticColumnEpsilon810 epsilon A B C D E F G +
    nuQuarticColumnZeta810 zeta A B C D E F G +
    nuQuarticColumnEta810 eta A B C D E F G +
    nuQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticChamberFace9500810 A B C D E F G +
        nuQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroNuQuartic810_eq_chamberSplit,
    nuQuarticLoadFree810_eq_face9500_add_rest]
  simp only [nuQuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ο` on unowned packet 9500 (4 monomial, top degree `3 * A.natDegree + 3 * B.natDegree`). -/
def omicronQuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ο` off packet 9500 (20 monomials). -/
def omicronQuarticChamberRestLF9500810
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
theorem omicronQuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    omicronQuarticLoadFree810 A B C D E F G =
      omicronQuarticChamberFace9500810 A B C D E F G + omicronQuarticChamberRestLF9500810 A B C D E F G := by
  simp only [omicronQuarticLoadFree810, omicronQuarticChamberFace9500810, omicronQuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def omicronQuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  omicronQuarticChamberRestLF9500810 A B C D E F G +
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
theorem degreeZeroOmicronQuartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticChamberFace9500810 A B C D E F G +
        omicronQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroOmicronQuartic810_eq_chamberSplit,
    omicronQuarticLoadFree810_eq_face9500_add_rest]
  simp only [omicronQuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 9501 (8 monomial, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace9501810
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
/-- Load-free rest of `π` off packet 9501 (13 monomials). -/
def piQuarticChamberRestLF9501810
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
theorem piQuarticLoadFree810_eq_face9501_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace9501810 A B C D E F G + piQuarticChamberRestLF9501810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace9501810, piQuarticChamberRestLF9501810]
  all_goals module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest9501810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF9501810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face9501_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace9501810 A B C D E F G +
        piQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face9501_add_rest]
  simp only [piQuarticChamberRest9501810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `Π` on unowned packet 9500 (4 monomial, top degree `4 * A.natDegree + 3 * B.natDegree`). -/
def primitiveQuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `Π` off packet 9500 (33 monomials). -/
def primitiveQuarticChamberRestLF9500810
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
theorem primitiveQuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    primitiveQuarticLoadFree810 A B C D E F G =
      primitiveQuarticChamberFace9500810 A B C D E F G + primitiveQuarticChamberRestLF9500810 A B C D E F G := by
  simp only [primitiveQuarticLoadFree810, primitiveQuarticChamberFace9500810, primitiveQuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def primitiveQuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  primitiveQuarticChamberRestLF9500810 A B C D E F G +
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
theorem degreeZeroPrimitiveQuartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticChamberFace9500810 A B C D E F G +
        primitiveQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPrimitiveQuartic810_eq_chamberSplit,
    primitiveQuarticLoadFree810_eq_face9500_add_rest]
  simp only [primitiveQuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 9501 (5 monomial, top degree `A.natDegree + 4 * B.natDegree`). -/
def xiQuarticChamberFace9501810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 9501 (8 monomials). -/
def xiQuarticChamberRestLF9501810
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
theorem xiQuarticLoadFree810_eq_face9501_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace9501810 A B C D E F G + xiQuarticChamberRestLF9501810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace9501810, xiQuarticChamberRestLF9501810]
  all_goals module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest9501810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF9501810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face9501_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace9501810 A B C D E F G +
        xiQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face9501_add_rest]
  simp only [xiQuarticChamberRest9501810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₂` on unowned packet 9501 (2 monomial, top degree `3 * B.natDegree + C.natDegree`). -/
def n2QuarticChamberFace9501810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₂` off packet 9501 (6 monomials). -/
def n2QuarticChamberRestLF9501810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem n2QuarticLoadFree810_eq_face9501_add_rest
    (A B C D E F G : k[X]) :
    n2QuarticLoadFree810 A B C D E F G =
      n2QuarticChamberFace9501810 A B C D E F G + n2QuarticChamberRestLF9501810 A B C D E F G := by
  simp only [n2QuarticLoadFree810, n2QuarticChamberFace9501810, n2QuarticChamberRestLF9501810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n2QuarticChamberRest9501810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticChamberRestLF9501810 A B C D E F G +
    n2QuarticColumnL810 l A B C D E F G +
    n2QuarticColumnBeta810 beta A B C D E F G +
    n2QuarticColumnGamma810 gamma A B C D E F G +
    n2QuarticColumnDelta810 delta A B C D E F G +
    n2QuarticColumnEpsilon810 epsilon A B C D E F G +
    n2QuarticColumnZeta810 zeta A B C D E F G +
    n2QuarticColumnEta810 eta A B C D E F G +
    n2QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_face9501_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticChamberFace9501810 A B C D E F G +
        n2QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN2Quartic810_eq_chamberSplit,
    n2QuarticLoadFree810_eq_face9501_add_rest]
  simp only [n2QuarticChamberRest9501810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₃` on unowned packet 9501 (6 monomial, top degree `A.natDegree + 3 * B.natDegree + C.natDegree`). -/
def n3QuarticChamberFace9501810
    (A B C D E F G : k[X]) : k[X] :=
  (-(175 / 8192 : k)) • (A * B ^ 3 * C)
  + (65 / 2048 : k) • (A * B ^ 2 * F)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 64 : k) • (C ^ 2 * F)
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₃` off packet 9501 (13 monomials). -/
def n3QuarticChamberRestLF9501810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 8192 : k)) • (A ^ 2 * B ^ 2 * D)
  - (21 / 4096 : k) • B ^ 5
  + (45 / 1024 : k) • (A * B * C * E)
  + (85 / 2048 : k) • (A * B * D ^ 2)
  + (45 / 2048 : k) • (A * C ^ 2 * D)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  - (15 / 256 : k) • (A * D * G)
  - (15 / 256 : k) • (A * E * F)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3

set_option maxHeartbeats 64000000 in
theorem n3QuarticLoadFree810_eq_face9501_add_rest
    (A B C D E F G : k[X]) :
    n3QuarticLoadFree810 A B C D E F G =
      n3QuarticChamberFace9501810 A B C D E F G + n3QuarticChamberRestLF9501810 A B C D E F G := by
  simp only [n3QuarticLoadFree810, n3QuarticChamberFace9501810, n3QuarticChamberRestLF9501810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n3QuarticChamberRest9501810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n3QuarticChamberRestLF9501810 A B C D E F G +
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
theorem degreeZeroN3Quartic810_eq_face9501_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n3QuarticChamberFace9501810 A B C D E F G +
        n3QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN3Quartic810_eq_chamberSplit,
    n3QuarticLoadFree810_eq_face9501_add_rest]
  simp only [n3QuarticChamberRest9501810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₄` on unowned packet 9502 (6 monomial, top degree `2 * A.natDegree + 3 * B.natDegree + C.natDegree`). -/
def n4QuarticChamberFace9502810
    (A B C D E F G : k[X]) : k[X] :=
  (155 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  - (55 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  - (15 / 256 : k) • (A * B * C ^ 3)
  + (5 / 32 : k) • (A * B * C * G)
  + (5 / 64 : k) • (A * C ^ 2 * F)
  - (5 / 8 : k) • (A * F * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₄` off packet 9502 (27 monomials). -/
def n4QuarticChamberRestLF9502810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 8192 : k) • (A ^ 3 * B ^ 2 * D)
  + (107 / 8192 : k) • (A * B ^ 5)
  - (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (95 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (45 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 512 : k) • (A * B ^ 2 * C * D)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (5 / 256 : k) • (A ^ 2 * D * G)
  + (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 16 : k) • (A * B * D * F)
  + (5 / 32 : k) • (A * B * E ^ 2)
  + (5 / 16 : k) • (A * C * D * E)
  + (5 / 64 : k) • (A * D ^ 3)
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
theorem n4QuarticLoadFree810_eq_face9502_add_rest
    (A B C D E F G : k[X]) :
    n4QuarticLoadFree810 A B C D E F G =
      n4QuarticChamberFace9502810 A B C D E F G + n4QuarticChamberRestLF9502810 A B C D E F G := by
  simp only [n4QuarticLoadFree810, n4QuarticChamberFace9502810, n4QuarticChamberRestLF9502810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n4QuarticChamberRest9502810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n4QuarticChamberRestLF9502810 A B C D E F G +
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
theorem degreeZeroN4Quartic810_eq_face9502_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n4QuarticChamberFace9502810 A B C D E F G +
        n4QuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN4Quartic810_eq_chamberSplit,
    n4QuarticLoadFree810_eq_face9502_add_rest]
  simp only [n4QuarticChamberRest9502810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₅` on unowned packet 9500 (6 monomial, top degree `A.natDegree + 3 * B.natDegree + C.natDegree`). -/
def n5QuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 64 : k) • (C ^ 2 * F)
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₅` off packet 9500 (8 monomials). -/
def n5QuarticChamberRestLF9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(21 / 4096 : k)) • B ^ 5
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3

set_option maxHeartbeats 64000000 in
theorem n5QuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    n5QuarticLoadFree810 A B C D E F G =
      n5QuarticChamberFace9500810 A B C D E F G + n5QuarticChamberRestLF9500810 A B C D E F G := by
  simp only [n5QuarticLoadFree810, n5QuarticChamberFace9500810, n5QuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n5QuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n5QuarticChamberRestLF9500810 A B C D E F G +
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
theorem degreeZeroN5Quartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN5Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticChamberFace9500810 A B C D E F G +
        n5QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN5Quartic810_eq_chamberSplit,
    n5QuarticLoadFree810_eq_face9500_add_rest]
  simp only [n5QuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₆` on unowned packet 9501 (6 monomial, top degree `2 * A.natDegree + 3 * B.natDegree + C.natDegree`). -/
def n6QuarticChamberFace9501810
    (A B C D E F G : k[X]) : k[X] :=
  (145 / 12288 : k) • (A ^ 2 * B ^ 3 * C)
  - (25 / 1536 : k) • (A ^ 2 * B ^ 2 * F)
  - (45 / 1024 : k) • (A * B * C ^ 3)
  + (15 / 128 : k) • (A * B * C * G)
  + (5 / 96 : k) • (A * C ^ 2 * F)
  - (25 / 48 : k) • (A * F * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₆` off packet 9501 (22 monomials). -/
def n6QuarticChamberRestLF9501810
    (A B C D E F G : k[X]) : k[X] :=
  (93 / 8192 : k) • (A * B ^ 5)
  - (25 / 768 : k) • (A ^ 2 * B * D ^ 2)
  - (115 / 1536 : k) • (A * B ^ 3 * E)
  - (225 / 1024 : k) • (A * B ^ 2 * C * D)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (25 / 96 : k) • (A * B * D * F)
  + (25 / 192 : k) • (A * B * E ^ 2)
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
theorem n6QuarticLoadFree810_eq_face9501_add_rest
    (A B C D E F G : k[X]) :
    n6QuarticLoadFree810 A B C D E F G =
      n6QuarticChamberFace9501810 A B C D E F G + n6QuarticChamberRestLF9501810 A B C D E F G := by
  simp only [n6QuarticLoadFree810, n6QuarticChamberFace9501810, n6QuarticChamberRestLF9501810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n6QuarticChamberRest9501810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n6QuarticChamberRestLF9501810 A B C D E F G +
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
theorem degreeZeroN6Quartic810_eq_face9501_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN6Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n6QuarticChamberFace9501810 A B C D E F G +
        n6QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN6Quartic810_eq_chamberSplit,
    n6QuarticLoadFree810_eq_face9501_add_rest]
  simp only [n6QuarticChamberRest9501810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₇` on unowned packet 9500 (4 monomial, top degree `2 * A.natDegree + 3 * B.natDegree + C.natDegree`). -/
def n7QuarticChamberFace9500810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 2 * B ^ 3 * C)
  + (15 / 512 : k) • (A * B * C ^ 3)
  - (5 / 64 : k) • (A * B * C * G)
  - (5 / 64 : k) • (A * C ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₇` off packet 9500 (17 monomials). -/
def n7QuarticChamberRestLF9500810
    (A B C D E F G : k[X]) : k[X] :=
  (23 / 8192 : k) • (A * B ^ 5)
  - (5 / 512 : k) • (A * B ^ 3 * E)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 64 : k) • (A * C * D * E)
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
theorem n7QuarticLoadFree810_eq_face9500_add_rest
    (A B C D E F G : k[X]) :
    n7QuarticLoadFree810 A B C D E F G =
      n7QuarticChamberFace9500810 A B C D E F G + n7QuarticChamberRestLF9500810 A B C D E F G := by
  simp only [n7QuarticLoadFree810, n7QuarticChamberFace9500810, n7QuarticChamberRestLF9500810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n7QuarticChamberRest9500810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n7QuarticChamberRestLF9500810 A B C D E F G +
    n7QuarticColumnL1810 l A B C D E F G +
    n7QuarticColumnL2810 l A B C D E F G +
    n7QuarticColumnBeta1810 beta A B C D E F G +
    n7QuarticColumnBeta2810 beta A B C D E F G +
    n7QuarticColumnGamma810 gamma A B C D E F G +
    n7QuarticColumnDelta810 delta A B C D E F G +
    n7QuarticColumnEpsilon810 epsilon A B C D E F G +
    n7QuarticColumnZeta810 zeta A B C D E F G +
    n7QuarticColumnEta810 eta A B C D E F G +
    n7QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN7Quartic810_eq_face9500_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN7Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticChamberFace9500810 A B C D E F G +
        n7QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN7Quartic810_eq_chamberSplit,
    n7QuarticLoadFree810_eq_face9500_add_rest]
  simp only [n7QuarticChamberRest9500810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 9501 (1 monomial, top degree `D.natDegree + E.natDegree`). -/
def kappaQuarticChamberFace9501810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 9501 (5 monomials). -/
def kappaQuarticChamberRestLF9501810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face9501_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace9501810 A B C D E F G + kappaQuarticChamberRestLF9501810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace9501810, kappaQuarticChamberRestLF9501810]
  all_goals module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest9501810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF9501810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face9501_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace9501810 A B C D E F G +
        kappaQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face9501_add_rest]
  simp only [kappaQuarticChamberRest9501810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 9502 (1 monomial, top degree `E.natDegree + G.natDegree`). -/
def xiQuarticChamberFace9502810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 9502 (12 monomials). -/
def xiQuarticChamberRestLF9502810
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
theorem xiQuarticLoadFree810_eq_face9502_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace9502810 A B C D E F G + xiQuarticChamberRestLF9502810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace9502810, xiQuarticChamberRestLF9502810]
  all_goals module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest9502810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF9502810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face9502_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace9502810 A B C D E F G +
        xiQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face9502_add_rest]
  simp only [xiQuarticChamberRest9502810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₃` on unowned packet 9502 (2 monomial, top degree `A.natDegree + D.natDegree + G.natDegree`). -/
def n3QuarticChamberFace9502810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 256 : k)) • (A * D * G)
  - (15 / 256 : k) • (A * E * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₃` off packet 9502 (17 monomials). -/
def n3QuarticChamberRestLF9502810
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
theorem n3QuarticLoadFree810_eq_face9502_add_rest
    (A B C D E F G : k[X]) :
    n3QuarticLoadFree810 A B C D E F G =
      n3QuarticChamberFace9502810 A B C D E F G + n3QuarticChamberRestLF9502810 A B C D E F G := by
  simp only [n3QuarticLoadFree810, n3QuarticChamberFace9502810, n3QuarticChamberRestLF9502810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n3QuarticChamberRest9502810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n3QuarticChamberRestLF9502810 A B C D E F G +
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
theorem degreeZeroN3Quartic810_eq_face9502_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n3QuarticChamberFace9502810 A B C D E F G +
        n3QuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN3Quartic810_eq_chamberSplit,
    n3QuarticLoadFree810_eq_face9502_add_rest]
  simp only [n3QuarticChamberRest9502810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₄` on unowned packet 9503 (2 monomial, top degree `2 * A.natDegree + D.natDegree + G.natDegree`). -/
def n4QuarticChamberFace9503810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 256 : k) • (A ^ 2 * D * G)
  + (5 / 256 : k) • (A ^ 2 * E * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₄` off packet 9503 (31 monomials). -/
def n4QuarticChamberRestLF9503810
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
theorem n4QuarticLoadFree810_eq_face9503_add_rest
    (A B C D E F G : k[X]) :
    n4QuarticLoadFree810 A B C D E F G =
      n4QuarticChamberFace9503810 A B C D E F G + n4QuarticChamberRestLF9503810 A B C D E F G := by
  simp only [n4QuarticLoadFree810, n4QuarticChamberFace9503810, n4QuarticChamberRestLF9503810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n4QuarticChamberRest9503810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n4QuarticChamberRestLF9503810 A B C D E F G +
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
theorem degreeZeroN4Quartic810_eq_face9503_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n4QuarticChamberFace9503810 A B C D E F G +
        n4QuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN4Quartic810_eq_chamberSplit,
    n4QuarticLoadFree810_eq_face9503_add_rest]
  simp only [n4QuarticChamberRest9503810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 9502 (2 monomial, top degree `A.natDegree + 2 * F.natDegree`). -/
def piQuarticChamberFace9502810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (A * F ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 9502 (19 monomials). -/
def piQuarticChamberRestLF9502810
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
theorem piQuarticLoadFree810_eq_face9502_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace9502810 A B C D E F G + piQuarticChamberRestLF9502810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace9502810, piQuarticChamberRestLF9502810]
  all_goals module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest9502810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF9502810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face9502_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace9502810 A B C D E F G +
        piQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face9502_add_rest]
  simp only [piQuarticChamberRest9502810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 9503 (2 monomial, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace9503810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 9503 (11 monomials). -/
def xiQuarticChamberRestLF9503810
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
theorem xiQuarticLoadFree810_eq_face9503_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace9503810 A B C D E F G + xiQuarticChamberRestLF9503810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace9503810, xiQuarticChamberRestLF9503810]
  all_goals module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest9503810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF9503810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face9503_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace9503810 A B C D E F G +
        xiQuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face9503_add_rest]
  simp only [xiQuarticChamberRest9503810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 9504 (1 monomial, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace9504810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 9504 (12 monomials). -/
def xiQuarticChamberRestLF9504810
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
theorem xiQuarticLoadFree810_eq_face9504_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace9504810 A B C D E F G + xiQuarticChamberRestLF9504810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace9504810, xiQuarticChamberRestLF9504810]
  all_goals module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest9504810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF9504810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face9504_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace9504810 A B C D E F G +
        xiQuarticChamberRest9504810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face9504_add_rest]
  simp only [xiQuarticChamberRest9504810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 9502 (1 monomial, top degree `2 * E.natDegree`). -/
def muQuarticChamberFace9502810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 9502 (9 monomials). -/
def muQuarticChamberRestLF9502810
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
theorem muQuarticLoadFree810_eq_face9502_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace9502810 A B C D E F G + muQuarticChamberRestLF9502810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace9502810, muQuarticChamberRestLF9502810]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest9502810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF9502810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face9502_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace9502810 A B C D E F G +
        muQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face9502_add_rest]
  simp only [muQuarticChamberRest9502810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 9502 (4 monomial, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace9502810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 9502 (2 monomials). -/
def kappaQuarticChamberRestLF9502810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face9502_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace9502810 A B C D E F G + kappaQuarticChamberRestLF9502810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace9502810, kappaQuarticChamberRestLF9502810]
  all_goals module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest9502810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF9502810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face9502_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace9502810 A B C D E F G +
        kappaQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face9502_add_rest]
  simp only [kappaQuarticChamberRest9502810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 9503 (3 monomial, top degree `3 * C.natDegree`). -/
def muQuarticChamberFace9503810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 9503 (7 monomials). -/
def muQuarticChamberRestLF9503810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face9503_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace9503810 A B C D E F G + muQuarticChamberRestLF9503810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace9503810, muQuarticChamberRestLF9503810]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest9503810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF9503810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face9503_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace9503810 A B C D E F G +
        muQuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face9503_add_rest]
  simp only [muQuarticChamberRest9503810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₂` on unowned packet 9502 (4 monomial, top degree `B.natDegree + C.natDegree + E.natDegree`). -/
def n2QuarticChamberFace9502810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 64 : k)) • (B * C * E)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₂` off packet 9502 (4 monomials). -/
def n2QuarticChamberRestLF9502810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 128 : k) • (B * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem n2QuarticLoadFree810_eq_face9502_add_rest
    (A B C D E F G : k[X]) :
    n2QuarticLoadFree810 A B C D E F G =
      n2QuarticChamberFace9502810 A B C D E F G + n2QuarticChamberRestLF9502810 A B C D E F G := by
  simp only [n2QuarticLoadFree810, n2QuarticChamberFace9502810, n2QuarticChamberRestLF9502810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n2QuarticChamberRest9502810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticChamberRestLF9502810 A B C D E F G +
    n2QuarticColumnL810 l A B C D E F G +
    n2QuarticColumnBeta810 beta A B C D E F G +
    n2QuarticColumnGamma810 gamma A B C D E F G +
    n2QuarticColumnDelta810 delta A B C D E F G +
    n2QuarticColumnEpsilon810 epsilon A B C D E F G +
    n2QuarticColumnZeta810 zeta A B C D E F G +
    n2QuarticColumnEta810 eta A B C D E F G +
    n2QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_face9502_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticChamberFace9502810 A B C D E F G +
        n2QuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN2Quartic810_eq_chamberSplit,
    n2QuarticLoadFree810_eq_face9502_add_rest]
  simp only [n2QuarticChamberRest9502810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₃` on unowned packet 9503 (4 monomial, top degree `A.natDegree + B.natDegree + C.natDegree + E.natDegree`). -/
def n3QuarticChamberFace9503810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (A * B * C * E)
  + (45 / 2048 : k) • (A * C ^ 2 * D)
  - (15 / 256 : k) • (A * D * G)
  - (15 / 256 : k) • (A * E * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₃` off packet 9503 (15 monomials). -/
def n3QuarticChamberRestLF9503810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 8192 : k)) • (A ^ 2 * B ^ 2 * D)
  - (175 / 8192 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (65 / 2048 : k) • (A * B ^ 2 * F)
  + (85 / 2048 : k) • (A * B * D ^ 2)
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
theorem n3QuarticLoadFree810_eq_face9503_add_rest
    (A B C D E F G : k[X]) :
    n3QuarticLoadFree810 A B C D E F G =
      n3QuarticChamberFace9503810 A B C D E F G + n3QuarticChamberRestLF9503810 A B C D E F G := by
  simp only [n3QuarticLoadFree810, n3QuarticChamberFace9503810, n3QuarticChamberRestLF9503810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n3QuarticChamberRest9503810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n3QuarticChamberRestLF9503810 A B C D E F G +
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
theorem degreeZeroN3Quartic810_eq_face9503_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n3QuarticChamberFace9503810 A B C D E F G +
        n3QuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN3Quartic810_eq_chamberSplit,
    n3QuarticLoadFree810_eq_face9503_add_rest]
  simp only [n3QuarticChamberRest9503810]
  ring


end QuarticChamberUnownedTreePackets1810

end Max11DegreeRoutes
