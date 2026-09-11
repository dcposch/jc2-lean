import Grok810ScaleZeroQuarticChamberFacesPart0Scratch
import Grok810ScaleZeroQuarticChamberInfraN4Scratch
import Grok810ScaleZeroQuarticChamberInfraN2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems9Part2Scratch

/-! # Tower face packets, part 2/2

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

section QuarticChamberTowerPackets2810

set_option maxHeartbeats 64000000 in
/-- Face of `π` on unowned packet 9008 (5 monomial, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace9008810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
  - (5 / 16 : k) • (A * F ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 9008 (16 monomials). -/
def piQuarticChamberRestLF9008810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
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
theorem piQuarticLoadFree810_eq_face9008_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace9008810 A B C D E F G + piQuarticChamberRestLF9008810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace9008810, piQuarticChamberRestLF9008810]
  all_goals module

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest9008810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF9008810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face9008_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace9008810 A B C D E F G +
        piQuarticChamberRest9008810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face9008_add_rest]
  simp only [piQuarticChamberRest9008810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 9004 (3 monomial, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace9004810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 9004 (3 monomials). -/
def kappaQuarticChamberRestLF9004810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face9004_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace9004810 A B C D E F G + kappaQuarticChamberRestLF9004810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace9004810, kappaQuarticChamberRestLF9004810]
  all_goals module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest9004810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF9004810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face9004_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace9004810 A B C D E F G +
        kappaQuarticChamberRest9004810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face9004_add_rest]
  simp only [kappaQuarticChamberRest9004810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₂` on unowned packet 9007 (3 monomial, top degree `A.natDegree + 2 * B.natDegree + D.natDegree`). -/
def n2QuarticChamberFace9007810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₂` off packet 9007 (5 monomials). -/
def n2QuarticChamberRestLF9007810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem n2QuarticLoadFree810_eq_face9007_add_rest
    (A B C D E F G : k[X]) :
    n2QuarticLoadFree810 A B C D E F G =
      n2QuarticChamberFace9007810 A B C D E F G + n2QuarticChamberRestLF9007810 A B C D E F G := by
  simp only [n2QuarticLoadFree810, n2QuarticChamberFace9007810, n2QuarticChamberRestLF9007810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n2QuarticChamberRest9007810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticChamberRestLF9007810 A B C D E F G +
    n2QuarticColumnL810 l A B C D E F G +
    n2QuarticColumnBeta810 beta A B C D E F G +
    n2QuarticColumnGamma810 gamma A B C D E F G +
    n2QuarticColumnDelta810 delta A B C D E F G +
    n2QuarticColumnEpsilon810 epsilon A B C D E F G +
    n2QuarticColumnZeta810 zeta A B C D E F G +
    n2QuarticColumnEta810 eta A B C D E F G +
    n2QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_face9007_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticChamberFace9007810 A B C D E F G +
        n2QuarticChamberRest9007810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN2Quartic810_eq_chamberSplit,
    n2QuarticLoadFree810_eq_face9007_add_rest]
  simp only [n2QuarticChamberRest9007810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₄` on unowned packet 9001 (3 monomial, top degree `2 * A.natDegree + 2 * C.natDegree + D.natDegree`). -/
def n4QuarticChamberFace9001810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A ^ 2 * C ^ 2 * D)
  + (5 / 256 : k) • (A ^ 2 * D * G)
  + (5 / 256 : k) • (A ^ 2 * E * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₄` off packet 9001 (30 monomials). -/
def n4QuarticChamberRestLF9001810
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
theorem n4QuarticLoadFree810_eq_face9001_add_rest
    (A B C D E F G : k[X]) :
    n4QuarticLoadFree810 A B C D E F G =
      n4QuarticChamberFace9001810 A B C D E F G + n4QuarticChamberRestLF9001810 A B C D E F G := by
  simp only [n4QuarticLoadFree810, n4QuarticChamberFace9001810, n4QuarticChamberRestLF9001810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n4QuarticChamberRest9001810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n4QuarticChamberRestLF9001810 A B C D E F G +
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
theorem degreeZeroN4Quartic810_eq_face9001_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n4QuarticChamberFace9001810 A B C D E F G +
        n4QuarticChamberRest9001810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN4Quartic810_eq_chamberSplit,
    n4QuarticLoadFree810_eq_face9001_add_rest]
  simp only [n4QuarticChamberRest9001810]
  ring


end QuarticChamberTowerPackets2810

end Max11DegreeRoutes
