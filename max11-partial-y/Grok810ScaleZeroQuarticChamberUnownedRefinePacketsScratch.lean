import Grok810ScaleZeroQuarticChamberFacesPart0Scratch
import Grok810ScaleZeroQuarticChamberInfraN3Scratch
import Grok810ScaleZeroQuarticChamberInfraN2Scratch

/-! # UnownedRefine face packets, part 1/1

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

section QuarticChamberUnownedRefinePackets810

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on unowned packet 8000 (1 monomial, top degree `D.natDegree + E.natDegree`). -/
def kappaQuarticChamberFace8000810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 8000 (5 monomials). -/
def kappaQuarticChamberRestLF8000810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face8000_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace8000810 A B C D E F G + kappaQuarticChamberRestLF8000810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace8000810, kappaQuarticChamberRestLF8000810]
  module

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest8000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF8000810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face8000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace8000810 A B C D E F G +
        kappaQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face8000_add_rest]
  simp only [kappaQuarticChamberRest8000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₂` on unowned packet 8000 (1 monomial, top degree `D.natDegree + G.natDegree`). -/
def n2QuarticChamberFace8000810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₂` off packet 8000 (7 monomials). -/
def n2QuarticChamberRestLF8000810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem n2QuarticLoadFree810_eq_face8000_add_rest
    (A B C D E F G : k[X]) :
    n2QuarticLoadFree810 A B C D E F G =
      n2QuarticChamberFace8000810 A B C D E F G + n2QuarticChamberRestLF8000810 A B C D E F G := by
  simp only [n2QuarticLoadFree810, n2QuarticChamberFace8000810, n2QuarticChamberRestLF8000810]
  module

set_option maxHeartbeats 64000000 in
def n2QuarticChamberRest8000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticChamberRestLF8000810 A B C D E F G +
    n2QuarticColumnL810 l A B C D E F G +
    n2QuarticColumnBeta810 beta A B C D E F G +
    n2QuarticColumnGamma810 gamma A B C D E F G +
    n2QuarticColumnDelta810 delta A B C D E F G +
    n2QuarticColumnEpsilon810 epsilon A B C D E F G +
    n2QuarticColumnZeta810 zeta A B C D E F G +
    n2QuarticColumnEta810 eta A B C D E F G +
    n2QuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_face8000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticChamberFace8000810 A B C D E F G +
        n2QuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN2Quartic810_eq_chamberSplit,
    n2QuarticLoadFree810_eq_face8000_add_rest]
  simp only [n2QuarticChamberRest8000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `N₃` on unowned packet 8000 (1 monomial, top degree `A.natDegree + D.natDegree + G.natDegree`). -/
def n3QuarticChamberFace8000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 256 : k)) • (A * D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `N₃` off packet 8000 (18 monomials). -/
def n3QuarticChamberRestLF8000810
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
theorem n3QuarticLoadFree810_eq_face8000_add_rest
    (A B C D E F G : k[X]) :
    n3QuarticLoadFree810 A B C D E F G =
      n3QuarticChamberFace8000810 A B C D E F G + n3QuarticChamberRestLF8000810 A B C D E F G := by
  simp only [n3QuarticLoadFree810, n3QuarticChamberFace8000810, n3QuarticChamberRestLF8000810]
  module

set_option maxHeartbeats 64000000 in
def n3QuarticChamberRest8000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n3QuarticChamberRestLF8000810 A B C D E F G +
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
theorem degreeZeroN3Quartic810_eq_face8000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n3QuarticChamberFace8000810 A B C D E F G +
        n3QuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN3Quartic810_eq_chamberSplit,
    n3QuarticLoadFree810_eq_face8000_add_rest]
  simp only [n3QuarticChamberRest8000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on unowned packet 8000 (1 monomial, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace8000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 8000 (9 monomials). -/
def muQuarticChamberRestLF8000810
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
theorem muQuarticLoadFree810_eq_face8000_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace8000810 A B C D E F G + muQuarticChamberRestLF8000810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace8000810, muQuarticChamberRestLF8000810]
  module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest8000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF8000810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face8000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace8000810 A B C D E F G +
        muQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face8000_add_rest]
  simp only [muQuarticChamberRest8000810]
  ring

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on unowned packet 8000 (1 monomial, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace8000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 8000 (12 monomials). -/
def xiQuarticChamberRestLF8000810
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
theorem xiQuarticLoadFree810_eq_face8000_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace8000810 A B C D E F G + xiQuarticChamberRestLF8000810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace8000810, xiQuarticChamberRestLF8000810]
  module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest8000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF8000810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face8000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace8000810 A B C D E F G +
        xiQuarticChamberRest8000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face8000_add_rest]
  simp only [xiQuarticChamberRest8000810]
  ring


end QuarticChamberUnownedRefinePackets810

end Max11DegreeRoutes
