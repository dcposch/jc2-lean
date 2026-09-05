import Grok810ScaleZeroQuarticChamberFacesPart0Scratch

/-! # Cost-argmin faces and rests, part 1: the packets, `(8,10)` scale zero

The 79 face packets — a packet is a *(carrier, face monomial
set)* pair, since the face depends on the live set as well as on the
argmin — each with its face, its load-free rest and the cone-free packet
split identity.  Definitions and identities only; the rest *bounds* are
in the sibling `…FacesPart2..PartN` modules, which are mutually
independent.  Untracked working note.
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

section QuarticChamberFaces810

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BBB, BF·DD, BF·DD·BBB, BF·EE·BBB` (1 monomial, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace0810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 0 (5 monomials). -/
def kappaQuarticChamberRestLF0810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face0_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace0810 A B C D E F G + kappaQuarticChamberRestLF0810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace0810, kappaQuarticChamberRestLF0810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CCC, CF·CCC` (1 monomial, top degree `3 * C.natDegree`). -/
def muQuarticChamberFace0810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 0 (9 monomials). -/
def muQuarticChamberRestLF0810
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
theorem muQuarticLoadFree810_eq_face0_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace0810 A B C D E F G + muQuarticChamberRestLF0810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace0810, muQuarticChamberRestLF0810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BG·DD, BG·DD·BBB, BG·DD·DG·GG, CF·DD` (1 monomial, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 1 (9 monomials). -/
def muQuarticChamberRestLF1810
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
theorem muQuarticLoadFree810_eq_face1_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace1810 A B C D E F G + muQuarticChamberRestLF1810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace1810, muQuarticChamberRestLF1810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BG·EE, BG·EE·BBB, BG·EE·EG·GG, CF·EE` (1 monomial, top degree `2 * E.natDegree`). -/
def muQuarticChamberFace2810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 2 (9 monomials). -/
def muQuarticChamberRestLF2810
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
theorem muQuarticLoadFree810_eq_face2_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace2810 A B C D E F G + muQuarticChamberRestLF2810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace2810, muQuarticChamberRestLF2810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG, BF·BG·CF·CG·FF·FG·GG, BF·CF·EE·EF·FF, BF·EE·EF·FF` (1 monomial, top degree `2 * F.natDegree`). -/
def xiQuarticChamberFace0810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 0 (12 monomials). -/
def xiQuarticChamberRestLF0810
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
theorem xiQuarticLoadFree810_eq_face0_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace0810 A B C D E F G + xiQuarticChamberRestLF0810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace0810, xiQuarticChamberRestLF0810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BG·CG·DD·DG·GG, BG·GG, CG·DD, CG·DD·DG·GG` (1 monomial, top degree `2 * G.natDegree`). -/
def piQuarticChamberFace0810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 0 (20 monomials). -/
def piQuarticChamberRestLF0810
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
theorem piQuarticLoadFree810_eq_face0_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace0810 A B C D E F G + piQuarticChamberRestLF0810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace0810, piQuarticChamberRestLF0810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BBB·BBC·BCC·CCC, EE·BBB·BBC·BCC·CCC` (2 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace1810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 1 (4 monomials). -/
def kappaQuarticChamberRestLF1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face1_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace1810 A B C D E F G + kappaQuarticChamberRestLF1810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace1810, kappaQuarticChamberRestLF1810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BBB·BBC·BCC·CCC` (2 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace3810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 128 : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 3 (8 monomials). -/
def muQuarticChamberRestLF3810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face3_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace3810 A B C D E F G + muQuarticChamberRestLF3810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace3810, muQuarticChamberRestLF3810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF, BF·BBB, BF·BG, BF·BG·BBB` (1 monomial, top degree `A.natDegree + B.natDegree + F.natDegree`). -/
def muQuarticChamberFace4810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * B * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 4 (9 monomials). -/
def muQuarticChamberRestLF4810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face4_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace4810 A B C D E F G + muQuarticChamberRestLF4810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace4810, muQuarticChamberRestLF4810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·BG·DD, BF·BG·EE, BG, BG·CG·DD` (1 monomial, top degree `B.natDegree + G.natDegree`). -/
def kappaQuarticChamberFace2810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 2 (5 monomials). -/
def kappaQuarticChamberRestLF2810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face2_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace2810 A B C D E F G + kappaQuarticChamberRestLF2810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace2810, kappaQuarticChamberRestLF2810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BG·BBB` (1 monomial, top degree `4 * B.natDegree`). -/
def muQuarticChamberFace5810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 5 (9 monomials). -/
def muQuarticChamberRestLF5810
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

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face5_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace5810 A B C D E F G + muQuarticChamberRestLF5810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace5810, muQuarticChamberRestLF5810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CG·CCC, CG·DD, CG·DD·CCC, DD·CCC` (1 monomial, top degree `C.natDegree + 2 * D.natDegree`). -/
def xiQuarticChamberFace1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 1 (12 monomials). -/
def xiQuarticChamberRestLF1810
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
theorem xiQuarticLoadFree810_eq_face1_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace1810 A B C D E F G + xiQuarticChamberRestLF1810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace1810, xiQuarticChamberRestLF1810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `EE·CCC` (1 monomial, top degree `2 * C.natDegree + E.natDegree`). -/
def xiQuarticChamberFace2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 2 (12 monomials). -/
def xiQuarticChamberRestLF2810
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
theorem xiQuarticLoadFree810_eq_face2_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace2810 A B C D E F G + xiQuarticChamberRestLF2810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace2810, xiQuarticChamberRestLF2810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·CF·DD, BF·CF·EE, CF, CF·CG·CCC` (1 monomial, top degree `C.natDegree + F.natDegree`). -/
def kappaQuarticChamberFace3810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 3 (5 monomials). -/
def kappaQuarticChamberRestLF3810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face3_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace3810 A B C D E F G + kappaQuarticChamberRestLF3810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace3810, kappaQuarticChamberRestLF3810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BG·CG, BG·CG·GG, CF·CG, CF·CG·FF·FG·GG` (1 monomial, top degree `C.natDegree + G.natDegree`). -/
def muQuarticChamberFace6810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 6 (9 monomials). -/
def muQuarticChamberRestLF6810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face6_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace6810 A B C D E F G + muQuarticChamberRestLF6810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace6810, muQuarticChamberRestLF6810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CG·CCC` (2 monomials, top degree `3 * C.natDegree`). -/
def muQuarticChamberFace7810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 7 (8 monomials). -/
def muQuarticChamberRestLF7810
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
theorem muQuarticLoadFree810_eq_face7_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace7810 A B C D E F G + muQuarticChamberRestLF7810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace7810, muQuarticChamberRestLF7810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `CG·CCC` (3 monomials, top degree `4 * C.natDegree`). -/
def piQuarticChamberFace1810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 1 (18 monomials). -/
def piQuarticChamberRestLF1810
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
theorem piQuarticLoadFree810_eq_face1_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace1810 A B C D E F G + piQuarticChamberRestLF1810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace1810, piQuarticChamberRestLF1810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·DD·DE·EE, CG·DD·DE·EE, CG·DD·DE·EE·CCC, CG·EE` (1 monomial, top degree `D.natDegree + E.natDegree`). -/
def kappaQuarticChamberFace4810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 4 (5 monomials). -/
def kappaQuarticChamberRestLF4810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face4_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace4810 A B C D E F G + kappaQuarticChamberRestLF4810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace4810, kappaQuarticChamberRestLF4810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CF·DD·DF·FF, DD·DF·DG·FF·FG·GG, DD·DF·FF` (2 monomials, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace8810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 8 (8 monomials). -/
def muQuarticChamberRestLF8810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face8_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace8810 A B C D E F G + muQuarticChamberRestLF8810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace8810, muQuarticChamberRestLF8810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CF·DD·DF·FF, DD·DF·DG·FF·FG·GG, DD·DF·FF` (2 monomials, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 3 (11 monomials). -/
def xiQuarticChamberRestLF3810
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

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face3_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace3810 A B C D E F G + xiQuarticChamberRestLF3810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace3810, xiQuarticChamberRestLF3810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BG·CG·DD·BBB·BBC·BCC·CCC, DD·BBB·BBC·BCC·CCC` (1 monomial, top degree `A.natDegree + B.natDegree + C.natDegree + D.natDegree`). -/
def xiQuarticChamberFace4810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 4 (12 monomials). -/
def xiQuarticChamberRestLF4810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
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

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face4_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace4810 A B C D E F G + xiQuarticChamberRestLF4810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace4810, xiQuarticChamberRestLF4810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·CF·EE·BBB·BBC·BCC·CCC, EE·BBB·BBC·BCC·CCC` (2 monomials, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace5810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  - (15 / 128 : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 5 (11 monomials). -/
def xiQuarticChamberRestLF5810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
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
theorem xiQuarticLoadFree810_eq_face5_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace5810 A B C D E F G + xiQuarticChamberRestLF5810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace5810, xiQuarticChamberRestLF5810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `EE·CCC` (1 monomial, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace5810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 5 (5 monomials). -/
def kappaQuarticChamberRestLF5810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face5_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace5810 A B C D E F G + kappaQuarticChamberRestLF5810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace5810, kappaQuarticChamberRestLF5810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·CF·BBB·BBC·BCC·CCC, BF·CF·DD·BBB·BBC·BCC·CCC, BF·CF·EE·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace6810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6 (3 monomials). -/
def kappaQuarticChamberRestLF6810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6810 A B C D E F G + kappaQuarticChamberRestLF6810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6810, kappaQuarticChamberRestLF6810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·CF·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace9810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 9 (7 monomials). -/
def muQuarticChamberRestLF9810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face9_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace9810 A B C D E F G + muQuarticChamberRestLF9810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace9810, muQuarticChamberRestLF9810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·CF·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 4 * B.natDegree`). -/
def xiQuarticChamberFace6810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (25 / 128 : k) • (B * C * F)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 6 (9 monomials). -/
def xiQuarticChamberRestLF6810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face6_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace6810 A B C D E F G + xiQuarticChamberRestLF6810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace6810, xiQuarticChamberRestLF6810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·BG·EE·BBB, BG·BBB` (2 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace7810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 7 (4 monomials). -/
def kappaQuarticChamberRestLF7810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face7_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace7810 A B C D E F G + kappaQuarticChamberRestLF7810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace7810, kappaQuarticChamberRestLF7810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BG·BBB` (2 monomials, top degree `A.natDegree + 4 * B.natDegree`). -/
def xiQuarticChamberFace7810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 7 (11 monomials). -/
def xiQuarticChamberRestLF7810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face7_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace7810 A B C D E F G + xiQuarticChamberRestLF7810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace7810, xiQuarticChamberRestLF7810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BG·CG·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace10810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 10 (7 monomials). -/
def muQuarticChamberRestLF10810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face10_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace10810 A B C D E F G + muQuarticChamberRestLF10810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace10810, muQuarticChamberRestLF10810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BG·CG·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 4 * B.natDegree`). -/
def xiQuarticChamberFace8810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 8 (10 monomials). -/
def xiQuarticChamberRestLF8810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face8_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace8810 A B C D E F G + xiQuarticChamberRestLF8810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace8810, xiQuarticChamberRestLF8810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CG·CCC` (2 monomials, top degree `2 * B.natDegree + 2 * C.natDegree`). -/
def xiQuarticChamberFace9810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 9 (11 monomials). -/
def xiQuarticChamberRestLF9810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face9_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace9810 A B C D E F G + xiQuarticChamberRestLF9810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace9810, xiQuarticChamberRestLF9810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `DD·DE·EE·BBB` (1 monomial, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace10810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 10 (12 monomials). -/
def xiQuarticChamberRestLF10810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
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

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face10_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace10810 A B C D E F G + xiQuarticChamberRestLF10810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace10810, xiQuarticChamberRestLF10810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BF·CF·DD·DE·DF·EE·EF·FF, BF·CF·DD·DF·FF, BF·DD·DE·DF·EE·EF·FF, BF·DD·DF·FF` (1 monomial, top degree `A.natDegree + 2 * F.natDegree`). -/
def piQuarticChamberFace2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 2 (20 monomials). -/
def piQuarticChamberRestLF2810
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
theorem piQuarticLoadFree810_eq_face2_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace2810 A B C D E F G + piQuarticChamberRestLF2810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace2810, piQuarticChamberRestLF2810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BG·BBB` (3 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace3810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 3 (18 monomials). -/
def piQuarticChamberRestLF3810
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
theorem piQuarticLoadFree810_eq_face3_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace3810 A B C D E F G + piQuarticChamberRestLF3810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace3810, piQuarticChamberRestLF3810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CG·CCC, CG·EE·CCC` (2 monomials, top degree `2 * C.natDegree + E.natDegree`). -/
def xiQuarticChamberFace11810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 11 (11 monomials). -/
def xiQuarticChamberRestLF11810
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
theorem xiQuarticLoadFree810_eq_face11_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace11810 A B C D E F G + xiQuarticChamberRestLF11810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace11810, xiQuarticChamberRestLF11810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG·EE, BG·CG·DD·DE·DG·EE·EG·GG, BG·CG·DD·DE·EE, BG·CG·EE·EG·GG` (1 monomial, top degree `E.natDegree + G.natDegree`). -/
def xiQuarticChamberFace12810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 12 (12 monomials). -/
def xiQuarticChamberRestLF12810
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
theorem xiQuarticLoadFree810_eq_face12_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace12810 A B C D E F G + xiQuarticChamberRestLF12810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace12810, xiQuarticChamberRestLF12810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CG·EE·CCC` (3 monomials, top degree `3 * C.natDegree`). -/
def muQuarticChamberFace11810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 11 (7 monomials). -/
def muQuarticChamberRestLF11810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face11_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace11810 A B C D E F G + muQuarticChamberRestLF11810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace11810, muQuarticChamberRestLF11810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `CG·EE·CCC` (4 monomials, top degree `4 * C.natDegree`). -/
def piQuarticChamberFace4810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (C * E ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 4 (17 monomials). -/
def piQuarticChamberRestLF4810
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
theorem piQuarticLoadFree810_eq_face4_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace4810 A B C D E F G + piQuarticChamberRestLF4810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace4810, piQuarticChamberRestLF4810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `DD·CCC` (2 monomials, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace12810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 12 (8 monomials). -/
def muQuarticChamberRestLF12810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face12_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace12810 A B C D E F G + muQuarticChamberRestLF12810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace12810, muQuarticChamberRestLF12810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `DD·CCC` (2 monomials, top degree `A.natDegree + C.natDegree + 2 * D.natDegree`). -/
def piQuarticChamberFace5810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 5 (19 monomials). -/
def piQuarticChamberRestLF5810
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
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face5_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace5810 A B C D E F G + piQuarticChamberRestLF5810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace5810, piQuarticChamberRestLF5810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `DD·DE·EE·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace8810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 8 (3 monomials). -/
def kappaQuarticChamberRestLF8810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face8_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace8810 A B C D E F G + kappaQuarticChamberRestLF8810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace8810, kappaQuarticChamberRestLF8810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `DD·DE·EE·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace13810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 128 : k) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 13 (6 monomials). -/
def muQuarticChamberRestLF13810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face13_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace13810 A B C D E F G + muQuarticChamberRestLF13810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace13810, muQuarticChamberRestLF13810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `DD·DE·EE·BBB·BBC·BCC·CCC` (6 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace6810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (C * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 6 (15 monomials). -/
def piQuarticChamberRestLF6810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face6_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace6810 A B C D E F G + piQuarticChamberRestLF6810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace6810, piQuarticChamberRestLF6810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `DD·DE·EE·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace13810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  - (15 / 128 : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 13 (10 monomials). -/
def xiQuarticChamberRestLF13810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
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
theorem xiQuarticLoadFree810_eq_face13_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace13810 A B C D E F G + xiQuarticChamberRestLF13810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace13810, xiQuarticChamberRestLF13810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·CF·DD·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace14810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 14 (6 monomials). -/
def muQuarticChamberRestLF14810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face14_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace14810 A B C D E F G + muQuarticChamberRestLF14810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace14810, muQuarticChamberRestLF14810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BF·CF·DD·BBB·BBC·BCC·CCC` (6 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace7810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 7 (15 monomials). -/
def piQuarticChamberRestLF7810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
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
theorem piQuarticLoadFree810_eq_face7_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace7810 A B C D E F G + piQuarticChamberRestLF7810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace7810, piQuarticChamberRestLF7810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC, BF·CF·DD·BBB·BBC·BCC·CCC, CG·DD·CCC` (2 monomials, top degree `A.natDegree + B.natDegree + C.natDegree + D.natDegree`). -/
def xiQuarticChamberFace14810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 14 (11 monomials). -/
def xiQuarticChamberRestLF14810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
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
theorem xiQuarticLoadFree810_eq_face14_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace14810 A B C D E F G + xiQuarticChamberRestLF14810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace14810, xiQuarticChamberRestLF14810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG·DD, BF·BG·DD·BBB, BF·CF·DD·DE·EE, BF·DD` (1 monomial, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace15810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 15 (12 monomials). -/
def xiQuarticChamberRestLF15810
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
theorem xiQuarticLoadFree810_eq_face15_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace15810 A B C D E F G + xiQuarticChamberRestLF15810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace15810, xiQuarticChamberRestLF15810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BG·CG·BBB·BBC·BCC·CCC, BG·CG·EE·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace9810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 9 (3 monomials). -/
def kappaQuarticChamberRestLF9810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face9_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace9810 A B C D E F G + kappaQuarticChamberRestLF9810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace9810, kappaQuarticChamberRestLF9810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BG·CG·BBB·BBC·BCC·CCC` (6 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace8810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 8 (15 monomials). -/
def piQuarticChamberRestLF8810
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
theorem piQuarticLoadFree810_eq_face8_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace8810 A B C D E F G + piQuarticChamberRestLF8810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace8810, piQuarticChamberRestLF8810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·CF·EE·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace15810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • C ^ 3
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 15 (6 monomials). -/
def muQuarticChamberRestLF15810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face15_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace15810 A B C D E F G + muQuarticChamberRestLF15810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace15810, muQuarticChamberRestLF15810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC, BG·CG·EE·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace16810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 16 (10 monomials). -/
def xiQuarticChamberRestLF16810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
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
theorem xiQuarticLoadFree810_eq_face16_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace16810 A B C D E F G + xiQuarticChamberRestLF16810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace16810, xiQuarticChamberRestLF16810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `CG·CCC` (2 monomials, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace10810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 10 (4 monomials). -/
def kappaQuarticChamberRestLF10810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face10_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace10810 A B C D E F G + kappaQuarticChamberRestLF10810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace10810, kappaQuarticChamberRestLF10810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace11810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 11 (2 monomials). -/
def kappaQuarticChamberRestLF11810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face11_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace11810 A B C D E F G + kappaQuarticChamberRestLF11810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace11810, kappaQuarticChamberRestLF11810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace16810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 16 (6 monomials). -/
def muQuarticChamberRestLF16810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face16_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace16810 A B C D E F G + muQuarticChamberRestLF16810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace16810, muQuarticChamberRestLF16810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (8 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace9810
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
/-- Load-free rest of `π` off packet 9 (13 monomials). -/
def piQuarticChamberRestLF9810
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
theorem piQuarticLoadFree810_eq_face9_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace9810 A B C D E F G + piQuarticChamberRestLF9810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace9810, piQuarticChamberRestLF9810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (5 monomials, top degree `A.natDegree + 4 * B.natDegree`). -/
def xiQuarticChamberFace17810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 17 (8 monomials). -/
def xiQuarticChamberRestLF17810
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
theorem xiQuarticLoadFree810_eq_face17_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace17810 A B C D E F G + xiQuarticChamberRestLF17810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace17810, xiQuarticChamberRestLF17810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·DD·DE·EE·BBB` (2 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace12810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 12 (4 monomials). -/
def kappaQuarticChamberRestLF12810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face12_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace12810 A B C D E F G + kappaQuarticChamberRestLF12810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace12810, kappaQuarticChamberRestLF12810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·BG·DD·DE·EE, BF·DD·DE·EE·BBB` (3 monomials, top degree `A.natDegree + B.natDegree + F.natDegree`). -/
def muQuarticChamberFace17810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 17 (7 monomials). -/
def muQuarticChamberRestLF17810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face17_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace17810 A B C D E F G + muQuarticChamberRestLF17810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace17810, muQuarticChamberRestLF17810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BF·DD·DE·EE·BBB` (3 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace10810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  + (5 / 16 : k) • (A * B * D * E)
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 10 (18 monomials). -/
def piQuarticChamberRestLF10810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
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
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face10_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace10810 A B C D E F G + piQuarticChamberRestLF10810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace10810, piQuarticChamberRestLF10810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·DD·DE·EE·BBB` (2 monomials, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace18810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 18 (11 monomials). -/
def xiQuarticChamberRestLF18810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
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
theorem xiQuarticLoadFree810_eq_face18_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace18810 A B C D E F G + xiQuarticChamberRestLF18810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace18810, xiQuarticChamberRestLF18810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BG·DD·DE·EE·BBB` (3 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace13810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 13 (3 monomials). -/
def kappaQuarticChamberRestLF13810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face13_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace13810 A B C D E F G + kappaQuarticChamberRestLF13810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace13810, kappaQuarticChamberRestLF13810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BG·DD·DE·EE·BBB` (4 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace11810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 11 (17 monomials). -/
def piQuarticChamberRestLF11810
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
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face11_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace11810 A B C D E F G + piQuarticChamberRestLF11810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace11810, piQuarticChamberRestLF11810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·EE·BBB, BG·DD·DE·EE·BBB` (2 monomials, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace19810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 19 (11 monomials). -/
def xiQuarticChamberRestLF19810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
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
theorem xiQuarticLoadFree810_eq_face19_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace19810 A B C D E F G + xiQuarticChamberRestLF19810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace19810, xiQuarticChamberRestLF19810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `CF·DD·DE·EE·CCC, CG·DD·CCC` (2 monomials, top degree `C.natDegree + F.natDegree`). -/
def kappaQuarticChamberFace14810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 14 (4 monomials). -/
def kappaQuarticChamberRestLF14810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face14_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace14810 A B C D E F G + kappaQuarticChamberRestLF14810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace14810, kappaQuarticChamberRestLF14810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CF·DD·DE·EE·CCC` (3 monomials, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace18810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 18 (7 monomials). -/
def muQuarticChamberRestLF18810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face18_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace18810 A B C D E F G + muQuarticChamberRestLF18810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace18810, muQuarticChamberRestLF18810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `CF·DD·DE·EE·CCC` (4 monomials, top degree `A.natDegree + C.natDegree + 2 * D.natDegree`). -/
def piQuarticChamberFace12810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (C * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 12 (17 monomials). -/
def piQuarticChamberRestLF12810
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
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face12_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace12810 A B C D E F G + piQuarticChamberRestLF12810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace12810, piQuarticChamberRestLF12810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CF·DD·DE·EE·CCC` (2 monomials, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace20810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  - (15 / 128 : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 20 (11 monomials). -/
def xiQuarticChamberRestLF20810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face20_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace20810 A B C D E F G + xiQuarticChamberRestLF20810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace20810, xiQuarticChamberRestLF20810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `CG·DD·CCC, CG·EE·CCC` (3 monomials, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace15810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 15 (3 monomials). -/
def kappaQuarticChamberRestLF15810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face15_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace15810 A B C D E F G + kappaQuarticChamberRestLF15810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace15810, kappaQuarticChamberRestLF15810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CG·DD·CCC` (3 monomials, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace19810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 19 (7 monomials). -/
def muQuarticChamberRestLF19810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face19_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace19810 A B C D E F G + muQuarticChamberRestLF19810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace19810, muQuarticChamberRestLF19810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `CG·DD·CCC` (4 monomials, top degree `A.natDegree + C.natDegree + 2 * D.natDegree`). -/
def piQuarticChamberFace13810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 13 (17 monomials). -/
def piQuarticChamberRestLF13810
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
theorem piQuarticLoadFree810_eq_face13_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace13810 A B C D E F G + piQuarticChamberRestLF13810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace13810, piQuarticChamberRestLF13810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CG·DD·CCC` (3 monomials, top degree `A.natDegree + B.natDegree + C.natDegree + D.natDegree`). -/
def xiQuarticChamberFace21810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 21 (10 monomials). -/
def xiQuarticChamberRestLF21810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face21_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace21810 A B C D E F G + xiQuarticChamberRestLF21810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace21810, xiQuarticChamberRestLF21810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·BG·CF·CG` (2 monomials, top degree `B.natDegree + G.natDegree`). -/
def kappaQuarticChamberFace16810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 16 (4 monomials). -/
def kappaQuarticChamberRestLF16810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face16_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace16810 A B C D E F G + kappaQuarticChamberRestLF16810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace16810, kappaQuarticChamberRestLF16810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·BG·CF·CG` (2 monomials, top degree `A.natDegree + B.natDegree + F.natDegree`). -/
def muQuarticChamberFace20810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * B * F)
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 20 (8 monomials). -/
def muQuarticChamberRestLF20810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face20_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace20810 A B C D E F G + muQuarticChamberRestLF20810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace20810, muQuarticChamberRestLF20810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BF·BG·CF·CG, BF·BG·DD·DE·EE, CF·CG·DD·DE·EE` (2 monomials, top degree `A.natDegree + 2 * F.natDegree`). -/
def piQuarticChamberFace14810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (A * F ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 14 (19 monomials). -/
def piQuarticChamberRestLF14810
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
theorem piQuarticLoadFree810_eq_face14_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace14810 A B C D E F G + piQuarticChamberRestLF14810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace14810, piQuarticChamberRestLF14810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `CG·DD·CCC, CG·EE·CCC` (3 monomials, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace17810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 17 (3 monomials). -/
def kappaQuarticChamberRestLF17810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face17_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace17810 A B C D E F G + kappaQuarticChamberRestLF17810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace17810, kappaQuarticChamberRestLF17810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·DD·DE·EE, CF·CG·DD·DE·EE` (2 monomials, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace22810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 22 (11 monomials). -/
def xiQuarticChamberRestLF22810
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
theorem xiQuarticLoadFree810_eq_face22_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace22810 A B C D E F G + xiQuarticChamberRestLF22810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace22810, xiQuarticChamberRestLF22810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CF·CG·DD·DE·EE` (3 monomials, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace21810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 21 (7 monomials). -/
def muQuarticChamberRestLF21810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face21_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace21810 A B C D E F G + muQuarticChamberRestLF21810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace21810, muQuarticChamberRestLF21810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CG·DD·CCC` (3 monomials, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace23810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 23 (10 monomials). -/
def xiQuarticChamberRestLF23810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face23_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace23810 A B C D E F G + xiQuarticChamberRestLF23810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace23810, xiQuarticChamberRestLF23810]
  module


end QuarticChamberFaces810

end Max11DegreeRoutes
