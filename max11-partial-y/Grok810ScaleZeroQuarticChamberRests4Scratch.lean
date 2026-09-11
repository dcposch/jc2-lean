import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberColumns2Scratch
import Grok810ScaleZeroQuarticChamberNuFacesScratch

/-! # Chamber rests for the multi-carrier kills, `(8,10)` scale zero

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

section QuarticChamberRests4810

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF1810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face1_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace1810 A B C D E F G +
        kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face1_add_rest]
  simp only [kappaQuarticChamberRest1810]
  ring

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF3810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face3_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace3810 A B C D E F G +
        muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face3_add_rest]
  simp only [muQuarticChamberRest3810]
  ring

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF7810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face7_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace7810 A B C D E F G +
        kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face7_add_rest]
  simp only [kappaQuarticChamberRest7810]
  ring

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF3810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face3_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace3810 A B C D E F G +
        piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face3_add_rest]
  simp only [piQuarticChamberRest3810]
  ring

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF6810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face6_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace6810 A B C D E F G +
        kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face6_add_rest]
  simp only [kappaQuarticChamberRest6810]
  ring

set_option maxHeartbeats 64000000 in
def muQuarticChamberRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF9810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnGamma810 gamma A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_face9_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticChamberFace9810 A B C D E F G +
        muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroMuQuartic810_eq_chamberSplit,
    muQuarticLoadFree810_eq_face9_add_rest]
  simp only [muQuarticChamberRest9810]
  ring

set_option maxHeartbeats 64000000 in
def piQuarticChamberRest2000810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  piQuarticChamberRestLF2000810 A B C D E F G +
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
theorem degreeZeroPiQuartic810_eq_face2000_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticChamberFace2000810 A B C D E F G +
        piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroPiQuartic810_eq_chamberSplit,
    piQuarticLoadFree810_eq_face2000_add_rest]
  simp only [piQuarticChamberRest2000810]
  ring

set_option maxHeartbeats 64000000 in
def kappaQuarticChamberRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticChamberRestLF10810 A B C D E F G +
    kappaQuarticColumnL810 l A B C D E F G +
    kappaQuarticColumnBeta810 beta A B C D E F G +
    kappaQuarticColumnGamma810 gamma A B C D E F G +
    kappaQuarticColumnDelta810 delta A B C D E F G +
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
    kappaQuarticColumnZeta810 zeta A B C D E F G +
    kappaQuarticColumnEta810 eta A B C D E F G +
    kappaQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_face10_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticChamberFace10810 A B C D E F G +
        kappaQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroKappaQuartic810_eq_chamberSplit,
    kappaQuarticLoadFree810_eq_face10_add_rest]
  simp only [kappaQuarticChamberRest10810]
  ring

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRest19810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF19810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnEpsilon810 epsilon A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_face19_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticChamberFace19810 A B C D E F G +
        xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroXiQuartic810_eq_chamberSplit,
    xiQuarticLoadFree810_eq_face19_add_rest]
  simp only [xiQuarticChamberRest19810]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BC
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BC
      A B C D E F G hdpos hDz hEz hFz hGz
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BC l A B C D E F G hdpos hDz hEz hFz hGz g0 g1 g2 g3 g4
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BC beta A B C D E F G hdpos hDz hEz hFz hGz g0 g1 g2 g3
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BC gamma A B C D E F G hdpos hDz hEz hFz hGz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BC delta A B C D E F G hdpos hDz hEz hFz hGz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hEz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BC zeta A B C D E F G hdpos hDz hEz hFz hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BC eta A B C D E F G hdpos hDz hEz hFz hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BC theta A B C D E F G hdpos hDz hEz hFz hGz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BC
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BC
      A B C D E F G hdpos hDz hEz hFz hGz hl0
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BC l A B C D E F G hdpos hDz hEz hFz hGz g0 g1 g2 g3
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BC beta A B C D E F G hdpos hDz hEz hFz hGz g0 g1 g2
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BC gamma A B C D E F G hdpos hDz hEz hFz hGz g0 g1
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BC delta A B C D E F G hdpos hDz hEz hFz hGz g0 g1
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BC epsilon A B C D E F G hdpos hDz hEz hFz hGz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BC zeta A B C D E F G hdpos hDz hEz hFz hGz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BC eta A B C D E F G hdpos hDz hEz hFz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BC theta A B C D E F G hdpos hDz hEz hFz hGz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCD
      A B C D E F G hdpos hEz hFz hGz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCD l A B C D E F G hdpos hEz hFz hGz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCD beta A B C D E F G hdpos hEz hFz hGz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCD gamma A B C D E F G hdpos hEz hFz hGz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCD delta A B C D E F G hdpos hEz hFz hGz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCD epsilon A B C D E F G hdpos hEz hFz hGz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCD zeta A B C D E F G hdpos hEz hFz hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCD eta A B C D E F G hdpos hEz hFz hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCD theta A B C D E F G hdpos hEz hFz hGz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * D.natDegree < d)
    (hl2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCD
      A B C D E F G hdpos hEz hFz hGz hl0 hl1 hl2
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCD l A B C D E F G hdpos hEz hFz hGz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCD beta A B C D E F G hdpos hEz hFz hGz g0 g1 g2 g3 g4
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCD gamma A B C D E F G hdpos hEz hFz hGz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCD delta A B C D E F G hdpos hEz hFz hGz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCD epsilon A B C D E F G hdpos hEz hFz hGz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCD zeta A B C D E F G hdpos hEz hFz hGz g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCD eta A B C D E F G hdpos hEz hFz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCD theta A B C D E F G hdpos hEz hFz hGz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCE
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCE
      A B C D E F G hdpos hDz hFz hGz
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCE l A B C D E F G hdpos hDz hFz hGz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCE beta A B C D E F G hdpos hDz hFz hGz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCE gamma A B C D E F G hdpos hDz hFz hGz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCE delta A B C D E F G hdpos hDz hFz hGz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCE zeta A B C D E F G hdpos hDz hFz hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCE eta A B C D E F G hdpos hDz hFz hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCE theta A B C D E F G hdpos hDz hFz hGz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCE
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : 2 * B.natDegree + E.natDegree < d)
    (hl2 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCE
      A B C D E F G hdpos hDz hFz hGz hl0 hl1 hl2
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCE l A B C D E F G hdpos hDz hFz hGz g0 g1 g2 g3 g4
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCE beta A B C D E F G hdpos hDz hFz hGz g0 g1 g2 g3
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCE gamma A B C D E F G hdpos hDz hFz hGz g0 g1
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCE delta A B C D E F G hdpos hDz hFz hGz g0 g1
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCE epsilon A B C D E F G hdpos hDz hFz hGz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCE zeta A B C D E F G hdpos hDz hFz hGz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCE eta A B C D E F G hdpos hDz hFz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCE theta A B C D E F G hdpos hDz hFz hGz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : C.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCF
      A B C D E F G hdpos hDz hEz hGz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCF beta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCF gamma A B C D E F G hdpos hDz hEz hGz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCF delta A B C D E F G hdpos hDz hEz hGz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hEz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCF zeta A B C D E F G hdpos hDz hEz hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCF eta A B C D E F G hdpos hDz hEz hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCF theta A B C D E F G hdpos hDz hEz hGz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCF
      A B C D E F G hdpos hDz hEz hGz hl0 hl1
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCF beta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCF gamma A B C D E F G hdpos hDz hEz hGz g0 g1
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCF delta A B C D E F G hdpos hDz hEz hGz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCF epsilon A B C D E F G hdpos hDz hEz hGz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCF zeta A B C D E F G hdpos hDz hEz hGz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCF eta A B C D E F G hdpos hDz hEz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCF theta A B C D E F G hdpos hDz hEz hGz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : B.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCG
      A B C D E F G hdpos hDz hEz hFz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCG l A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4 g5
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCG beta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCG gamma A B C D E F G hdpos hDz hEz hFz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCG delta A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hEz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCG zeta A B C D E F G hdpos hDz hEz hFz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCG eta A B C D E F G hdpos hDz hEz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCG theta A B C D E F G hdpos hDz hEz hFz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : C.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCG
      A B C D E F G hdpos hDz hEz hFz hl0 hl1
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCG l A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCG beta A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCG gamma A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCG delta A B C D E F G hdpos hDz hEz hFz g0 g1
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCG epsilon A B C D E F G hdpos hDz hEz hFz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCG zeta A B C D E F G hdpos hDz hEz hFz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCG eta A B C D E F G hdpos hDz hEz hFz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCG theta A B C D E F G hdpos hDz hEz hFz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BEG
      A B C D E F G hdpos hCz hDz hFz
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BEG l A B C D E F G hdpos hCz hDz hFz g0 g1 g2 g3
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BEG beta A B C D E F G hdpos hCz hDz hFz g0 g1 g2 g3
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    subst hCz
    subst hDz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BEG delta A B C D E F G hdpos hCz hDz hFz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hCz
    subst hDz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BEG zeta A B C D E F G hdpos hCz hDz hFz g0
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BEG eta A B C D E F G hdpos hCz hDz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BEG theta A B C D E F G hdpos hCz hDz hFz g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hbl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 5 * B.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (4 * B.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ G.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BEG
      A B C D E F G hdpos hCz hDz hFz
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BEG l A B C D E F G hdpos hCz hDz hFz g0 g1 g2 g3
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BEG l A B C D E F G hdpos hCz hDz hFz g4
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BEG beta A B C D E F G hdpos hCz hDz hFz g0 g1
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BEG gamma A B C D E F G hdpos hCz hDz hFz g0 g1 g2
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BEG delta A B C D E F G hdpos hCz hDz hFz g0 g1
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hCz
    subst hDz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [piQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BEG zeta A B C D E F G hdpos hCz hDz hFz g0 g1
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BEG eta A B C D E F G hdpos hCz hDz hFz g0 g1
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hCz
    subst hDz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [piQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCDE
      A B C D E F G hdpos hFz hGz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDE l A B C D E F G hdpos hFz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDE beta A B C D E F G hdpos hFz hGz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDE gamma A B C D E F G hdpos hFz hGz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDE delta A B C D E F G hdpos hFz hGz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDE epsilon A B C D E F G hdpos hFz hGz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDE zeta A B C D E F G hdpos hFz hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDE eta A B C D E F G hdpos hFz hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDE theta A B C D E F G hdpos hFz hGz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * D.natDegree < d)
    (hl2 : 2 * B.natDegree + E.natDegree < d)
    (hl3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl4 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCDE
      A B C D E F G hdpos hFz hGz hl0 hl1 hl2 hl3 hl4
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDE l A B C D E F G hdpos hFz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDE beta A B C D E F G hdpos hFz hGz g0 g1 g2 g3 g4 g5
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDE gamma A B C D E F G hdpos hFz hGz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDE delta A B C D E F G hdpos hFz hGz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDE epsilon A B C D E F G hdpos hFz hGz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDE zeta A B C D E F G hdpos hFz hGz g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDE eta A B C D E F G hdpos hFz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDE theta A B C D E F G hdpos hFz hGz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : C.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCDF
      A B C D E F G hdpos hEz hGz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDF l A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDF beta A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDF gamma A B C D E F G hdpos hEz hGz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDF delta A B C D E F G hdpos hEz hGz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDF epsilon A B C D E F G hdpos hEz hGz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDF zeta A B C D E F G hdpos hEz hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDF eta A B C D E F G hdpos hEz hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDF theta A B C D E F G hdpos hEz hGz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hl2 : A.natDegree + 2 * D.natDegree < d)
    (hl3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl4 : D.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCDF
      A B C D E F G hdpos hEz hGz hl0 hl1 hl2 hl3 hl4
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDF l A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDF beta A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4 g5
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDF gamma A B C D E F G hdpos hEz hGz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDF delta A B C D E F G hdpos hEz hGz g0 g1 g2 g3
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDF epsilon A B C D E F G hdpos hEz hGz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDF zeta A B C D E F G hdpos hEz hGz g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDF eta A B C D E F G hdpos hEz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDF theta A B C D E F G hdpos hEz hGz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCDF
      A B C D E F G hdpos hEz hGz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDF l A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDF beta A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDF gamma A B C D E F G hdpos hEz hGz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDF delta A B C D E F G hdpos hEz hGz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDF epsilon A B C D E F G hdpos hEz hGz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDF zeta A B C D E F G hdpos hEz hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDF eta A B C D E F G hdpos hEz hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDF theta A B C D E F G hdpos hEz hGz g0
  simp only [kappaQuarticChamberRest6810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest9810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * D.natDegree < d)
    (hl2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl3 : D.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF9810_natDegree_lt_of_live_BCDF
      A B C D E F G hdpos hEz hGz hl0 hl1 hl2 hl3
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDF l A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDF beta A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4 g5
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDF gamma A B C D E F G hdpos hEz hGz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDF delta A B C D E F G hdpos hEz hGz g0 g1 g2 g3
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDF epsilon A B C D E F G hdpos hEz hGz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDF zeta A B C D E F G hdpos hEz hGz g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDF eta A B C D E F G hdpos hEz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDF theta A B C D E F G hdpos hEz hGz g0
  simp only [muQuarticChamberRest9810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest2000810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : 4 * B.natDegree + C.natDegree < d)
    (hl2 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl3 : 3 * B.natDegree + F.natDegree < d)
    (hl4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl6 : C.natDegree + D.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree + D.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ B.natDegree + D.natDegree + F.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d ∧ 3 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCDF
      A B C D E F G hdpos hEz hGz hl0 hl1 hl2 hl3 hl4 hl5 hl6
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCDF l A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCDF l A B C D E F G hdpos hEz hGz g14 g15 g16
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCDF beta A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCDF gamma A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4 g5
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCDF delta A B C D E F G hdpos hEz hGz g0 g1 g2 g3 g4 g5 g6
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCDF epsilon A B C D E F G hdpos hEz hGz g0 g1 g2 g3
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCDF zeta A B C D E F G hdpos hEz hGz g0 g1 g2 g3
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCDF eta A B C D E F G hdpos hEz hGz g0 g1 g2
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCDF theta A B C D E F G hdpos hEz hGz g0 g1
  simp only [piQuarticChamberRest2000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : B.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCDG
      A B C D E F G hdpos hEz hFz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDG l A B C D E F G hdpos hEz hFz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDG beta A B C D E F G hdpos hEz hFz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDG gamma A B C D E F G hdpos hEz hFz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDG delta A B C D E F G hdpos hEz hFz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDG epsilon A B C D E F G hdpos hEz hFz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDG zeta A B C D E F G hdpos hEz hFz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDG eta A B C D E F G hdpos hEz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDG theta A B C D E F G hdpos hEz hFz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * D.natDegree < d)
    (hl2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl3 : C.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCDG
      A B C D E F G hdpos hEz hFz hl0 hl1 hl2 hl3
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDG l A B C D E F G hdpos hEz hFz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDG beta A B C D E F G hdpos hEz hFz g0 g1 g2 g3 g4
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDG gamma A B C D E F G hdpos hEz hFz g0 g1 g2 g3
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDG delta A B C D E F G hdpos hEz hFz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDG epsilon A B C D E F G hdpos hEz hFz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDG zeta A B C D E F G hdpos hEz hFz g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDG eta A B C D E F G hdpos hEz hFz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDG theta A B C D E F G hdpos hEz hFz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : B.natDegree + 2 * C.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCDG
      A B C D E F G hdpos hEz hFz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDG l A B C D E F G hdpos hEz hFz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDG beta A B C D E F G hdpos hEz hFz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDG gamma A B C D E F G hdpos hEz hFz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDG delta A B C D E F G hdpos hEz hFz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDG epsilon A B C D E F G hdpos hEz hFz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDG zeta A B C D E F G hdpos hEz hFz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDG eta A B C D E F G hdpos hEz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDG theta A B C D E F G hdpos hEz hFz g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hl2 : 4 * B.natDegree + C.natDegree < d)
    (hl3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl6 : 4 * C.natDegree < d)
    (hl7 : B.natDegree + D.natDegree + G.natDegree < d)
    (hl8 : 2 * C.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree + D.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ 3 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BCDG
      A B C D E F G hdpos hEz hFz hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCDG l A B C D E F G hdpos hEz hFz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCDG l A B C D E F G hdpos hEz hFz g12
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCDG beta A B C D E F G hdpos hEz hFz g0 g1 g2 g3 g4 g5 g6 g7
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCDG gamma A B C D E F G hdpos hEz hFz g0 g1 g2 g3 g4
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCDG delta A B C D E F G hdpos hEz hFz g0 g1 g2 g3 g4
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCDG epsilon A B C D E F G hdpos hEz hFz g0 g1 g2
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCDG zeta A B C D E F G hdpos hEz hFz g0 g1 g2
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCDG eta A B C D E F G hdpos hEz hFz g0 g1 g2 g3
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCDG theta A B C D E F G hdpos hEz hFz g0
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hl0 : C.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCEF
      A B C D E F G hdpos hDz hGz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCEF l A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCEF beta A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCEF gamma A B C D E F G hdpos hDz hGz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCEF delta A B C D E F G hdpos hDz hGz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCEF zeta A B C D E F G hdpos hDz hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCEF eta A B C D E F G hdpos hDz hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCEF theta A B C D E F G hdpos hDz hGz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hl2 : 2 * B.natDegree + E.natDegree < d)
    (hl3 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCEF
      A B C D E F G hdpos hDz hGz hl0 hl1 hl2 hl3
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCEF l A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCEF beta A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCEF gamma A B C D E F G hdpos hDz hGz g0 g1
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCEF delta A B C D E F G hdpos hDz hGz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCEF epsilon A B C D E F G hdpos hDz hGz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCEF zeta A B C D E F G hdpos hDz hGz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCEF eta A B C D E F G hdpos hDz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCEF theta A B C D E F G hdpos hDz hGz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest6810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCEF
      A B C D E F G hdpos hDz hGz
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCEF l A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCEF beta A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCEF gamma A B C D E F G hdpos hDz hGz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCEF delta A B C D E F G hdpos hDz hGz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCEF zeta A B C D E F G hdpos hDz hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCEF eta A B C D E F G hdpos hDz hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCEF theta A B C D E F G hdpos hDz hGz g0
  simp only [kappaQuarticChamberRest6810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest9810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : 2 * B.natDegree + E.natDegree < d)
    (hl2 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF9810_natDegree_lt_of_live_BCEF
      A B C D E F G hdpos hDz hGz hl0 hl1 hl2
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCEF l A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCEF beta A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCEF gamma A B C D E F G hdpos hDz hGz g0 g1
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCEF delta A B C D E F G hdpos hDz hGz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCEF epsilon A B C D E F G hdpos hDz hGz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCEF zeta A B C D E F G hdpos hDz hGz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCEF eta A B C D E F G hdpos hDz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCEF theta A B C D E F G hdpos hDz hGz g0
  simp only [muQuarticChamberRest9810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest2000810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree + C.natDegree < d)
    (hl1 : 3 * B.natDegree + F.natDegree < d)
    (hl2 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hl3 : B.natDegree + E.natDegree + F.natDegree < d)
    (hl4 : C.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ 3 * C.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCEF
      A B C D E F G hdpos hDz hGz hl0 hl1 hl2 hl3 hl4
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCEF l A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCEF l A B C D E F G hdpos hDz hGz g13 g14
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCEF beta A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCEF gamma A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCEF delta A B C D E F G hdpos hDz hGz g0 g1 g2 g3 g4 g5
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCEF epsilon A B C D E F G hdpos hDz hGz g0 g1 g2
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCEF zeta A B C D E F G hdpos hDz hGz g0 g1 g2 g3
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCEF eta A B C D E F G hdpos hDz hGz g0 g1
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCEF theta A B C D E F G hdpos hDz hGz g0 g1
  simp only [piQuarticChamberRest2000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hl0 : B.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCEG
      A B C D E F G hdpos hDz hFz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCEG l A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCEG beta A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCEG gamma A B C D E F G hdpos hDz hFz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCEG delta A B C D E F G hdpos hDz hFz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCEG zeta A B C D E F G hdpos hDz hFz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCEG eta A B C D E F G hdpos hDz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCEG theta A B C D E F G hdpos hDz hFz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : 2 * B.natDegree + E.natDegree < d)
    (hl2 : C.natDegree + G.natDegree < d)
    (hl3 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCEG
      A B C D E F G hdpos hDz hFz hl0 hl1 hl2 hl3
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCEG l A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCEG beta A B C D E F G hdpos hDz hFz g0 g1 g2 g3
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCEG gamma A B C D E F G hdpos hDz hFz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCEG delta A B C D E F G hdpos hDz hFz g0 g1
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCEG epsilon A B C D E F G hdpos hDz hFz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCEG zeta A B C D E F G hdpos hDz hFz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCEG eta A B C D E F G hdpos hDz hFz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCEG theta A B C D E F G hdpos hDz hFz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hl0 : B.natDegree + 2 * C.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCEG
      A B C D E F G hdpos hDz hFz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCEG l A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCEG beta A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCEG gamma A B C D E F G hdpos hDz hFz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCEG delta A B C D E F G hdpos hDz hFz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCEG zeta A B C D E F G hdpos hDz hFz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCEG eta A B C D E F G hdpos hDz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCEG theta A B C D E F G hdpos hDz hFz g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hl1 : 4 * B.natDegree + C.natDegree < d)
    (hl2 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hl3 : 4 * C.natDegree < d)
    (hl4 : 2 * C.natDegree + G.natDegree < d)
    (hl5 : C.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ 3 * C.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree + C.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BCEG
      A B C D E F G hdpos hDz hFz hl0 hl1 hl2 hl3 hl4 hl5
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCEG l A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCEG l A B C D E F G hdpos hDz hFz g10
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCEG beta A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCEG gamma A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCEG delta A B C D E F G hdpos hDz hFz g0 g1 g2 g3
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCEG epsilon A B C D E F G hdpos hDz hFz g0 g1
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCEG zeta A B C D E F G hdpos hDz hFz g0 g1 g2
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCEG eta A B C D E F G hdpos hDz hFz g0 g1 g2
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCEG theta A B C D E F G hdpos hDz hFz g0
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest10810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + 3 * B.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF10810_natDegree_lt_of_live_BCEG
      A B C D E F G hdpos hDz hFz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCEG l A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCEG beta A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCEG gamma A B C D E F G hdpos hDz hFz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCEG delta A B C D E F G hdpos hDz hFz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCEG zeta A B C D E F G hdpos hDz hFz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCEG eta A B C D E F G hdpos hDz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCEG theta A B C D E F G hdpos hDz hFz g0
  simp only [kappaQuarticChamberRest10810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest7810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hl1 : 4 * B.natDegree < d)
    (hl2 : 2 * B.natDegree + E.natDegree < d)
    (hl3 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF7810_natDegree_lt_of_live_BCEG
      A B C D E F G hdpos hDz hFz hl0 hl1 hl2 hl3
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCEG l A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCEG beta A B C D E F G hdpos hDz hFz g0 g1 g2 g3
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCEG gamma A B C D E F G hdpos hDz hFz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCEG delta A B C D E F G hdpos hDz hFz g0 g1
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCEG epsilon A B C D E F G hdpos hDz hFz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCEG zeta A B C D E F G hdpos hDz hFz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCEG eta A B C D E F G hdpos hDz hFz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCEG theta A B C D E F G hdpos hDz hFz g0
  simp only [muQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest11810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hl1 : 4 * B.natDegree < d)
    (hl2 : 2 * B.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF11810_natDegree_lt_of_live_BCEG
      A B C D E F G hdpos hDz hFz hl0 hl1 hl2
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCEG l A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCEG beta A B C D E F G hdpos hDz hFz g0 g1 g2 g3
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCEG gamma A B C D E F G hdpos hDz hFz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCEG delta A B C D E F G hdpos hDz hFz g0 g1
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCEG epsilon A B C D E F G hdpos hDz hFz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCEG zeta A B C D E F G hdpos hDz hFz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCEG eta A B C D E F G hdpos hDz hFz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCEG theta A B C D E F G hdpos hDz hFz g0
  simp only [muQuarticChamberRest11810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest4810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hl0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hl2 : 4 * B.natDegree + C.natDegree < d)
    (hl3 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hl4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ 3 * C.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree + C.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d)) :
    (piQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF4810_natDegree_lt_of_live_BCEG
      A B C D E F G hdpos hDz hFz hl0 hl1 hl2 hl3 hl4
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCEG l A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCEG l A B C D E F G hdpos hDz hFz g10
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCEG beta A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4 g5
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCEG gamma A B C D E F G hdpos hDz hFz g0 g1 g2 g3 g4
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCEG delta A B C D E F G hdpos hDz hFz g0 g1 g2 g3
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCEG epsilon A B C D E F G hdpos hDz hFz g0 g1
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCEG zeta A B C D E F G hdpos hDz hFz g0 g1 g2
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCEG eta A B C D E F G hdpos hDz hFz g0 g1 g2
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCEG theta A B C D E F G hdpos hDz hFz g0
  simp only [piQuarticChamberRest4810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hl0 : B.natDegree + G.natDegree < d)
    (hl1 : C.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCFG
      A B C D E F G hdpos hDz hEz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCFG gamma A B C D E F G hdpos hDz hEz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCFG delta A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hEz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hl2 : C.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCFG
      A B C D E F G hdpos hDz hEz hl0 hl1 hl2
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g0 g1 g2 g3
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCFG gamma A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCFG delta A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BDEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BDEG
      A B C D E F G hdpos hCz hFz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BDEG l A B C D E F G hdpos hCz hFz g0 g1 g2 g3 g4 g5
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BDEG beta A B C D E F G hdpos hCz hFz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    subst hCz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BDEG delta A B C D E F G hdpos hCz hFz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BDEG epsilon A B C D E F G hdpos hCz hFz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BDEG zeta A B C D E F G hdpos hCz hFz g0
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BDEG eta A B C D E F G hdpos hCz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BDEG theta A B C D E F G hdpos hCz hFz g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BDEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hl2 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl3 : B.natDegree + D.natDegree + G.natDegree < d)
    (hl4 : 2 * D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ 3 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ G.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BDEG
      A B C D E F G hdpos hCz hFz hl0 hl1 hl2 hl3 hl4
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BDEG l A B C D E F G hdpos hCz hFz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BDEG l A B C D E F G hdpos hCz hFz g7 g8
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BDEG beta A B C D E F G hdpos hCz hFz g0 g1 g2 g3 g4
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BDEG gamma A B C D E F G hdpos hCz hFz g0 g1 g2 g3
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BDEG delta A B C D E F G hdpos hCz hFz g0 g1 g2 g3
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BDEG epsilon A B C D E F G hdpos hCz hFz g0 g1
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BDEG zeta A B C D E F G hdpos hCz hFz g0 g1
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BDEG eta A B C D E F G hdpos hCz hFz g0 g1 g2
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hCz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [piQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BDFG
      A B C D E F G hdpos hCz hEz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BDFG l A B C D E F G hdpos hCz hEz g0 g1 g2 g3 g4 g5
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BDFG beta A B C D E F G hdpos hCz hEz g0 g1 g2 g3
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BDFG gamma A B C D E F G hdpos hCz hEz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BDFG delta A B C D E F G hdpos hCz hEz g0 g1
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BDFG epsilon A B C D E F G hdpos hCz hEz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BDFG zeta A B C D E F G hdpos hCz hEz g0
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BDFG eta A B C D E F G hdpos hCz hEz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BDFG theta A B C D E F G hdpos hCz hEz g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : 3 * B.natDegree + F.natDegree < d)
    (hl2 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl3 : A.natDegree + 2 * F.natDegree < d)
    (hl4 : B.natDegree + D.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 5 * B.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ B.natDegree + D.natDegree + F.natDegree < d ∧ 3 * D.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ D.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (F.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BDFG
      A B C D E F G hdpos hCz hEz hl0 hl1 hl2 hl3 hl4
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BDFG l A B C D E F G hdpos hCz hEz g0 g1 g2 g3 g4 g5
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BDFG l A B C D E F G hdpos hCz hEz g6 g7 g8
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BDFG beta A B C D E F G hdpos hCz hEz g0 g1 g2 g3 g4
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BDFG gamma A B C D E F G hdpos hCz hEz g0 g1 g2
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BDFG delta A B C D E F G hdpos hCz hEz g0 g1 g2
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BDFG epsilon A B C D E F G hdpos hCz hEz g0 g1 g2
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BDFG zeta A B C D E F G hdpos hCz hEz g0 g1
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BDFG eta A B C D E F G hdpos hCz hEz g0 g1 g2
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BDFG theta A B C D E F G hdpos hCz hEz g0
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BEFG
      A B C D E F G hdpos hCz hDz
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BEFG l A B C D E F G hdpos hCz hDz g0 g1 g2 g3 g4
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BEFG beta A B C D E F G hdpos hCz hDz g0 g1 g2 g3
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BEFG gamma A B C D E F G hdpos hCz hDz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BEFG delta A B C D E F G hdpos hCz hDz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hCz
    subst hDz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BEFG zeta A B C D E F G hdpos hCz hDz g0
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BEFG eta A B C D E F G hdpos hCz hDz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BEFG theta A B C D E F G hdpos hCz hDz g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest19810_natDegree_lt_of_live_BEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hl0 : A.natDegree + 4 * B.natDegree < d)
    (hl1 : 2 * B.natDegree + G.natDegree < d)
    (hl2 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ G.natDegree < d))
    (hbzeta : zeta = 0 ∨ (F.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d)) :
    (xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF19810_natDegree_lt_of_live_BEFG
      A B C D E F G hdpos hCz hDz hl0 hl1 hl2
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_BEFG l A B C D E F G hdpos hCz hDz g0 g1 g2 g3 g4
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_BEFG beta A B C D E F G hdpos hCz hDz g0 g1 g2
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_BEFG gamma A B C D E F G hdpos hCz hDz g0
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_BEFG delta A B C D E F G hdpos hCz hDz g0 g1 g2
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_BEFG epsilon A B C D E F G hdpos hCz hDz g0 g1
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_BEFG zeta A B C D E F G hdpos hCz hDz g0
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_BEFG eta A B C D E F G hdpos hCz hDz g0 g1
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hCz
    subst hDz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [xiQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [xiQuarticChamberRest19810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hl0 : 3 * B.natDegree + F.natDegree < d)
    (hl1 : A.natDegree + 2 * F.natDegree < d)
    (hl2 : B.natDegree + E.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 5 * B.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (4 * B.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (B.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (F.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BEFG
      A B C D E F G hdpos hCz hDz hl0 hl1 hl2
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BEFG l A B C D E F G hdpos hCz hDz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BEFG l A B C D E F G hdpos hCz hDz g7 g8
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BEFG beta A B C D E F G hdpos hCz hDz g0 g1 g2 g3 g4
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BEFG gamma A B C D E F G hdpos hCz hDz g0 g1 g2
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BEFG delta A B C D E F G hdpos hCz hDz g0 g1 g2
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BEFG epsilon A B C D E F G hdpos hCz hDz g0
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BEFG zeta A B C D E F G hdpos hCz hDz g0 g1 g2
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BEFG eta A B C D E F G hdpos hCz hDz g0 g1
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BEFG theta A B C D E F G hdpos hCz hDz g0
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : C.natDegree + F.natDegree < d)
    (hl2 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCDEF
      A B C D E F G hdpos hGz hl0 hl1 hl2
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDEF l A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDEF beta A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDEF gamma A B C D E F G hdpos hGz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDEF delta A B C D E F G hdpos hGz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEF epsilon A B C D E F G hdpos hGz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDEF zeta A B C D E F G hdpos hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDEF eta A B C D E F G hdpos hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDEF theta A B C D E F G hdpos hGz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hl2 : A.natDegree + 2 * D.natDegree < d)
    (hl3 : 2 * B.natDegree + E.natDegree < d)
    (hl4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl5 : D.natDegree + F.natDegree < d)
    (hl6 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEF
      A B C D E F G hdpos hGz hl0 hl1 hl2 hl3 hl4 hl5 hl6
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDEF l A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDEF beta A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5 g6
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDEF gamma A B C D E F G hdpos hGz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDEF delta A B C D E F G hdpos hGz g0 g1 g2 g3
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEF epsilon A B C D E F G hdpos hGz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDEF zeta A B C D E F G hdpos hGz g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDEF eta A B C D E F G hdpos hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDEF theta A B C D E F G hdpos hGz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEF
      A B C D E F G hdpos hGz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDEF l A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDEF beta A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDEF gamma A B C D E F G hdpos hGz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDEF delta A B C D E F G hdpos hGz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEF epsilon A B C D E F G hdpos hGz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDEF zeta A B C D E F G hdpos hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDEF eta A B C D E F G hdpos hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDEF theta A B C D E F G hdpos hGz g0
  simp only [kappaQuarticChamberRest6810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest9810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * D.natDegree < d)
    (hl2 : 2 * B.natDegree + E.natDegree < d)
    (hl3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl4 : D.natDegree + F.natDegree < d)
    (hl5 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF9810_natDegree_lt_of_live_BCDEF
      A B C D E F G hdpos hGz hl0 hl1 hl2 hl3 hl4 hl5
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDEF l A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDEF beta A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5 g6
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDEF gamma A B C D E F G hdpos hGz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDEF delta A B C D E F G hdpos hGz g0 g1 g2 g3
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEF epsilon A B C D E F G hdpos hGz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDEF zeta A B C D E F G hdpos hGz g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDEF eta A B C D E F G hdpos hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDEF theta A B C D E F G hdpos hGz g0
  simp only [muQuarticChamberRest9810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest2000810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : 4 * B.natDegree + C.natDegree < d)
    (hl2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hl3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl4 : 3 * B.natDegree + F.natDegree < d)
    (hl5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hl6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hl9 : C.natDegree + D.natDegree + F.natDegree < d)
    (hl10 : C.natDegree + 2 * E.natDegree < d)
    (hl11 : 2 * D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 3 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * A.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ 2 * B.natDegree + C.natDegree + D.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + F.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree + E.natDegree < d ∧ 3 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCDEF
      A B C D E F G hdpos hGz hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCDEF l A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCDEF l A B C D E F G hdpos hGz g19 g20 g21 g22 g23
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCDEF beta A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCDEF gamma A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5 g6 g7
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCDEF delta A B C D E F G hdpos hGz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEF epsilon A B C D E F G hdpos hGz g0 g1 g2 g3 g4
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCDEF zeta A B C D E F G hdpos hGz g0 g1 g2 g3 g4
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCDEF eta A B C D E F G hdpos hGz g0 g1 g2
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCDEF theta A B C D E F G hdpos hGz g0 g1
  simp only [piQuarticChamberRest2000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : B.natDegree + G.natDegree < d)
    (hl2 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCDEG
      A B C D E F G hdpos hFz hl0 hl1 hl2
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDEG l A B C D E F G hdpos hFz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDEG beta A B C D E F G hdpos hFz g0 g1 g2 g3 g4 g5 g6
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDEG gamma A B C D E F G hdpos hFz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDEG delta A B C D E F G hdpos hFz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEG epsilon A B C D E F G hdpos hFz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDEG zeta A B C D E F G hdpos hFz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDEG eta A B C D E F G hdpos hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDEG theta A B C D E F G hdpos hFz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * D.natDegree < d)
    (hl2 : 2 * B.natDegree + E.natDegree < d)
    (hl3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl4 : C.natDegree + G.natDegree < d)
    (hl5 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEG
      A B C D E F G hdpos hFz hl0 hl1 hl2 hl3 hl4 hl5
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDEG l A B C D E F G hdpos hFz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDEG beta A B C D E F G hdpos hFz g0 g1 g2 g3 g4 g5
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDEG gamma A B C D E F G hdpos hFz g0 g1 g2 g3
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDEG delta A B C D E F G hdpos hFz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEG epsilon A B C D E F G hdpos hFz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDEG zeta A B C D E F G hdpos hFz g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDEG eta A B C D E F G hdpos hFz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDEG theta A B C D E F G hdpos hFz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : B.natDegree + 2 * C.natDegree < d)
    (hl2 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCDEG
      A B C D E F G hdpos hFz hl0 hl1 hl2
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDEG l A B C D E F G hdpos hFz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDEG beta A B C D E F G hdpos hFz g0 g1 g2 g3 g4 g5 g6
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDEG gamma A B C D E F G hdpos hFz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDEG delta A B C D E F G hdpos hFz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEG epsilon A B C D E F G hdpos hFz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDEG zeta A B C D E F G hdpos hFz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDEG eta A B C D E F G hdpos hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDEG theta A B C D E F G hdpos hFz g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hl2 : 4 * B.natDegree + C.natDegree < d)
    (hl3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hl4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hl6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl8 : 4 * C.natDegree < d)
    (hl9 : B.natDegree + D.natDegree + G.natDegree < d)
    (hl10 : 2 * C.natDegree + G.natDegree < d)
    (hl11 : C.natDegree + 2 * E.natDegree < d)
    (hl12 : 2 * D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 3 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ 2 * B.natDegree + C.natDegree + D.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ C.natDegree + D.natDegree + E.natDegree < d ∧ 3 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEG
      A B C D E F G hdpos hFz hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCDEG l A B C D E F G hdpos hFz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCDEG l A B C D E F G hdpos hFz g16 g17 g18
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCDEG beta A B C D E F G hdpos hFz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCDEG gamma A B C D E F G hdpos hFz g0 g1 g2 g3 g4 g5 g6
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCDEG delta A B C D E F G hdpos hFz g0 g1 g2 g3 g4 g5 g6
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEG epsilon A B C D E F G hdpos hFz g0 g1 g2 g3
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCDEG zeta A B C D E F G hdpos hFz g0 g1 g2 g3
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCDEG eta A B C D E F G hdpos hFz g0 g1 g2 g3
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCDEG theta A B C D E F G hdpos hFz g0
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : B.natDegree + G.natDegree < d)
    (hl2 : C.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCDFG
      A B C D E F G hdpos hEz hl0 hl1 hl2
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDFG l A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDFG beta A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDFG gamma A B C D E F G hdpos hEz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDFG delta A B C D E F G hdpos hEz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG epsilon A B C D E F G hdpos hEz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDFG zeta A B C D E F G hdpos hEz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDFG eta A B C D E F G hdpos hEz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDFG theta A B C D E F G hdpos hEz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hl2 : A.natDegree + 2 * D.natDegree < d)
    (hl3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl4 : C.natDegree + G.natDegree < d)
    (hl5 : D.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCDFG
      A B C D E F G hdpos hEz hl0 hl1 hl2 hl3 hl4 hl5
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDFG l A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDFG beta A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDFG gamma A B C D E F G hdpos hEz g0 g1 g2 g3
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDFG delta A B C D E F G hdpos hEz g0 g1 g2 g3
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG epsilon A B C D E F G hdpos hEz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDFG zeta A B C D E F G hdpos hEz g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDFG eta A B C D E F G hdpos hEz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDFG theta A B C D E F G hdpos hEz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : B.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCDFG
      A B C D E F G hdpos hEz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDFG l A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDFG beta A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDFG gamma A B C D E F G hdpos hEz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDFG delta A B C D E F G hdpos hEz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG epsilon A B C D E F G hdpos hEz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDFG zeta A B C D E F G hdpos hEz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDFG eta A B C D E F G hdpos hEz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDFG theta A B C D E F G hdpos hEz g0
  simp only [kappaQuarticChamberRest6810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest9810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * D.natDegree < d)
    (hl2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl3 : C.natDegree + G.natDegree < d)
    (hl4 : D.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF9810_natDegree_lt_of_live_BCDFG
      A B C D E F G hdpos hEz hl0 hl1 hl2 hl3 hl4
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDFG l A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDFG beta A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDFG gamma A B C D E F G hdpos hEz g0 g1 g2 g3
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDFG delta A B C D E F G hdpos hEz g0 g1 g2 g3
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG epsilon A B C D E F G hdpos hEz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDFG zeta A B C D E F G hdpos hEz g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDFG eta A B C D E F G hdpos hEz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDFG theta A B C D E F G hdpos hEz g0
  simp only [muQuarticChamberRest9810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest2000810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : 4 * B.natDegree + C.natDegree < d)
    (hl2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hl3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl4 : 3 * B.natDegree + F.natDegree < d)
    (hl5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl7 : B.natDegree + D.natDegree + G.natDegree < d)
    (hl8 : 2 * C.natDegree + G.natDegree < d)
    (hl9 : C.natDegree + D.natDegree + F.natDegree < d)
    (hl10 : 2 * G.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree + D.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ B.natDegree + D.natDegree + F.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d ∧ 3 * D.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCDFG
      A B C D E F G hdpos hEz hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCDFG l A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCDFG l A B C D E F G hdpos hEz g15 g16 g17 g18
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCDFG beta A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCDFG gamma A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCDFG delta A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG epsilon A B C D E F G hdpos hEz g0 g1 g2 g3
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCDFG zeta A B C D E F G hdpos hEz g0 g1 g2 g3
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCDFG eta A B C D E F G hdpos hEz g0 g1 g2 g3
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCDFG theta A B C D E F G hdpos hEz g0 g1
  simp only [piQuarticChamberRest2000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : B.natDegree + 2 * C.natDegree < d)
    (hl2 : C.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCDFG
      A B C D E F G hdpos hEz hl0 hl1 hl2
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDFG l A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDFG beta A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDFG gamma A B C D E F G hdpos hEz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDFG delta A B C D E F G hdpos hEz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG epsilon A B C D E F G hdpos hEz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDFG zeta A B C D E F G hdpos hEz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDFG eta A B C D E F G hdpos hEz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDFG theta A B C D E F G hdpos hEz g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hl2 : 4 * B.natDegree + C.natDegree < d)
    (hl3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hl4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl5 : 3 * B.natDegree + F.natDegree < d)
    (hl6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl8 : 4 * C.natDegree < d)
    (hl9 : A.natDegree + 2 * F.natDegree < d)
    (hl10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hl11 : 2 * C.natDegree + G.natDegree < d)
    (hl12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree + D.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ B.natDegree + D.natDegree + F.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d ∧ 3 * D.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BCDFG
      A B C D E F G hdpos hEz hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCDFG l A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCDFG l A B C D E F G hdpos hEz g15 g16 g17 g18
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCDFG beta A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCDFG gamma A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCDFG delta A B C D E F G hdpos hEz g0 g1 g2 g3 g4 g5 g6
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG epsilon A B C D E F G hdpos hEz g0 g1 g2 g3
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCDFG zeta A B C D E F G hdpos hEz g0 g1 g2 g3
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCDFG eta A B C D E F G hdpos hEz g0 g1 g2 g3
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCDFG theta A B C D E F G hdpos hEz g0 g1
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hl0 : B.natDegree + G.natDegree < d)
    (hl1 : C.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCEFG
      A B C D E F G hdpos hDz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCEFG l A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCEFG beta A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCEFG gamma A B C D E F G hdpos hDz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCEFG delta A B C D E F G hdpos hDz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCEFG zeta A B C D E F G hdpos hDz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCEFG eta A B C D E F G hdpos hDz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCEFG theta A B C D E F G hdpos hDz g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hl2 : 2 * B.natDegree + E.natDegree < d)
    (hl3 : C.natDegree + G.natDegree < d)
    (hl4 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCEFG
      A B C D E F G hdpos hDz hl0 hl1 hl2 hl3 hl4
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCEFG l A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCEFG beta A B C D E F G hdpos hDz g0 g1 g2 g3 g4
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCEFG gamma A B C D E F G hdpos hDz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCEFG delta A B C D E F G hdpos hDz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCEFG epsilon A B C D E F G hdpos hDz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCEFG zeta A B C D E F G hdpos hDz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCEFG eta A B C D E F G hdpos hDz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCEFG theta A B C D E F G hdpos hDz g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest6810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hl0 : B.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCEFG
      A B C D E F G hdpos hDz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCEFG l A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCEFG beta A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCEFG gamma A B C D E F G hdpos hDz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCEFG delta A B C D E F G hdpos hDz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCEFG zeta A B C D E F G hdpos hDz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCEFG eta A B C D E F G hdpos hDz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCEFG theta A B C D E F G hdpos hDz g0
  simp only [kappaQuarticChamberRest6810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest9810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : 2 * B.natDegree + E.natDegree < d)
    (hl2 : C.natDegree + G.natDegree < d)
    (hl3 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF9810_natDegree_lt_of_live_BCEFG
      A B C D E F G hdpos hDz hl0 hl1 hl2 hl3
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCEFG l A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCEFG beta A B C D E F G hdpos hDz g0 g1 g2 g3 g4
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCEFG gamma A B C D E F G hdpos hDz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCEFG delta A B C D E F G hdpos hDz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCEFG epsilon A B C D E F G hdpos hDz g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCEFG zeta A B C D E F G hdpos hDz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCEFG eta A B C D E F G hdpos hDz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCEFG theta A B C D E F G hdpos hDz g0
  simp only [muQuarticChamberRest9810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest2000810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hl0 : 4 * B.natDegree + C.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hl2 : 3 * B.natDegree + F.natDegree < d)
    (hl3 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hl4 : B.natDegree + E.natDegree + F.natDegree < d)
    (hl5 : 2 * C.natDegree + G.natDegree < d)
    (hl6 : C.natDegree + 2 * E.natDegree < d)
    (hl7 : 2 * G.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ 3 * C.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCEFG
      A B C D E F G hdpos hDz hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCEFG l A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCEFG l A B C D E F G hdpos hDz g14 g15 g16
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCEFG beta A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCEFG gamma A B C D E F G hdpos hDz g0 g1 g2 g3 g4
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCEFG delta A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCEFG epsilon A B C D E F G hdpos hDz g0 g1 g2
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCEFG zeta A B C D E F G hdpos hDz g0 g1 g2 g3
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCEFG eta A B C D E F G hdpos hDz g0 g1 g2
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCEFG theta A B C D E F G hdpos hDz g0 g1
  simp only [piQuarticChamberRest2000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hl0 : B.natDegree + 2 * C.natDegree < d)
    (hl1 : C.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCEFG
      A B C D E F G hdpos hDz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCEFG l A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCEFG beta A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCEFG gamma A B C D E F G hdpos hDz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCEFG delta A B C D E F G hdpos hDz g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCEFG zeta A B C D E F G hdpos hDz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCEFG eta A B C D E F G hdpos hDz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCEFG theta A B C D E F G hdpos hDz g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hl0 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hl1 : 4 * B.natDegree + C.natDegree < d)
    (hl2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hl3 : 3 * B.natDegree + F.natDegree < d)
    (hl4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hl5 : 4 * C.natDegree < d)
    (hl6 : A.natDegree + 2 * F.natDegree < d)
    (hl7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hl8 : 2 * C.natDegree + G.natDegree < d)
    (hl9 : C.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ 3 * C.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BCEFG
      A B C D E F G hdpos hDz hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCEFG l A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCEFG l A B C D E F G hdpos hDz g14 g15 g16
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCEFG beta A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCEFG gamma A B C D E F G hdpos hDz g0 g1 g2 g3 g4
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCEFG delta A B C D E F G hdpos hDz g0 g1 g2 g3 g4 g5
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCEFG epsilon A B C D E F G hdpos hDz g0 g1 g2
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCEFG zeta A B C D E F G hdpos hDz g0 g1 g2 g3
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCEFG eta A B C D E F G hdpos hDz g0 g1 g2
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCEFG theta A B C D E F G hdpos hDz g0 g1
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BDEFG
      A B C D E F G hdpos hCz hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BDEFG l A B C D E F G hdpos hCz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BDEFG beta A B C D E F G hdpos hCz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BDEFG gamma A B C D E F G hdpos hCz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BDEFG delta A B C D E F G hdpos hCz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BDEFG epsilon A B C D E F G hdpos hCz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BDEFG zeta A B C D E F G hdpos hCz g0
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BDEFG eta A B C D E F G hdpos hCz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BDEFG theta A B C D E F G hdpos hCz g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hl2 : 3 * B.natDegree + F.natDegree < d)
    (hl3 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl4 : A.natDegree + 2 * F.natDegree < d)
    (hl5 : B.natDegree + D.natDegree + G.natDegree < d)
    (hl6 : B.natDegree + E.natDegree + F.natDegree < d)
    (hl7 : 2 * D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + F.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ 3 * D.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (F.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BDEFG
      A B C D E F G hdpos hCz hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BDEFG l A B C D E F G hdpos hCz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BDEFG l A B C D E F G hdpos hCz g10 g11 g12 g13
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BDEFG beta A B C D E F G hdpos hCz g0 g1 g2 g3 g4 g5 g6 g7
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BDEFG gamma A B C D E F G hdpos hCz g0 g1 g2 g3 g4
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BDEFG delta A B C D E F G hdpos hCz g0 g1 g2 g3 g4
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BDEFG epsilon A B C D E F G hdpos hCz g0 g1 g2
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BDEFG zeta A B C D E F G hdpos hCz g0 g1 g2
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BDEFG eta A B C D E F G hdpos hCz g0 g1 g2
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BDEFG theta A B C D E F G hdpos hCz g0
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : B.natDegree + G.natDegree < d)
    (hl2 : C.natDegree + F.natDegree < d)
    (hl3 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF1810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0
  simp only [kappaQuarticChamberRest1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hl2 : A.natDegree + 2 * D.natDegree < d)
    (hl3 : 2 * B.natDegree + E.natDegree < d)
    (hl4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl5 : C.natDegree + G.natDegree < d)
    (hl6 : D.natDegree + F.natDegree < d)
    (hl7 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0
  simp only [muQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : B.natDegree + G.natDegree < d)
    (hl2 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0
  simp only [kappaQuarticChamberRest6810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest9810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * D.natDegree < d)
    (hl2 : 2 * B.natDegree + E.natDegree < d)
    (hl3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl4 : C.natDegree + G.natDegree < d)
    (hl5 : D.natDegree + F.natDegree < d)
    (hl6 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF9810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0
  simp only [muQuarticChamberRest9810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest2000810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : 4 * B.natDegree + C.natDegree < d)
    (hl2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hl3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hl4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl5 : 3 * B.natDegree + F.natDegree < d)
    (hl6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hl7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl9 : B.natDegree + D.natDegree + G.natDegree < d)
    (hl10 : B.natDegree + E.natDegree + F.natDegree < d)
    (hl11 : 2 * C.natDegree + G.natDegree < d)
    (hl12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hl13 : C.natDegree + 2 * E.natDegree < d)
    (hl14 : 2 * D.natDegree + E.natDegree < d)
    (hl15 : 2 * G.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 3 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * A.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ 2 * B.natDegree + C.natDegree + D.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ B.natDegree + D.natDegree + F.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree + E.natDegree < d ∧ 3 * D.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest2000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g20 g21 g22 g23 g24 g25
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2 g3 g4
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2 g3 g4
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1 g2 g3
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1
  simp only [piQuarticChamberRest2000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 2 * B.natDegree + D.natDegree < d)
    (hl1 : B.natDegree + 2 * C.natDegree < d)
    (hl2 : C.natDegree + F.natDegree < d)
    (hl3 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0
  simp only [kappaQuarticChamberRest7810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hl2 : 4 * B.natDegree + C.natDegree < d)
    (hl3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hl4 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hl5 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl6 : 3 * B.natDegree + F.natDegree < d)
    (hl7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hl8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl9 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl10 : 4 * C.natDegree < d)
    (hl11 : A.natDegree + 2 * F.natDegree < d)
    (hl12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hl13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hl14 : 2 * C.natDegree + G.natDegree < d)
    (hl15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hl16 : C.natDegree + 2 * E.natDegree < d)
    (hl17 : 2 * D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 3 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * A.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ 2 * B.natDegree + C.natDegree + D.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ B.natDegree + D.natDegree + F.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree + E.natDegree < d ∧ 3 * D.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g20 g21 g22 g23 g24 g25
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2 g3 g4
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2 g3 g4
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1 g2 g3
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1
  simp only [piQuarticChamberRest3810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8


end QuarticChamberRests4810

end Max11DegreeRoutes
