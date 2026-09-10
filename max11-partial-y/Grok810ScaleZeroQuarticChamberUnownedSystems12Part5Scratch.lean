import Grok810ScaleZeroQuarticChamberFacesScratch
import Grok810ScaleZeroQuarticChamberColumnsScratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsScratch
import Grok810ScaleZeroQuarticChamberColumns2Scratch
import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberKills2Scratch
import Grok810ScaleZeroQuarticChamberNuFacesScratch
import Grok810ScaleZeroQuarticChamberColumns3Scratch
import Grok810ScaleZeroQuarticChamberRests3Scratch
import Grok810ScaleZeroQuarticChamberKills3Scratch
import Grok810ScaleZeroQuarticChamberRests4Scratch
import Grok810ScaleZeroQuarticChamberInnerScratch
import Grok810ScaleZeroQuarticChamberKills4Scratch
import Grok810ScaleZeroQuarticChamberColumns5Scratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsScratch
import Grok810ScaleZeroQuarticChamberRests6Scratch
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
import Grok810ScaleZeroQuarticChamberUnownedPacketsScratch
import Grok810ScaleZeroQuarticChamberUnownedColumns1Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns4Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns5Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests2Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests3Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests4Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills1Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills2Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills3Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills4Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills5Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns4Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns5Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns6Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns7Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns8Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns9Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns10Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests3Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests4Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests5Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests6Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests7Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests8Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests9Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests10Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests11Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemBridges1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemBridges2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems12Part4Scratch

/-! # Unowned multi-carrier systems, part 12/15

4 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
Singular-lifted top-coefficient system.  Every load column of every row
carries an exact rational Farkas verdict (`dominated`, `dominated-hnc` or
a named band).
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

section QuarticChamberUnownedSystems12810

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` leaf 6 dies on the 7-carrier system (κ, μ, ν, ξ, ο, π, Π). -/
theorem quarticRefinedBCDEFG7L6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG7L6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG; omega
  have hdz0 : 0 < A.natDegree + 3 * B.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13 hcq14; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13 hcq14; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13 hcq14; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
  have hr0 : (kappaQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6005810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11; omega) hz0l hz0beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos; omega)) hz0delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos; omega)) hz0zeta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos; omega)) (Or.inr (by omega))
  have hct0 := kappaQuarticChamberFace6005810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega
  rw [degreeZeroKappaQuartic810_eq_face6005_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff + (5 / 16 : k) * C.leadingCoeff * F.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13 hcq14; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13 hcq14; omega)
  have hr1 : (muQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest6005810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11 hcq14; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11; omega) hz1l hz1beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos; omega)) (Or.inr (by omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos hcq11; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos; omega))
  have hct1 := muQuarticChamberFace6005810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroMuQuartic810_eq_face6005_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (15 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff + (-5 / 64 : k) * A.leadingCoeff * B.leadingCoeff * F.leadingCoeff + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp3 : 0 < A.natDegree + 4 * B.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1; omega
  have hdz3 : 0 < A.natDegree + 4 * B.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 4 * B.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13 hcq14; omega)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13 hcq14; omega)
  have hr3 : (xiQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 4 * B.natDegree :=
    xiQuarticChamberRest6003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 (by omega) (by omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11; omega) (by omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by omega) hz3l hz3beta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos hcq11; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos; omega))
  have hct3 := xiQuarticChamberFace6003810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3; omega)
  have hq3 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3; omega
  rw [degreeZeroXiQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : (-15 / 2048 : k) * A.leadingCoeff * B.leadingCoeff ^ 4 + (45 / 512 : k) * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (-5 / 64 : k) * B.leadingCoeff ^ 2 * G.leadingCoeff + (-25 / 128 : k) * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (5 / 32 : k) * F.leadingCoeff ^ 2 = 0 :=
    hct3.symm.trans hq3
  have hdp5 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3; omega
  have hdz5 : 0 < 2 * A.natDegree + 4 * B.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3 hdp5; omega
  have hz5l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11 hcq13 hcq14; omega)
  have hz5beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13 hcq14; omega)
  have hr5 : (piQuarticChamberRest6007810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6007810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz5 (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq14; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11 hcq14; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq13; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq3 hcq7 hcq9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq11; omega) hz5l hz5beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos hcq11; omega)) (Or.inr (by omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos hcq11; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos hcq11; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq1 hcq3 hcq7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hApos; omega))
  have hct5 := piQuarticChamberFace6007810_coeff_top hAne hBne hCne hFne hGne (D := D) (E := E) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3 hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3 hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3 hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3 hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3 hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3 hdp5 hdz5; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3 hdp5 hdz5; omega)
  have hq5 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx22 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hdz0 hdp1 hdz1 hdp3 hdz3 hdp5 hdz5; omega
  rw [degreeZeroPiQuartic810_eq_face6007_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr5,
    add_zero] at hq5
  have hin5 : (15 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 + (-45 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (5 / 64 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 32 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (-5 / 16 : k) * A.leadingCoeff * F.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct5.symm.trans hq5
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : F.leadingCoeff ^ 2 * G.leadingCoeff ^ 2 = 0 := by
    linear_combination ((99 / 1120 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff ^ 2 + (1011 / 14000 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 * G.leadingCoeff + (-594 / 875 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff + (3267 / 7000 : k) * A.leadingCoeff * B.leadingCoeff * F.leadingCoeff ^ 2 + (2761 / 3500 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 * G.leadingCoeff + (1872 / 875 : k) * B.leadingCoeff * G.leadingCoeff ^ 2 + (-33 / 70 : k) * C.leadingCoeff * F.leadingCoeff * G.leadingCoeff) * hin0 + ((33 / 280 : k) * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 3 + (-2411 / 1750 : k) * B.leadingCoeff ^ 2 * C.leadingCoeff * G.leadingCoeff + (-792 / 875 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 * F.leadingCoeff + (187 / 70 : k) * B.leadingCoeff * F.leadingCoeff * G.leadingCoeff + (1089 / 1750 : k) * C.leadingCoeff * F.leadingCoeff ^ 2) * hin1 + ((11 / 70 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (-131 / 1750 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff + (-1056 / 875 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (726 / 875 : k) * A.leadingCoeff * F.leadingCoeff ^ 2 + (66 / 125 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (2696 / 875 : k) * G.leadingCoeff ^ 2) * hin3 + ((11 / 140 : k) * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (-599 / 1750 : k) * B.leadingCoeff ^ 2 * G.leadingCoeff + (-528 / 875 : k) * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (363 / 875 : k) * F.leadingCoeff ^ 2) * hin5
  exact (mul_ne_zero (pow_ne_zero 2 hFc) (pow_ne_zero 2 hGc)) ht

end QuarticChamberUnownedSystems12810

end Max11DegreeRoutes
