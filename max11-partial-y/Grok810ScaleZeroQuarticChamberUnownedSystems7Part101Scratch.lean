import Mathlib
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRefineScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests6Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemBridges1Scratch

/-! # Unowned multi-carrier systems, part 7/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems7810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCDEG` / `CG·DD·CCC` leaf 2: the 10 face rows force `d ^ 2 * e = 0`. -/
theorem quarticUnownedSystemBCDEG30L2810_cert
    (a b c d e f g : k)
    (hr0 : (-15 / 128 : k) * b * c ^ 2 + (5 / 16 : k) * b * g + (5 / 16 : k) * d * e = 0)
    (hr1 : (-5 / 128 : k) * a * d ^ 2 + (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr2 : (15 / 1024 : k) * a * b * c ^ 2 + (-5 / 128 : k) * a * b * g + (-5 / 128 : k) * a * d * e + (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr3 : (15 / 256 : k) * a * b * c * d + (-15 / 128 : k) * c ^ 2 * e + (-15 / 128 : k) * c * d ^ 2 + (5 / 16 : k) * e * g = 0)
    (hr4 : (15 / 16384 : k) * a ^ 2 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 2 * b * g + (-5 / 2048 : k) * a ^ 2 * d * e + (15 / 1024 : k) * a * c ^ 2 * d + (-5 / 128 : k) * a * d * g = 0)
    (hr5 : (5 / 32 : k) * a * c * d ^ 2 + (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr6 : (15 / 16384 : k) * a ^ 3 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 3 * b * g + (-5 / 2048 : k) * a ^ 3 * d * e + (15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (-5 / 256 : k) * a ^ 2 * d * g = 0)
    (hr7 : (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr8 : (45 / 2048 : k) * a * c ^ 2 * d + (-15 / 256 : k) * a * d * g = 0)
    (hr9 : (-15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (5 / 256 : k) * a ^ 2 * d * g = 0)
    (hDc : (d : k) ≠ 0)
    (hEc : (e : k) ≠ 0) :
    False := by
  have ht : d ^ 2 * e = 0 := by
    linear_combination ((16 / 5 : k) * d) * hr0 + ((-16 / 5 : k) * b) * hr7
  exact (mul_ne_zero (pow_ne_zero 2 hDc) hEc) ht

end QuarticChamberUnownedSystems7810

end Max11DegreeRoutes
/-! # Unowned multi-carrier systems, part 7/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems7810

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCDEG` / `CG·DD·CCC` leaf 2 dies on the 10-carrier system (κ, μ, ν, ξ, ο, π, Π, N₂, N₃, N₄). -/
theorem quarticRefinedBCDEG30L2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEG30L2810 A B C D E F G)
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
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp0 : 0 < B.natDegree + 2 * C.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn; omega
  have hdz0 : 0 < B.natDegree + 2 * C.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * D.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 h; omega)
      · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 h; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 h; omega)
      · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 h; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 h; omega)
      · exact Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 h; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq4; omega)
  have hr0 : (kappaQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest6004810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hFz (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq2; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq2 hcq4; omega) hz0l hz0beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)) hz0delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hApos; omega)) hz0zeta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq2; omega))
  have hct0 := kappaQuarticChamberFace6004810_coeff_top hBne hCne hDne hEne hGne (A := A) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega
  rw [degreeZeroKappaQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * E.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp7 : A.natDegree < 2 * C.natDegree + D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega
  have hdz7 : 0 < 2 * C.natDegree + D.natDegree := by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp7; omega
  have hz7l : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * E.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz7beta : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz7delta : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ G.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz7zeta : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ E.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hr7 : (n2QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + D.natDegree :=
    n2QuarticChamberRest6000810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz7 hFz (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq2; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq2 hcq3; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq2 hcq4; omega) hz7l hz7beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)) hz7delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)) hz7zeta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by omega))
  have hct7 := n2QuarticChamberFace6000810_coeff_top hCne hDne hGne (A := A) (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp7 hdz7; omega)
  have hq7 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp7 hdz7 hle; omega
  rw [degreeZeroN2Quartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr7,
    add_zero] at hq7
  have hin7 : (-15 / 128 : k) * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * G.leadingCoeff = 0 :=
    hct7.symm.trans hq7
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have ht : D.leadingCoeff ^ 2 * E.leadingCoeff = 0 := by
    linear_combination ((16 / 5 : k) * D.leadingCoeff) * hin0 + ((-16 / 5 : k) * B.leadingCoeff) * hin7
  exact (mul_ne_zero (pow_ne_zero 2 hDc) hEc) ht

end QuarticChamberUnownedSystems7810

end Max11DegreeRoutes
/-! # Unowned multi-carrier systems, part 7/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems7810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCDEG` / `CG·DD·CCC` leaf 4: the 5 face rows force `d * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBCDEG30L4810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 128 : k) * a * d ^ 2 + (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr1 : (5 / 32 : k) * a * c * d ^ 2 + (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr2 : (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr3 : (45 / 2048 : k) * a * c ^ 2 * d + (-15 / 256 : k) * a * d * g = 0)
    (hr4 : (-15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (5 / 256 : k) * a ^ 2 * d * g = 0)
    (hDc : (d : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : d * g ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * c * d) * hr0 + ((18 / 55 : k) * d) * hr1 + ((-3 / 11 : k) * c ^ 2 + (104 / 55 : k) * g) * hr2
  exact (mul_ne_zero hDc (pow_ne_zero 2 hGc)) ht

end QuarticChamberUnownedSystems7810

end Max11DegreeRoutes
/-! # Unowned multi-carrier systems, part 7/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
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

section QuarticChamberUnownedSystems7810

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCDEG` / `CG·DD·CCC` leaf 4 dies on the 5-carrier system (μ, π, N₂, N₃, N₄). -/
theorem quarticRefinedBCDEG30L4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEG30L4810 A B C D E F G)
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
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hx0, hx1, hx2, hx3⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn; omega
  have hdz0 : 0 < A.natDegree + 2 * D.natDegree := by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4 hApos; omega)
  have hr0 : (muQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest6003810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hFz (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq3; omega) hz0l hz0beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4 hApos; omega)) hz0delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hApos; omega))
  have hct0 := muQuarticChamberFace6003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega
  rw [degreeZeroMuQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff ^ 2 + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0; omega
  have hdz1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact absurd h (by clear * - hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)
  have hr1 : (piQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest6004810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hFz (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq2; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq2 hcq3; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq2 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq3; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq3 hcq4; omega) hz1l hz1beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)) hz1delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hApos; omega))
  have hct1 := piQuarticChamberFace6004810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega
  rw [degreeZeroPiQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (5 / 32 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hdp2 : A.natDegree < 2 * C.natDegree + D.natDegree := by
    clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1; omega
  have hdz2 : 0 < 2 * C.natDegree + D.natDegree := by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2; omega
  have hz2l : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * E.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz2beta : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz2delta : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ G.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz2zeta : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ E.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hAF hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
  have hz2theta : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq2; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hFn hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)
  have hr2 : (n2QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + D.natDegree :=
    n2QuarticChamberRest6000810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hFz (by clear * - hx0 hx1 hx2 hx3 hcq2; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq2 hcq3; omega) (by clear * - hx0 hx1 hx2 hx3 hcq2 hcq4; omega) hz2l hz2beta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hApos; omega)) hz2delta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)) hz2zeta (Or.inr (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq4; omega)) hz2theta
  have hct2 := n2QuarticChamberFace6000810_coeff_top hCne hDne hGne (A := A) (B := B) (E := E) (F := F) (by clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2; omega)
  have hq2 : (degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hnu hkap
    clear * - hx0 hx1 hx2 hx3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdz0 hdp1 hdz1 hdp2 hdz2 hle; omega
  rw [degreeZeroN2Quartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : (-15 / 128 : k) * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : D.leadingCoeff * G.leadingCoeff ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * C.leadingCoeff * D.leadingCoeff) * hin0 + ((18 / 55 : k) * D.leadingCoeff) * hin1 + ((-3 / 11 : k) * C.leadingCoeff ^ 2 + (104 / 55 : k) * G.leadingCoeff) * hin2
  exact (mul_ne_zero hDc (pow_ne_zero 2 hGc)) ht


end QuarticChamberUnownedSystems7810

end Max11DegreeRoutes
