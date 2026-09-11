import Grok810ScaleZeroQuarticSigmaLadderPart60Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part5Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part4Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part3Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part2Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part1Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part0Scratch
import Grok810ScaleZeroQuarticChamberExhaust1Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part01Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part02Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part03Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part04Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part05Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part06Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part07Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part08Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part09Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part10Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part11Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part12Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part13Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part14Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part15Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part0Scratch

/-! # Cost-argmin chamber exhaust (4/4), `(8,10)` scale zero

The 1 live-letter sets with |S| ∈ {6}.  Each theorem runs the case tree
of `CHAMBERS.md` §1: a linear tournament for `β = min s|_{B,C}`,
`q = min s|_{D,E}`, `r = min s|_{F,G}`, then `μ₂ = min(q,r)`,
`ω = min(β,q)`, then the three cost types `2μ₂`, `β+r`, `2β+ω`
against each other.  Branches no chamber matches are ℚ-infeasible
(exact Farkas certificates in
`scripts/check_810_quartic_chambers_lean.py`) and close by `omega`.
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

section QuarticChamberExhaust810

set_option maxHeartbeats 64000000 in
/-- Every point of cone `A` with a live letter sits in exactly one
cost-argmin chamber. -/
theorem quarticChamberSupport810_of
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    QuarticChamberSupport810 A B C D E F G := by
  by_cases hBz : B = 0
  · -- B vanishes
    by_cases hCz : C = 0
    · -- C vanishes
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact (quarticSigmaSupportCone810_of_allZero A B C D E F G hA l beta gamma delta epsilon zeta eta theta hjdiv hder hBz hCz hDz hEz hFz hGz).elim
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_G A B C D E F G hA hBz hCz hDz hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_F A B C D E F G hA hBz hCz hDz hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_FG A B C D E F G hA hBz hCz hDz hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_E A B C D E F G hA hBz hCz hDz hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_EG A B C D E F G hA hBz hCz hDz hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_EF A B C D E F G hA hBz hCz hDz hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_EFG A B C D E F G hA hBz hCz hDz hEne hFne hGne
      · -- D lives
        have hDne : D ≠ 0 := hDz
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_D A B C D E F G hA hBz hCz hDne hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_DG A B C D E F G hA hBz hCz hDne hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_DF A B C D E F G hA hBz hCz hDne hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_DFG A B C D E F G hA hBz hCz hDne hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_DE A B C D E F G hA hBz hCz hDne hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_DEG A B C D E F G hA hBz hCz hDne hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_DEF A B C D E F G hA hBz hCz hDne hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_DEFG A B C D E F G hA hBz hCz hDne hEne hFne hGne
    · -- C lives
      have hCne : C ≠ 0 := hCz
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_C A B C D E F G hA hBz hCne hDz hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CG A B C D E F G hA hBz hCne hDz hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CF A B C D E F G hA hBz hCne hDz hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CFG A B C D E F G hA hBz hCne hDz hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CE A B C D E F G hA hBz hCne hDz hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CEG A B C D E F G hA hBz hCne hDz hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CEF A B C D E F G hA hBz hCne hDz hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CEFG A B C D E F G hA hBz hCne hDz hEne hFne hGne
      · -- D lives
        have hDne : D ≠ 0 := hDz
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CD A B C D E F G hA hBz hCne hDne hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CDG A B C D E F G hA hBz hCne hDne hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CDF A B C D E F G hA hBz hCne hDne hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CDFG A B C D E F G hA hBz hCne hDne hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CDE A B C D E F G hA hBz hCne hDne hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CDEG A B C D E F G hA hBz hCne hDne hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CDEF A B C D E F G hA hBz hCne hDne hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CDEFG A B C D E F G hA hBz hCne hDne hEne hFne hGne
  · -- B lives
    have hBne : B ≠ 0 := hBz
    by_cases hCz : C = 0
    · -- C vanishes
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_B A B C D E F G hA hBne hCz hDz hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BG A B C D E F G hA hBne hCz hDz hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BF A B C D E F G hA hBne hCz hDz hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BFG A B C D E F G hA hBne hCz hDz hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BE A B C D E F G hA hBne hCz hDz hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BEG A B C D E F G hA hBne hCz hDz hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BEF A B C D E F G hA hBne hCz hDz hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BEFG A B C D E F G hA hBne hCz hDz hEne hFne hGne
      · -- D lives
        have hDne : D ≠ 0 := hDz
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BD A B C D E F G hA hBne hCz hDne hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BDG A B C D E F G hA hBne hCz hDne hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BDF A B C D E F G hA hBne hCz hDne hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BDFG A B C D E F G hA hBne hCz hDne hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BDE A B C D E F G hA hBne hCz hDne hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BDEG A B C D E F G hA hBne hCz hDne hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BDEF A B C D E F G hA hBne hCz hDne hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BDEFG A B C D E F G hA hBne hCz hDne hEne hFne hGne
    · -- C lives
      have hCne : C ≠ 0 := hCz
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BC A B C D E F G hA hBne hCne hDz hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCG A B C D E F G hA hBne hCne hDz hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCF A B C D E F G hA hBne hCne hDz hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCFG A B C D E F G hA hBne hCne hDz hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCE A B C D E F G hA hBne hCne hDz hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCEG A B C D E F G hA hBne hCne hDz hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCEF A B C D E F G hA hBne hCne hDz hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCEFG A B C D E F G hA hBne hCne hDz hEne hFne hGne
      · -- D lives
        have hDne : D ≠ 0 := hDz
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCD A B C D E F G hA hBne hCne hDne hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCDG A B C D E F G hA hBne hCne hDne hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCDF A B C D E F G hA hBne hCne hDne hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCDFG A B C D E F G hA hBne hCne hDne hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCDE A B C D E F G hA hBne hCne hDne hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCDEG A B C D E F G hA hBne hCne hDne hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCDEF A B C D E F G hA hBne hCne hDne hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCDEFG A B C D E F G hA hBne hCne hDne hEne hFne hGne


end QuarticChamberExhaust810


end Max11DegreeRoutes
