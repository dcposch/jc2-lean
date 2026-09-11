import Batteries.Tactic.OpenPrivate
import Grok810ScaleZeroQuarticChamberExhaust4Part105Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part104Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part103Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part102Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part101Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart102Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part5Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part4Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part3Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part2Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part1Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part0Scratch
import Grok810ScaleZeroQuarticChamberExhaust1Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part101Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part102Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part103Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part104Scratch

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

open private chamberExhaustBCDEFGPath000 from Grok810ScaleZeroQuarticChamberExhaust4Part101Scratch in
open private chamberExhaustBCDEFGPath001 from Grok810ScaleZeroQuarticChamberExhaust4Part101Scratch in
open private chamberExhaustBCDEFGPath002 from Grok810ScaleZeroQuarticChamberExhaust4Part101Scratch in
open private chamberExhaustBCDEFGPath010 from Grok810ScaleZeroQuarticChamberExhaust4Part101Scratch in
open private chamberExhaustBCDEFGPath011 from Grok810ScaleZeroQuarticChamberExhaust4Part101Scratch in
open private chamberExhaustBCDEFGPath012 from Grok810ScaleZeroQuarticChamberExhaust4Part101Scratch in
open private chamberExhaustBCDEFGPath020 from Grok810ScaleZeroQuarticChamberExhaust4Part102Scratch in
open private chamberExhaustBCDEFGPath021 from Grok810ScaleZeroQuarticChamberExhaust4Part102Scratch in
open private chamberExhaustBCDEFGPath022 from Grok810ScaleZeroQuarticChamberExhaust4Part102Scratch in
open private chamberExhaustBCDEFGPath100 from Grok810ScaleZeroQuarticChamberExhaust4Part102Scratch in
open private chamberExhaustBCDEFGPath101 from Grok810ScaleZeroQuarticChamberExhaust4Part102Scratch in
open private chamberExhaustBCDEFGPath102 from Grok810ScaleZeroQuarticChamberExhaust4Part102Scratch in
open private chamberExhaustBCDEFGPath110 from Grok810ScaleZeroQuarticChamberExhaust4Part103Scratch in
open private chamberExhaustBCDEFGPath111 from Grok810ScaleZeroQuarticChamberExhaust4Part103Scratch in
open private chamberExhaustBCDEFGPath112 from Grok810ScaleZeroQuarticChamberExhaust4Part103Scratch in
open private chamberExhaustBCDEFGPath120 from Grok810ScaleZeroQuarticChamberExhaust4Part103Scratch in
open private chamberExhaustBCDEFGPath121 from Grok810ScaleZeroQuarticChamberExhaust4Part103Scratch in
open private chamberExhaustBCDEFGPath122 from Grok810ScaleZeroQuarticChamberExhaust4Part104Scratch in
open private chamberExhaustBCDEFGPath200 from Grok810ScaleZeroQuarticChamberExhaust4Part104Scratch in
open private chamberExhaustBCDEFGPath201 from Grok810ScaleZeroQuarticChamberExhaust4Part104Scratch in
open private chamberExhaustBCDEFGPath202 from Grok810ScaleZeroQuarticChamberExhaust4Part104Scratch in
open private chamberExhaustBCDEFGPath210 from Grok810ScaleZeroQuarticChamberExhaust4Part104Scratch in
open private chamberExhaustBCDEFGPath211 from Grok810ScaleZeroQuarticChamberExhaust4Part104Scratch in
open private chamberExhaustBCDEFGPath212 from Grok810ScaleZeroQuarticChamberExhaust4Part105Scratch in
open private chamberExhaustBCDEFGPath220 from Grok810ScaleZeroQuarticChamberExhaust4Part105Scratch in
open private chamberExhaustBCDEFGPath221 from Grok810ScaleZeroQuarticChamberExhaust4Part105Scratch in
open private chamberExhaustBCDEFGPath222 from Grok810ScaleZeroQuarticChamberExhaust4Part105Scratch in
set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDEFG`. -/
theorem quarticChamberSupport810_of_live_BCDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath000 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0a ht1a ht2a
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath001 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0a ht1a ht2b
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath002 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0a ht1a ht2c
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath010 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0a ht1b ht2a
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath011 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0a ht1b ht2b
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath012 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0a ht1b ht2c
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath020 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0a ht1c ht2a
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath021 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0a ht1c ht2b
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath022 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0a ht1c ht2c
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath100 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0b ht1a ht2a
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath101 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0b ht1a ht2b
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath102 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0b ht1a ht2c
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath110 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0b ht1b ht2a
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath111 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0b ht1b ht2b
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath112 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0b ht1b ht2c
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath120 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0b ht1c ht2a
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath121 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0b ht1c ht2b
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath122 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0b ht1c ht2c
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath200 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0c ht1a ht2a
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath201 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0c ht1a ht2b
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath202 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0c ht1a ht2c
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath210 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0c ht1b ht2a
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath211 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0c ht1b ht2b
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath212 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0c ht1b ht2c
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath220 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0c ht1c ht2a
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath221 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0c ht1c ht2b
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        exact chamberExhaustBCDEFGPath222 A B C D E F G hA hBne hCne hDne hEne hFne hGne ht0c ht1c ht2c

end QuarticChamberExhaust810

end Max11DegreeRoutes
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
