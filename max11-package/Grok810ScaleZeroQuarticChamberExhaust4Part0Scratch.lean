import Grok810ScaleZeroQuarticChamberExhaust3Scratch
import Batteries.Tactic.OpenPrivate
import Grok810ScaleZeroQuarticChamberExhaust4Part2Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part3Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part4Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part5Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part6Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part7Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part8Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part9Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part10Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part11Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part12Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part13Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part14Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part15Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part16Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part17Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part18Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part19Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part20Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part21Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part22Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part23Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part24Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part25Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part26Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part27Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part28Scratch

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

open private chamberExhaustBCDEFGPath000 from Grok810ScaleZeroQuarticChamberExhaust4Part2Scratch in
open private chamberExhaustBCDEFGPath001 from Grok810ScaleZeroQuarticChamberExhaust4Part3Scratch in
open private chamberExhaustBCDEFGPath002 from Grok810ScaleZeroQuarticChamberExhaust4Part4Scratch in
open private chamberExhaustBCDEFGPath010 from Grok810ScaleZeroQuarticChamberExhaust4Part5Scratch in
open private chamberExhaustBCDEFGPath011 from Grok810ScaleZeroQuarticChamberExhaust4Part6Scratch in
open private chamberExhaustBCDEFGPath012 from Grok810ScaleZeroQuarticChamberExhaust4Part7Scratch in
open private chamberExhaustBCDEFGPath020 from Grok810ScaleZeroQuarticChamberExhaust4Part8Scratch in
open private chamberExhaustBCDEFGPath021 from Grok810ScaleZeroQuarticChamberExhaust4Part9Scratch in
open private chamberExhaustBCDEFGPath022 from Grok810ScaleZeroQuarticChamberExhaust4Part10Scratch in
open private chamberExhaustBCDEFGPath100 from Grok810ScaleZeroQuarticChamberExhaust4Part11Scratch in
open private chamberExhaustBCDEFGPath101 from Grok810ScaleZeroQuarticChamberExhaust4Part12Scratch in
open private chamberExhaustBCDEFGPath102 from Grok810ScaleZeroQuarticChamberExhaust4Part13Scratch in
open private chamberExhaustBCDEFGPath110 from Grok810ScaleZeroQuarticChamberExhaust4Part14Scratch in
open private chamberExhaustBCDEFGPath111 from Grok810ScaleZeroQuarticChamberExhaust4Part15Scratch in
open private chamberExhaustBCDEFGPath112 from Grok810ScaleZeroQuarticChamberExhaust4Part16Scratch in
open private chamberExhaustBCDEFGPath120 from Grok810ScaleZeroQuarticChamberExhaust4Part17Scratch in
open private chamberExhaustBCDEFGPath121 from Grok810ScaleZeroQuarticChamberExhaust4Part18Scratch in
open private chamberExhaustBCDEFGPath122 from Grok810ScaleZeroQuarticChamberExhaust4Part19Scratch in
open private chamberExhaustBCDEFGPath200 from Grok810ScaleZeroQuarticChamberExhaust4Part20Scratch in
open private chamberExhaustBCDEFGPath201 from Grok810ScaleZeroQuarticChamberExhaust4Part21Scratch in
open private chamberExhaustBCDEFGPath202 from Grok810ScaleZeroQuarticChamberExhaust4Part22Scratch in
open private chamberExhaustBCDEFGPath210 from Grok810ScaleZeroQuarticChamberExhaust4Part23Scratch in
open private chamberExhaustBCDEFGPath211 from Grok810ScaleZeroQuarticChamberExhaust4Part24Scratch in
open private chamberExhaustBCDEFGPath212 from Grok810ScaleZeroQuarticChamberExhaust4Part25Scratch in
open private chamberExhaustBCDEFGPath220 from Grok810ScaleZeroQuarticChamberExhaust4Part26Scratch in
open private chamberExhaustBCDEFGPath221 from Grok810ScaleZeroQuarticChamberExhaust4Part27Scratch in
open private chamberExhaustBCDEFGPath222 from Grok810ScaleZeroQuarticChamberExhaust4Part28Scratch in
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
