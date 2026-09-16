import Grok810ScaleZeroQuarticChamberFacesPart101Scratch
import Grok810ScaleZeroQuarticPowerCertificatesScratch
import Grok810ScaleZeroQuarticChamberDefs1Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch

/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_000
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_001
    {a b c e g : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : c + g < 2 * e)
    : b + g < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_002
    {a b d e : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : a + 2 * d < 2 * e)
    : d + e < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_003
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : b + c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_004
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_005
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_006
    {a b c e : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : 4 * e = 3 * a + 6 * b)
    : b + 2 * c = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_007
    {a b e : ℕ}
    (h0 : 2 * b < e)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_008
    {a b c d e : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : a + b + c + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_009
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_010
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_011
    {a b c e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : c + g < 2 * e)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_012
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : b + d + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_013
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_014
    {a b c e g : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : c + g < 2 * e)
    : e + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_015
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_016
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    (h4 : c + g < 2 * e)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_017
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_018
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_019
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_020
    {a b c e : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : 4 * e = 3 * a + 6 * b)
    : 2 * c + e = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_021
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ d + g)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_022
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ e + f)
    (h4 : f = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_023
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * d < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_024
    {a b e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 6 * a ≤ 2 * b + f)
    (h3 : f = 0)
    (h4 : g < a + e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_025
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ b + c + e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_026
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 6 * a ≤ b + 2 * d)
    (h3 : a + 2 * d < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_027
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ 2 * c + d)
    (h4 : a + 2 * d < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_028
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ 3 * b + c)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_029
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_030
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ d + g)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_031
    {a b e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : f = 0)
    (h4 : g < a + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_032
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_033
    {a b e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + f)
    (h3 : f = 0)
    (h4 : g < a + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_034
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ b + c + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_035
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : a + 2 * d < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_036
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 2 * c + d)
    (h4 : a + 2 * d < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_037
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 3 * b + c)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_038
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a < a + 3 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_039
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ d + g)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_040
    {a b e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ e + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    (h4 : g < a + e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_041
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_042
    {a b e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    (h4 : g < a + e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_043
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ b + c + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_044
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_045
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_046
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ 3 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_047
    {a b e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ b + e)
    (h2 : 4 * e = 3 * a + 6 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_048
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_049
    {a b e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : 4 * e = 3 * a + 6 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_050
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a < a + 3 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_051
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ d + g)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_052
    {a b c e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ e + f)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    (h5 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_053
    {a b d e : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_054
    {a b c e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 2 * b + f)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    (h5 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_055
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ b + c + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_056
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_057
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 2 * c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_058
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 3 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_059
    {a b e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ b + e)
    (h2 : 4 * e = 3 * a + 6 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_060
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_061
    {a b e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a ≤ b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_062
    {a b e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    (h4 : g < a + e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_063
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_064
    {a b c e : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_065
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_066
    {a b e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_067
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a ≤ 2 * b + d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_068
    {a b e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_069
    {a b c e : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_070
    {a b d e : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_071
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_072
    {a b c e : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_073
    {a b e : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_074
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_075
    {a b e : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_076
    {a b e f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    (h4 : g < a + e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_077
    {a b c e : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_078
    {a b d e : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_079
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 4 * b)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_080
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 7 * a ≤ 4 * c)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_081
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 9 * a ≤ 4 * d)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_082
    {a b c d e : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_083
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : f = 0)
    : ¬ (13 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_084
    {a b c d e g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_085
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_086
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 4 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_087
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 4 * c)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_088
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 7 * a ≤ 4 * d)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_089
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 9 * a ≤ 4 * e)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_090
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : f = 0)
    : ¬ (11 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_091
    {a b c d e g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_092
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_093
    {a b d e : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a ≤ 4 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_094
    {a b c d e : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : 3 * a ≤ 4 * c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_095
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ 4 * d)
    (h3 : a + 2 * d < 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_096
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 7 * a ≤ 4 * e)
    (h3 : a + 2 * d < 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_097
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : f = 0)
    : ¬ (9 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_098
    {a b c d e g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_099
    {a b c d e : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_100
    {a b c e f : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    : c + f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_101
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_102
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + b + f < 2 * e)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_103
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_104
    {a b d e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + b + f < 2 * e)
    : a + d + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_105
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_106
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_107
    {a b c d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    (h4 : a + b + f < 2 * e)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_108
    {a b c d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    (h4 : a + b + f < 2 * e)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_109
    {a b c d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    (h4 : a + b + f < 2 * e)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_110
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_111
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + b + f < 2 * e)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_112
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : a + 4 * b + 2 * d < 4 * e)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_113
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 6 * a ≤ e + f)
    (h3 : a + b + f < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_114
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 6 * a ≤ 2 * b + f)
    (h3 : a + b + f < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_115
    {a b c d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : a + b + f < 2 * e)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_116
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : a + 4 * b + 2 * d < 4 * e)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_117
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : a + b + f < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_118
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + f)
    (h3 : a + b + f < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_119
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a < a + 3 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_120
    {a b d e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ d + g)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 4 * b + 2 * d < 4 * e)
    (h4 : a + b + f < 2 * e)
    (h5 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_121
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ e + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_122
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_123
    {a b d e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ d + g)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 4 * b + 2 * d < 4 * e)
    (h4 : a + b + f < 2 * e)
    (h5 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_124
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ e + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_125
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_126
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_127
    {a b d e g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    (h4 : g = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_128
    {a b e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_129
    {a b e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_130
    {a b e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_131
    {a b c d e f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : a + b + f < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_132
    {a b e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    (h3 : g = 0)
    : ¬ (15 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_133
    {a b c d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : a + b + f < 2 * e)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_134
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 4 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_135
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 4 * c)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_136
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 7 * a ≤ 4 * d)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_137
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 9 * a ≤ 4 * e)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_138
    {a b c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : a + b + f < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_139
    {a b e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    (h3 : g = 0)
    : ¬ (13 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_140
    {a b c d e f : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_141
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 9 * a ≤ 4 * f)
    (h3 : a + 2 * d < 2 * e)
    (h4 : a + b + f < 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_142
    {a b e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    (h3 : g = 0)
    : ¬ (11 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_143
    {a b c d e f : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_144
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    : b + c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_145
    {a b e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_146
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    : 2 * b + c < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_147
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    : a + b + c < (a + 2 * b + e) ∧ 3 * b < (a + 2 * b + e) ∧ b + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_148
    {a b c e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : c + g < 2 * e)
    : a + 2 * b < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_149
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    : b + c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_150
    {a b e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_151
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ d + g)
    (h4 : d = 0)
    (h5 : g < a + e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_152
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_153
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ b + 2 * d)
    (h4 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_154
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : 6 * a ≤ 2 * c + d)
    (h5 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_155
    {a b c e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : c + g < 2 * e)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_156
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ d + g)
    (h4 : d = 0)
    (h5 : g < a + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_157
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    (h4 : g < a + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_158
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : d = 0)
    (h4 : g < a + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_159
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 2 * c + d)
    (h4 : d = 0)
    (h5 : g < a + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_160
    {a b c e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a < a + 3 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_161
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 4 * a ≤ d + g)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : d = 0)
    (h5 : g < a + e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_162
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    (h5 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_163
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    (h4 : g < a + e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_164
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    (h5 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_165
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * a ≤ c + d)
    (h4 : 4 * e = 3 * a + 6 * b)
    (h5 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_166
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ d + g)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    (h5 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_167
    {a b d e : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_168
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    (h4 : g < a + e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_169
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 2 * c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_170
    {a b c d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : d = 0)
    (h5 : g < a + e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_171
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    (h5 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_172
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a ≤ 2 * b + d)
    (h3 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_173
    {a b d e : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_174
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_175
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_176
    {a b e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_177
    {a b d e : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_178
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 4 * b)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_179
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 7 * a ≤ 4 * c)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_180
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : d = 0)
    : ¬ (9 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_181
    {a b c e : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_182
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : f = 0)
    : ¬ (13 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_183
    {a b c e g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_184
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a + b + c < a + 2 * b + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ b + c + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_185
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 4 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_186
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 4 * c)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_187
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : d = 0)
    : ¬ (7 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_188
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 9 * a ≤ 4 * e)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_189
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : f = 0)
    : ¬ (11 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_190
    {a b c e g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_191
    {a b c e : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_192
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_193
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : a + b + c < (a + 2 * b + e) ∧ 3 * b < (a + 2 * b + e) ∧ a + f < (a + 2 * b + e) ∧ b + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_194
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : a + 2 * b < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_195
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_196
    {a b d e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    (h5 : g < 4 * a)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_197
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : a + b + f < 2 * e)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_198
    {a b d e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * f < a + 2 * e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ d + g)
    (h4 : d = 0)
    (h5 : g < 4 * a)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_199
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_200
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_201
    {a b c d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 2 * c + d)
    (h4 : a + b + f < 2 * e)
    (h5 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_202
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a < a + 3 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_203
    {a b d e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ d + g)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    (h5 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_204
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_205
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_206
    {a b c d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    (h5 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_207
    {a b d e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ d + g)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    (h5 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_208
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_209
    {a b c d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    (h5 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_210
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    (h5 : g = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_211
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_212
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    (h5 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_213
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_214
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    (h3 : d = 0)
    : ¬ (9 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_215
    {a b c e f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_216
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a + b + c < a + 2 * b + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_217
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    (h3 : d = 0)
    : ¬ (7 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_218
    {a b c e f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_219
    {a b c e f : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_220
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_221
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ 2 * b + f)
    (h4 : f = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_222
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : a + 2 * d < 2 * e)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_223
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ e + f)
    (h4 : f = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_224
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 2 * b + f)
    (h4 : f = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_225
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ d + g)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 4 * b + 2 * d < 4 * e)
    (h4 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_226
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ e + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 4 * b + 2 * d < 4 * e)
    (h4 : f = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_227
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 4 * b + 2 * d < 4 * e)
    (h4 : f = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_228
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ d + g)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 4 * b + 2 * d < 4 * e)
    (h4 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_229
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ e + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    (h4 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_230
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    (h4 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_231
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 4 * b + 2 * d < 4 * e)
    (h4 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_232
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 4 * b + 2 * d < 4 * e)
    (h4 : f = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_233
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : g = 0)
    : ¬ (15 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_234
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_235
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : g = 0)
    : ¬ (13 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_236
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : g = 0)
    : ¬ (11 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_237
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    : a + 2 * b < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_238
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : d = 0)
    (h4 : g < 4 * a)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_239
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_240
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : d = 0)
    (h4 : g < 4 * a)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_241
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_242
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_243
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : 5 * a ≤ 2 * c + d)
    (h5 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_244
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ d + g)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    (h4 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_245
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ e + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_246
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_247
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * a ≤ 2 * b + f)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : f = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_248
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_249
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * a ≤ 2 * c + d)
    (h4 : 4 * e = 3 * a + 6 * b)
    (h5 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_250
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ d + g)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    (h4 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_251
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ e + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_252
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_253
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_254
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_255
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_256
    {a b d e g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    (h4 : g = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_257
    {a b e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : g = 0)
    : ¬ (15 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat102_258
    {a b e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : g = 0)
    : ¬ (13 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace1810_coeff_top_S00
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace1810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace1810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [kappaQuarticPowerInnerS00810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace5810_coeff_top_S00
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (ht1 : 2 * C.natDegree + E.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree) :
    (xiQuarticChamberFace5810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      xiQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace5810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS00810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace12810_coeff_top_S05
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (ht1 : 3 * C.natDegree = A.natDegree + 2 * D.natDegree) :
    (muQuarticChamberFace12810 A B C D E F G).coeff
        (A.natDegree + 2 * D.natDegree) =
      muQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace12810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [muQuarticPowerInnerS05810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace5810_coeff_top_S05
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (ht1 : 4 * C.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree) :
    (piQuarticChamberFace5810 A B C D E F G).coeff
        (A.natDegree + C.natDegree + 2 * D.natDegree) =
      piQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace5810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * C * D ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * C * D ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 4).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 4).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [piQuarticPowerInnerS05810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace8810_coeff_top_S06
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : D.natDegree + E.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace8810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace8810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    all_goals omega
  have hc2 : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [kappaQuarticPowerInnerS06810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace13810_coeff_top_S06
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (ht1 : A.natDegree + 2 * D.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht2 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht3 : 2 * E.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace13810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      muQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace13810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * D ^ 2)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [muQuarticPowerInnerS06810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace13810_coeff_top_S06
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (ht1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree)
    (ht2 : 2 * C.natDegree + E.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree) :
    (xiQuarticChamberFace13810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      xiQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace13810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * C * D)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * C * D)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [xiQuarticPowerInnerS06810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace6810_coeff_top_S06
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht3 : A.natDegree + C.natDegree + 2 * D.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht4 : 4 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht5 : C.natDegree + 2 * E.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace6810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      piQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace6810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * B * D * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne]
    all_goals omega
  have hc2 : ((A * B * D * E)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A * C * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A * C * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd4, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : ((C * E ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc5 : ((C * E ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5]
  all_goals simp only [piQuarticPowerInnerS06810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6810_coeff_top_S07
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : C.natDegree + F.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace6810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace6810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc2 : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [kappaQuarticPowerInnerS07810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace14810_coeff_top_S07
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + B.natDegree + F.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht2 : A.natDegree + 2 * D.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht3 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace14810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      muQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace14810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [muQuarticPowerInnerS07810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace14810_coeff_top_S07
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + D.natDegree + F.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree) :
    (xiQuarticChamberFace14810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + C.natDegree + D.natDegree) =
      xiQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace14810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * C * D)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc0 : ((A * B * C * D)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * D * F)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc1 : ((A * D * F)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS07810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace7810_coeff_top_S07
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht3 : A.natDegree + C.natDegree + 2 * D.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht4 : 4 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht5 : A.natDegree + 2 * F.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace7810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      piQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace7810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * B * C * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc2 : ((A * B * C * F)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A * C * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A * C * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd4, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc5 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5]
  all_goals simp only [piQuarticPowerInnerS07810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace9810_coeff_top_S08
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : B.natDegree + G.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace9810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS08810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace9810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc2 : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [kappaQuarticPowerInnerS08810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace10810_coeff_top_S08
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht2 : C.natDegree + G.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace10810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      muQuarticPowerInnerS08810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace10810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * G)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc2 : ((C * G)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [muQuarticPowerInnerS08810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace8810_coeff_top_S08
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + 2 * B.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht3 : 4 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht4 : 2 * C.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht5 : 2 * G.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace8810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      piQuarticPowerInnerS08810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace8810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((C ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : ((C ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc5 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5]
  all_goals simp only [piQuarticPowerInnerS08810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6810_coeff_top_S10
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : C.natDegree + F.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace6810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace6810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc2 : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [kappaQuarticPowerInnerS10810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace15810_coeff_top_S10
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + B.natDegree + F.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht2 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht3 : 2 * E.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace15810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      muQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace15810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [muQuarticPowerInnerS10810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace5810_coeff_top_S10
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (ht1 : 2 * C.natDegree + E.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree) :
    (xiQuarticChamberFace5810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      xiQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace5810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS10810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace9810_coeff_top_S11
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : B.natDegree + G.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace9810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS11810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace9810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc2 : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [kappaQuarticPowerInnerS11810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace16810_coeff_top_S11
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree + E.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree)
    (ht2 : E.natDegree + G.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree) :
    (xiQuarticChamberFace16810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      xiQuarticPowerInnerS11810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace16810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((E * G)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc2 : ((E * G)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [xiQuarticPowerInnerS11810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace12810_coeff_top_S13
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (ht1 : D.natDegree + E.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace12810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS13810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace12810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    all_goals omega
  have hc1 : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [kappaQuarticPowerInnerS13810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace17810_coeff_top_S13
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + 2 * D.natDegree = A.natDegree + B.natDegree + F.natDegree)
    (ht2 : 2 * E.natDegree = A.natDegree + B.natDegree + F.natDegree) :
    (muQuarticChamberFace17810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + F.natDegree) =
      muQuarticPowerInnerS13810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace17810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * F)).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    all_goals omega
  have hc0 : ((A * B * F)).coeff (A.natDegree + B.natDegree + F.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * D ^ 2)).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * D ^ 2)).coeff (A.natDegree + B.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (E ^ 2).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (E ^ 2).coeff (A.natDegree + B.natDegree + F.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [muQuarticPowerInnerS13810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace18810_coeff_top_S13
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + D.natDegree + F.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree) :
    (xiQuarticChamberFace18810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      xiQuarticPowerInnerS13810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace18810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * D * F)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc1 : ((A * D * F)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS13810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace10810_coeff_top_S13
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + B.natDegree + D.natDegree + E.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + 2 * F.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace10810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      piQuarticPowerInnerS13810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace10810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * D * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * D * E)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [piQuarticPowerInnerS13810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace13810_coeff_top_S14
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : D.natDegree + E.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace13810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace13810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc1 : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    all_goals omega
  have hc2 : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [kappaQuarticPowerInnerS14810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace19810_coeff_top_S14
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : E.natDegree + G.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree) :
    (xiQuarticChamberFace19810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      xiQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace19810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((E * G)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc1 : ((E * G)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS14810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace11810_coeff_top_S14
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht3 : 2 * G.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace11810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      piQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace11810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * B * D * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne]
    all_goals omega
  have hc2 : ((A * B * D * E)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [piQuarticPowerInnerS14810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace14810_coeff_top_S15
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : D.natDegree + E.natDegree = C.natDegree + F.natDegree) :
    (kappaQuarticChamberFace14810 A B C D E F G).coeff
        (C.natDegree + F.natDegree) =
      kappaQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace14810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((C * F)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc0 : ((C * F)).coeff (C.natDegree + F.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((D * E)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hDne hEne]
    all_goals omega
  have hc1 : ((D * E)).coeff (C.natDegree + F.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [kappaQuarticPowerInnerS15810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace18810_coeff_top_S15
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (ht1 : 3 * C.natDegree = A.natDegree + 2 * D.natDegree)
    (ht2 : 2 * E.natDegree = A.natDegree + 2 * D.natDegree) :
    (muQuarticChamberFace18810 A B C D E F G).coeff
        (A.natDegree + 2 * D.natDegree) =
      muQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace18810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (E ^ 2).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (E ^ 2).coeff (A.natDegree + 2 * D.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [muQuarticPowerInnerS15810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace20810_coeff_top_S15
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : 2 * C.natDegree + E.natDegree = A.natDegree + D.natDegree + F.natDegree) :
    (xiQuarticChamberFace20810 A B C D E F G).coeff
        (A.natDegree + D.natDegree + F.natDegree) =
      xiQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace20810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D * F)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc0 : ((A * D * F)).coeff (A.natDegree + D.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * E)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * E)).coeff (A.natDegree + D.natDegree + F.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS15810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace12810_coeff_top_S15
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : 4 * C.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree)
    (ht2 : A.natDegree + 2 * F.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree)
    (ht3 : C.natDegree + 2 * E.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree) :
    (piQuarticChamberFace12810 A B C D E F G).coeff
        (A.natDegree + C.natDegree + 2 * D.natDegree) =
      piQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace12810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * C * D ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * C * D ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 4).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 4).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * F ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A * F ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((C * E ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((C * E ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [piQuarticPowerInnerS15810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace16810_coeff_top_S16
    {A B C D E F G : k[X]}
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : C.natDegree + F.natDegree = B.natDegree + G.natDegree) :
    (kappaQuarticChamberFace16810 A B C D E F G).coeff
        (B.natDegree + G.natDegree) =
      kappaQuarticPowerInnerS16810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace16810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((B * G)).natDegree = B.natDegree + G.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc0 : ((B * G)).coeff (B.natDegree + G.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C * F)).natDegree = B.natDegree + G.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc1 : ((C * F)).coeff (B.natDegree + G.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [kappaQuarticPowerInnerS16810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace20810_coeff_top_S16
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : C.natDegree + G.natDegree = A.natDegree + B.natDegree + F.natDegree) :
    (muQuarticChamberFace20810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + F.natDegree) =
      muQuarticPowerInnerS16810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace20810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * F)).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    all_goals omega
  have hc0 : ((A * B * F)).coeff (A.natDegree + B.natDegree + F.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C * G)).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc1 : ((C * G)).coeff (A.natDegree + B.natDegree + F.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [muQuarticPowerInnerS16810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace14810_coeff_top_S16
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * G.natDegree = A.natDegree + 2 * F.natDegree) :
    (piQuarticChamberFace14810 A B C D E F G).coeff
        (A.natDegree + 2 * F.natDegree) =
      piQuarticPowerInnerS16810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace14810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * F ^ 2)).natDegree = A.natDegree + 2 * F.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * F ^ 2)).coeff (A.natDegree + 2 * F.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (G ^ 2).natDegree = A.natDegree + 2 * F.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (G ^ 2).coeff (A.natDegree + 2 * F.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [piQuarticPowerInnerS16810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace7810_coeff_top_S18
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace7810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS18810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace7810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc1 : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [kappaQuarticPowerInnerS18810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace19810_coeff_top_S18
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : E.natDegree + G.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree) :
    (xiQuarticChamberFace19810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      xiQuarticPowerInnerS18810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace19810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((E * G)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc1 : ((E * G)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS18810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace17810_coeff_top_S20
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + 2 * D.natDegree = A.natDegree + B.natDegree + F.natDegree)
    (ht2 : 2 * E.natDegree = A.natDegree + B.natDegree + F.natDegree) :
    (muQuarticChamberFace17810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + F.natDegree) =
      muQuarticPowerInnerS20810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace17810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * F)).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    all_goals omega
  have hc0 : ((A * B * F)).coeff (A.natDegree + B.natDegree + F.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * D ^ 2)).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * D ^ 2)).coeff (A.natDegree + B.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (E ^ 2).natDegree = A.natDegree + B.natDegree + F.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (E ^ 2).coeff (A.natDegree + B.natDegree + F.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [muQuarticPowerInnerS20810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace22810_coeff_top_S20
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : E.natDegree + G.natDegree = A.natDegree + D.natDegree + F.natDegree) :
    (xiQuarticChamberFace22810 A B C D E F G).coeff
        (A.natDegree + D.natDegree + F.natDegree) =
      xiQuarticPowerInnerS20810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace22810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D * F)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc0 : ((A * D * F)).coeff (A.natDegree + D.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((E * G)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc1 : ((E * G)).coeff (A.natDegree + D.natDegree + F.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS20810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace14810_coeff_top_S20
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * G.natDegree = A.natDegree + 2 * F.natDegree) :
    (piQuarticChamberFace14810 A B C D E F G).coeff
        (A.natDegree + 2 * F.natDegree) =
      piQuarticPowerInnerS20810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace14810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * F ^ 2)).natDegree = A.natDegree + 2 * F.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * F ^ 2)).coeff (A.natDegree + 2 * F.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (G ^ 2).natDegree = A.natDegree + 2 * F.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (G ^ 2).coeff (A.natDegree + 2 * F.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [piQuarticPowerInnerS20810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace21810_coeff_top_S22
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree)
    (ht2 : 2 * E.natDegree = A.natDegree + 2 * D.natDegree) :
    (muQuarticChamberFace21810 A B C D E F G).coeff
        (A.natDegree + 2 * D.natDegree) =
      muQuarticPowerInnerS22810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace21810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C * G)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc1 : ((C * G)).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (E ^ 2).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (E ^ 2).coeff (A.natDegree + 2 * D.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [muQuarticPowerInnerS22810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace22810_coeff_top_S22
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : E.natDegree + G.natDegree = A.natDegree + D.natDegree + F.natDegree) :
    (xiQuarticChamberFace22810 A B C D E F G).coeff
        (A.natDegree + D.natDegree + F.natDegree) =
      xiQuarticPowerInnerS22810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace22810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D * F)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc0 : ((A * D * F)).coeff (A.natDegree + D.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((E * G)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc1 : ((E * G)).coeff (A.natDegree + D.natDegree + F.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS22810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace14810_coeff_top_S22
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * G.natDegree = A.natDegree + 2 * F.natDegree) :
    (piQuarticChamberFace14810 A B C D E F G).coeff
        (A.natDegree + 2 * F.natDegree) =
      piQuarticPowerInnerS22810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace14810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * F ^ 2)).natDegree = A.natDegree + 2 * F.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * F ^ 2)).coeff (A.natDegree + 2 * F.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (G ^ 2).natDegree = A.natDegree + 2 * F.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (G ^ 2).coeff (A.natDegree + 2 * F.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [piQuarticPowerInnerS22810]
  all_goals simp only [sub_eq_add_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  all_goals ac_rfl

/-! ## The power-target chamber kills -/


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCE` / `EE·BBB·BBC·BCC·CCC` dies on power system `S00` (carriers κ, ξ). -/
theorem quarticChamberBCE5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCE5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_238 hcq4 hcq0 h hDn hAG)
      · exact Or.inr (by exact astra4wPowerNat102_022 hcq4 hAF hcq0 h hFn)
      · exact Or.inr (by exact astra4wPowerNat102_152 hcq4 hAD hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_221 hcq4 hAF hcq0 h hFn)
      · exact Or.inr (by exact astra4wPowerNat102_025 hcq4 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_153 hcq4 hAD hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_154 hcq4 hAD hcq1 hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_028 hcq4 hcq1 hcq0 h)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_239 hcq4 hcq1 hcq0 h)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_240 hcq4 hcq0 h hDn hAG)
      · exact Or.inr (by exact astra4wPowerNat102_223 hcq4 hAF hcq0 h hFn)
      · exact Or.inr (by exact astra4wPowerNat102_241 hcq4 hAD h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_224 hcq4 hAF hcq0 h hFn)
      · exact Or.inr (by exact astra4wPowerNat102_034 hcq4 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_242 hcq4 hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_243 hcq4 hAD hcq1 hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_037 hcq4 hcq1 hcq0 h)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_202 hcq4 hcq1 h hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_244 hcq4 h hcq0 hDn hGn)
      · exact Or.inr (by exact astra4wPowerNat102_245 hcq4 h hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_246 hcq4 hAD h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_247 hcq4 hAF h hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_043 hcq4 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_248 hcq4 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_249 hcq4 hAD hcq1 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_046 hcq4 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_047 hcq4 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_165 hcq4 hAD hcq1 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_049 hcq4 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_050 hcq4 hcq1 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_250 hcq4 h hcq0 hDn hGn)
      · exact Or.inr (by exact astra4wPowerNat102_251 hcq4 h hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_167 h hcq4 hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_252 hcq4 h hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_055 hcq4 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_253 hcq4 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_169 hcq4 hcq1 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_058 hcq4 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_059 hcq4 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_254 hcq4 hcq1 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_061 hcq4 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_255 hcq4 h hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_063 hcq4 hcq1 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_064 h hcq4 hcq1 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_256 h hcq4 hcq0 hDn hGn)
    · exact Or.inr (by exact astra4wPowerNat102_066 h hcq4 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_172 hcq4 hcq0 h hDn)
    · exact Or.inr (by exact astra4wPowerNat102_068 h hcq4 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_069 h hcq4 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_173 h hcq4 hcq0 hDn)
    · exact Or.inr (by exact astra4wPowerNat102_174 h hcq4 hcq1 hcq0 hDn)
    · exact Or.inr (by exact astra4wPowerNat102_072 h hcq4 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_073 h hcq4 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_175 h hcq4 hcq1 hcq0 hDn)
    · exact Or.inr (by exact astra4wPowerNat102_075 h hcq4 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_176 h hcq4 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_077 h hcq4 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_177 h hcq4 hcq0 hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hFz hGz hz0l hz0beta (Or.inr (by exact astra4wPowerNat102_144 hcq4 hcq1 hcq0)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat102_145 hcq4 hcq0)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top_S00 hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by exact astra4wPowerNat102_006 hcq1 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_178 hcq4 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_179 hcq4 hcq1 hcq0 h)
      · exact absurd h (by exact astra4wPowerNat102_180 hcq4 hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_181 h hcq4 hcq1 hcq0)
      · exact absurd h (by exact astra4wPowerNat102_182 hcq4 hcq0 hFn)
      · exact absurd h (by exact astra4wPowerNat102_257 hcq4 hcq0 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_184 hcq4 hcq1 h hcq0)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_185 hcq4 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_186 hcq4 hcq1 hcq0 h)
      · exact absurd h (by exact astra4wPowerNat102_187 hcq4 hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_188 hcq4 hcq1 hcq0 h)
      · exact absurd h (by exact astra4wPowerNat102_189 hcq4 hcq0 hFn)
      · exact absurd h (by exact astra4wPowerNat102_258 hcq4 hcq0 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_191 h hcq4 hcq1 hcq0)
  have hr1 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hFz hGz (by exact astra4wPowerNat102_007 hcq4) (by exact astra4wPowerNat102_010 hcq4 hcq1 hcq0) hz1l hz1beta (Or.inr (by exact astra4wPowerNat102_146 hcq4 hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat102_147 hcq4 hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat102_237 hcq4 hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat102_149 hcq4 hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat102_150 hcq4 hcq0))
  have hct1 := xiQuarticChamberFace5810_coeff_top_S00 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat102_020 hcq1 hcq0)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS00810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDE` / `EE·BBB·BBC·BCC·CCC` dies on power system `S00` (carriers κ, ξ). -/
theorem quarticChamberBCDE13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_112 hcq7 hcq0 h hcq6 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat102_022 hcq7 hAF hcq0 h hFn)
      · exact Or.inr (by exact astra4wPowerNat102_023 hcq7 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_221 hcq7 hAF hcq0 h hFn)
      · exact Or.inr (by exact astra4wPowerNat102_025 hcq7 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_026 hcq7 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_027 hcq7 hcq1 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_028 hcq7 hcq1 hcq0 h)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_222 hcq7 hcq1 hcq0 h hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_116 hcq7 hcq0 h hcq6 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat102_223 hcq7 hAF hcq0 h hFn)
      · exact Or.inr (by exact astra4wPowerNat102_032 hcq7 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_224 hcq7 hAF hcq0 h hFn)
      · exact Or.inr (by exact astra4wPowerNat102_034 hcq7 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_035 hcq7 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_036 hcq7 hcq1 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_037 hcq7 hcq1 hcq0 h)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_119 hcq7 hcq1 h hcq0 hcq4)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_225 hcq7 h hcq0 hcq6 hGn)
      · exact Or.inr (by exact astra4wPowerNat102_226 hcq7 h hcq0 hcq6 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_041 hcq7 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_227 hcq7 h hcq0 hcq6 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_043 hcq7 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_044 hcq7 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_045 hcq7 hcq1 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_046 hcq7 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_047 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_048 hcq7 hcq1 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_049 hcq7 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_050 hcq7 hcq1 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_228 hcq7 h hcq0 hcq6 hGn)
      · exact Or.inr (by exact astra4wPowerNat102_229 hcq7 h hcq0 hcq4 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_053 h hcq7 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_230 hcq7 h hcq0 hcq4 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_055 hcq7 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_056 hcq7 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_057 hcq7 hcq1 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_058 hcq7 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_059 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_060 hcq7 hcq1 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_061 hcq7 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_231 hcq7 h hcq0 hcq6 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_063 hcq7 hcq1 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_064 h hcq7 hcq1 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_127 h hcq7 hcq0 hcq4 hGn)
    · exact Or.inr (by exact astra4wPowerNat102_066 h hcq7 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_067 hcq7 hcq0 hcq4 h)
    · exact Or.inr (by exact astra4wPowerNat102_068 h hcq7 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_069 h hcq7 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_070 h hcq7 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat102_071 h hcq7 hcq1 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat102_072 h hcq7 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_073 h hcq7 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_074 h hcq7 hcq1 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat102_075 h hcq7 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_232 h hcq7 hcq0 hcq6 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_077 h hcq7 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_078 h hcq7 hcq0 hcq4)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz hGz (by exact astra4wPowerNat102_000 hcq7 hcq0 hcq4) (by exact astra4wPowerNat102_002 hcq0 hcq4) hz0l hz0beta (Or.inr (by exact astra4wPowerNat102_003 hcq7 hcq1 hcq0 hcq4)) hz0delta (Or.inr (by exact astra4wPowerNat102_004 hcq7 hcq0 hcq4)) hz0zeta (Or.inr (by exact astra4wPowerNat102_005 hcq7 hcq0 hcq4)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top_S00 hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by exact astra4wPowerNat102_006 hcq1 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_079 hcq7 hcq1 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_080 hcq7 hcq1 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_081 hcq7 hcq1 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_082 h hcq7 hcq1 hcq0 hcq4)
      · exact absurd h (by exact astra4wPowerNat102_083 hcq7 hcq0 hcq4 hFn)
      · exact absurd h (by exact astra4wPowerNat102_233 hcq7 hcq0 hcq4 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_234 hcq7 hcq1 h hcq0 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_086 hcq7 hcq1 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_087 hcq7 hcq1 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_088 hcq7 hcq1 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_089 hcq7 hcq1 hcq0 h hcq4)
      · exact absurd h (by exact astra4wPowerNat102_090 hcq7 hcq0 hcq4 hFn)
      · exact absurd h (by exact astra4wPowerNat102_235 hcq7 hcq0 hcq4 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_092 hcq7 hcq1 h hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_093 hcq4 h)
      · exact Or.inr (by exact astra4wPowerNat102_094 hcq1 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_095 hcq7 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_096 hcq7 hcq0 h hcq4)
      · exact absurd h (by exact astra4wPowerNat102_097 hcq7 hcq0 hcq4 hFn)
      · exact absurd h (by exact astra4wPowerNat102_236 hcq7 hcq0 hcq4 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_099 h hcq7 hcq1 hcq0)
  have hr1 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz hGz (by exact astra4wPowerNat102_007 hcq7) (by exact astra4wPowerNat102_008 hcq1 hcq0 hcq4) (by exact astra4wPowerNat102_009 hcq7 hcq0 hcq4) (by exact astra4wPowerNat102_010 hcq7 hcq1 hcq0) (by exact astra4wPowerNat102_012 hcq7 hcq0 hcq4) (by exact astra4wPowerNat102_013 hcq7 hcq1 hcq0 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat102_015 hcq7 hcq1 hcq0 hcq4)) hz1delta (Or.inr (by exact astra4wPowerNat102_220 hcq7 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat102_017 hcq7 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat102_018 hcq7 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat102_019 hcq7 hcq0 hcq4))
  have hct1 := xiQuarticChamberFace5810_coeff_top_S00 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat102_020 hcq1 hcq0)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS00810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEF` / `EE·BBB·BBC·BCC·CCC` dies on power system `S00` (carriers κ, ξ). -/
theorem quarticChamberBCEF23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEF23810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_196 hcq8 hcq0 h hcq4 hDn hAG)
      · exact Or.inr (by exact astra4wPowerNat102_113 hcq8 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_152 hcq8 hAD hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_114 hcq8 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_025 hcq8 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_153 hcq8 hAD hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_154 hcq8 hAD hcq1 hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_028 hcq8 hcq1 hcq0 h)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_197 hcq8 hcq1 hcq0 h hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_198 hcq8 hcq6 hcq0 h hDn hAG)
      · exact Or.inr (by exact astra4wPowerNat102_117 hcq8 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_199 hcq8 h hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_118 hcq8 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_034 hcq8 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_200 hcq8 hcq0 h hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_201 hcq8 hcq1 hcq0 h hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_037 hcq8 hcq1 hcq0 h)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_202 hcq8 hcq1 h hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_203 hcq8 h hcq0 hcq4 hDn hGn)
      · exact Or.inr (by exact astra4wPowerNat102_121 hcq8 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_204 hcq8 h hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_122 hcq8 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_043 hcq8 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_205 hcq8 h hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_206 hcq8 hcq1 h hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_046 hcq8 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_047 hcq8 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_165 hcq8 hAD hcq1 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_049 hcq8 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_050 hcq8 hcq1 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_207 hcq8 h hcq0 hcq4 hDn hGn)
      · exact Or.inr (by exact astra4wPowerNat102_124 hcq8 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_167 h hcq8 hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_125 hcq8 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_055 hcq8 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_208 hcq8 h hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_169 hcq8 hcq1 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_058 hcq8 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_059 hcq8 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_209 hcq8 hcq1 h hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_061 hcq8 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_126 hcq8 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_063 hcq8 hcq1 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_064 h hcq8 hcq1 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_210 h hcq8 hcq0 hcq4 hDn hGn)
    · exact Or.inr (by exact astra4wPowerNat102_128 h hcq8 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat102_172 hcq8 hcq0 h hDn)
    · exact Or.inr (by exact astra4wPowerNat102_129 h hcq8 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat102_069 h hcq8 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_211 h hcq8 hcq0 hcq4 hDn)
    · exact Or.inr (by exact astra4wPowerNat102_174 h hcq8 hcq1 hcq0 hDn)
    · exact Or.inr (by exact astra4wPowerNat102_072 h hcq8 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_073 h hcq8 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_212 h hcq8 hcq1 hcq0 hcq4 hDn)
    · exact Or.inr (by exact astra4wPowerNat102_075 h hcq8 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_130 h hcq8 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat102_077 h hcq8 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_213 h hcq8 hcq0 hcq4 hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hGz (by exact astra4wPowerNat102_100 hcq1 hcq0 hcq4) hz0l hz0beta (Or.inr (by exact astra4wPowerNat102_101 hcq8 hcq1 hcq0 hcq4)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat102_103 hcq8 hcq0 hcq4)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top_S00 hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by exact astra4wPowerNat102_006 hcq1 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_178 hcq8 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_179 hcq8 hcq1 hcq0 h)
      · exact absurd h (by exact astra4wPowerNat102_214 hcq8 hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_181 h hcq8 hcq1 hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_215 h hcq8 hcq1 hcq0 hcq4)
      · exact absurd h (by exact astra4wPowerNat102_132 hcq8 hcq0 hcq4 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_216 hcq8 hcq1 h hcq0 hcq4)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_185 hcq8 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_186 hcq8 hcq1 hcq0 h)
      · exact absurd h (by exact astra4wPowerNat102_217 hcq8 hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_188 hcq8 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_218 h hcq8 hcq1 hcq0 hcq4)
      · exact absurd h (by exact astra4wPowerNat102_139 hcq8 hcq0 hcq4 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_219 h hcq8 hcq1 hcq0 hcq4)
  have hr1 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hGz (by exact astra4wPowerNat102_007 hcq8) (by exact astra4wPowerNat102_010 hcq8 hcq1 hcq0) (by exact astra4wPowerNat102_105 hcq8 hcq1 hcq0 hcq4) (by exact astra4wPowerNat102_106 hcq8 hcq0 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat102_192 hcq8 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat102_193 hcq8 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat102_194 hcq8 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat102_195 hcq8 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat102_110 hcq8 hcq0 hcq4))
  have hct1 := xiQuarticChamberFace5810_coeff_top_S00 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat102_020 hcq1 hcq0)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS00810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEG` / `EE·BBB·BBC·BCC·CCC` dies on power system `S00` (carriers κ, ξ). -/
theorem quarticChamberBCEG23810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEG23810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_151 hcq8 hAD hcq0 h hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_022 hcq8 hAF hcq0 h hFn)
      · exact Or.inr (by exact astra4wPowerNat102_152 hcq8 hAD hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_024 hcq8 hcq0 h hFn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_025 hcq8 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_153 hcq8 hAD hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_154 hcq8 hAD hcq1 hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat102_028 hcq8 hcq1 hcq0 h)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_155 hcq8 hcq1 hcq0 h hcq5)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_156 hcq8 hAD hcq0 h hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_031 hcq8 hcq0 h hFn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_157 hcq8 h hcq0 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_033 hcq8 hcq0 h hFn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_034 hcq8 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_158 hcq8 hcq0 h hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_159 hcq8 hcq1 hcq0 h hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_037 hcq8 hcq1 hcq0 h)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_160 hcq8 hcq1 h hcq0 hcq5)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_161 hcq8 hAD h hcq0 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_040 hcq8 h hcq0 hFn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_162 hcq8 hcq1 h hcq0 hcq5 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_042 hcq8 h hcq0 hFn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_043 hcq8 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_163 hcq8 h hcq0 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_164 hcq8 hcq1 h hcq0 hcq5 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_046 hcq8 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_047 hcq8 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_165 hcq8 hAD hcq1 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_049 hcq8 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_050 hcq8 hcq1 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_166 hcq8 hcq1 h hcq0 hcq5 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_052 hcq8 hcq1 h hcq0 hcq5 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_167 h hcq8 hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_054 hcq8 hcq1 h hcq0 hcq5 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_055 hcq8 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_168 hcq8 h hcq0 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_169 hcq8 hcq1 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_058 hcq8 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_059 hcq8 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_170 hcq8 hcq1 h hcq0 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_061 hcq8 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_062 hcq8 h hcq0 hFn hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_063 hcq8 hcq1 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_064 h hcq8 hcq1 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_171 h hcq8 hcq1 hcq0 hcq5 hDn)
    · exact Or.inr (by exact astra4wPowerNat102_066 h hcq8 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_172 hcq8 hcq0 h hDn)
    · exact Or.inr (by exact astra4wPowerNat102_068 h hcq8 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_069 h hcq8 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_173 h hcq8 hcq0 hDn)
    · exact Or.inr (by exact astra4wPowerNat102_174 h hcq8 hcq1 hcq0 hDn)
    · exact Or.inr (by exact astra4wPowerNat102_072 h hcq8 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_073 h hcq8 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_175 h hcq8 hcq1 hcq0 hDn)
    · exact Or.inr (by exact astra4wPowerNat102_075 h hcq8 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_176 h hcq8 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_077 h hcq8 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_177 h hcq8 hcq0 hDn)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hFz (by exact astra4wPowerNat102_001 hcq1 hcq5) hz0l hz0beta (Or.inr (by exact astra4wPowerNat102_144 hcq8 hcq1 hcq0)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat102_145 hcq8 hcq0)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top_S00 hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by exact astra4wPowerNat102_006 hcq1 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_178 hcq8 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_179 hcq8 hcq1 hcq0 h)
      · exact absurd h (by exact astra4wPowerNat102_180 hcq8 hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_181 h hcq8 hcq1 hcq0)
      · exact absurd h (by exact astra4wPowerNat102_182 hcq8 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_183 h hcq8 hcq1 hcq0 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_184 hcq8 hcq1 h hcq0)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_185 hcq8 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_186 hcq8 hcq1 hcq0 h)
      · exact absurd h (by exact astra4wPowerNat102_187 hcq8 hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat102_188 hcq8 hcq1 hcq0 h)
      · exact absurd h (by exact astra4wPowerNat102_189 hcq8 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_190 h hcq8 hcq1 hcq0 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_191 h hcq8 hcq1 hcq0)
  have hr1 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hFz (by exact astra4wPowerNat102_007 hcq8) (by exact astra4wPowerNat102_010 hcq8 hcq1 hcq0) (by exact astra4wPowerNat102_011 hcq8 hcq1 hcq5) (by exact astra4wPowerNat102_014 hcq1 hcq5) hz1l hz1beta (Or.inr (by exact astra4wPowerNat102_146 hcq8 hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat102_147 hcq8 hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat102_148 hcq8 hcq1 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat102_149 hcq8 hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat102_150 hcq8 hcq0))
  have hct1 := xiQuarticChamberFace5810_coeff_top_S00 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat102_020 hcq1 hcq0)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS00810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `EE·BBB·BBC·BCC·CCC` dies on power system `S00` (carriers κ, ξ). -/
theorem quarticChamberBCDEF51810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF51810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_112 hcq12 hcq0 h hcq11 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat102_113 hcq12 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_023 hcq12 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_114 hcq12 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_025 hcq12 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_026 hcq12 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_027 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_028 hcq12 hcq1 hcq0 h)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_115 hcq12 hcq1 hcq0 h hcq6 hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_116 hcq12 hcq0 h hcq11 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat102_117 hcq12 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_032 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_118 hcq12 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_034 hcq12 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_035 hcq12 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_036 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_037 hcq12 hcq1 hcq0 h)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_119 hcq12 hcq1 h hcq0 hcq6)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_120 hcq12 h hcq0 hcq11 hcq4 hGn)
      · exact Or.inr (by exact astra4wPowerNat102_121 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_041 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_122 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_043 hcq12 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_044 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_045 hcq12 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_046 hcq12 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_047 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_048 hcq12 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_049 hcq12 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_050 hcq12 hcq1 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_123 hcq12 h hcq0 hcq11 hcq4 hGn)
      · exact Or.inr (by exact astra4wPowerNat102_124 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_053 h hcq12 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_125 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_055 hcq12 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_056 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_057 hcq12 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_058 hcq12 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_059 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_060 hcq12 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_061 hcq12 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_126 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat102_063 hcq12 hcq1 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_064 h hcq12 hcq1 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_127 h hcq12 hcq0 hcq6 hGn)
    · exact Or.inr (by exact astra4wPowerNat102_128 h hcq12 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat102_067 hcq12 hcq0 hcq6 h)
    · exact Or.inr (by exact astra4wPowerNat102_129 h hcq12 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat102_069 h hcq12 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_070 h hcq12 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat102_071 h hcq12 hcq1 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat102_072 h hcq12 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_073 h hcq12 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_074 h hcq12 hcq1 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat102_075 h hcq12 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_130 h hcq12 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat102_077 h hcq12 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_078 h hcq12 hcq0 hcq6)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hGz (by exact astra4wPowerNat102_000 hcq12 hcq0 hcq6) (by exact astra4wPowerNat102_100 hcq1 hcq0 hcq4) (by exact astra4wPowerNat102_002 hcq0 hcq6) hz0l hz0beta (Or.inr (by exact astra4wPowerNat102_101 hcq12 hcq1 hcq0 hcq4)) hz0delta (Or.inr (by exact astra4wPowerNat102_102 hcq12 hcq0 hcq6 hcq4)) hz0zeta (Or.inr (by exact astra4wPowerNat102_103 hcq12 hcq0 hcq4)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top_S00 hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by exact astra4wPowerNat102_006 hcq1 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_079 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_080 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_081 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_082 h hcq12 hcq1 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_131 h hcq12 hcq1 hcq0 hcq6 hcq4)
      · exact absurd h (by exact astra4wPowerNat102_132 hcq12 hcq0 hcq4 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_133 hcq12 hcq1 h hcq0 hcq6 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_134 hcq12 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_135 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_136 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_137 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_138 h hcq12 hcq1 hcq0 hcq6 hcq4)
      · exact absurd h (by exact astra4wPowerNat102_139 hcq12 hcq0 hcq4 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_140 h hcq12 hcq1 hcq0 hcq4)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_093 hcq6 h)
      · exact Or.inr (by exact astra4wPowerNat102_094 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_095 hcq12 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_096 hcq12 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_141 hcq12 hcq0 h hcq6 hcq4)
      · exact absurd h (by exact astra4wPowerNat102_142 hcq12 hcq0 hcq4 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_143 h hcq12 hcq1 hcq0 hcq4)
  have hr1 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hGz (by exact astra4wPowerNat102_007 hcq12) (by exact astra4wPowerNat102_008 hcq1 hcq0 hcq6) (by exact astra4wPowerNat102_009 hcq12 hcq0 hcq6) (by exact astra4wPowerNat102_010 hcq12 hcq1 hcq0) (by exact astra4wPowerNat102_104 hcq0 hcq6 hcq4) (by exact astra4wPowerNat102_105 hcq12 hcq1 hcq0 hcq4) (by exact astra4wPowerNat102_012 hcq12 hcq0 hcq6) (by exact astra4wPowerNat102_013 hcq12 hcq1 hcq0 hcq6) (by exact astra4wPowerNat102_106 hcq12 hcq0 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat102_107 hcq12 hcq1 hcq0 hcq6 hcq4)) hz1delta (Or.inr (by exact astra4wPowerNat102_108 hcq12 hcq1 hcq0 hcq6 hcq4)) (Or.inr (by exact astra4wPowerNat102_109 hcq12 hcq1 hcq0 hcq6 hcq4)) (Or.inr (by exact astra4wPowerNat102_110 hcq12 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat102_111 hcq12 hcq0 hcq6 hcq4))
  have hct1 := xiQuarticChamberFace5810_coeff_top_S00 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat102_020 hcq1 hcq0)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS00810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `EE·BBB·BBC·BCC·CCC` dies on power system `S00` (carriers κ, ξ). -/
theorem quarticChamberBCDEG51810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG51810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_021 hcq12 hcq1 hcq0 h hcq6 hcq5)
      · exact Or.inr (by exact astra4wPowerNat102_022 hcq12 hAF hcq0 h hFn)
      · exact Or.inr (by exact astra4wPowerNat102_023 hcq12 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_024 hcq12 hcq0 h hFn hcq9)
      · exact Or.inr (by exact astra4wPowerNat102_025 hcq12 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_026 hcq12 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_027 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_028 hcq12 hcq1 hcq0 h)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_029 hcq12 hcq1 hcq0 h hcq6 hcq5)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_030 hcq12 hcq1 hcq0 h hcq6 hcq5)
      · exact Or.inr (by exact astra4wPowerNat102_031 hcq12 hcq0 h hFn hcq9)
      · exact Or.inr (by exact astra4wPowerNat102_032 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_033 hcq12 hcq0 h hFn hcq9)
      · exact Or.inr (by exact astra4wPowerNat102_034 hcq12 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_035 hcq12 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_036 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_037 hcq12 hcq1 hcq0 h)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_038 hcq12 hcq1 h hcq0 hcq6 hcq5)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_039 hcq12 hcq1 h hcq0 hcq6 hcq5)
      · exact Or.inr (by exact astra4wPowerNat102_040 hcq12 h hcq0 hFn hcq9)
      · exact Or.inr (by exact astra4wPowerNat102_041 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_042 hcq12 h hcq0 hFn hcq9)
      · exact Or.inr (by exact astra4wPowerNat102_043 hcq12 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_044 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_045 hcq12 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_046 hcq12 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_047 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_048 hcq12 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_049 hcq12 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_050 hcq12 hcq1 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_051 hcq12 hcq1 h hcq0 hcq6 hcq5)
      · exact Or.inr (by exact astra4wPowerNat102_052 hcq12 hcq1 h hcq0 hcq5 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_053 h hcq12 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_054 hcq12 hcq1 h hcq0 hcq5 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_055 hcq12 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_056 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_057 hcq12 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_058 hcq12 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_059 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat102_060 hcq12 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_061 hcq12 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat102_062 hcq12 h hcq0 hFn hcq9)
      · exact Or.inr (by exact astra4wPowerNat102_063 hcq12 hcq1 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_064 h hcq12 hcq1 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_065 h hcq12 hcq1 hcq0 hcq6 hcq5)
    · exact Or.inr (by exact astra4wPowerNat102_066 h hcq12 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_067 hcq12 hcq0 hcq6 h)
    · exact Or.inr (by exact astra4wPowerNat102_068 h hcq12 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat102_069 h hcq12 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_070 h hcq12 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat102_071 h hcq12 hcq1 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat102_072 h hcq12 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_073 h hcq12 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_074 h hcq12 hcq1 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat102_075 h hcq12 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_076 h hcq12 hcq0 hFn hcq9)
    · exact Or.inr (by exact astra4wPowerNat102_077 h hcq12 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat102_078 h hcq12 hcq0 hcq6)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by exact astra4wPowerNat102_000 hcq12 hcq0 hcq6) (by exact astra4wPowerNat102_001 hcq1 hcq5) (by exact astra4wPowerNat102_002 hcq0 hcq6) hz0l hz0beta (Or.inr (by exact astra4wPowerNat102_003 hcq12 hcq1 hcq0 hcq6)) hz0delta (Or.inr (by exact astra4wPowerNat102_004 hcq12 hcq0 hcq6)) hz0zeta (Or.inr (by exact astra4wPowerNat102_005 hcq12 hcq0 hcq6)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top_S00 hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by exact astra4wPowerNat102_006 hcq1 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face1_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_079 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_080 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_081 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_082 h hcq12 hcq1 hcq0 hcq6)
      · exact absurd h (by exact astra4wPowerNat102_083 hcq12 hcq0 hcq6 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_084 h hcq12 hcq1 hcq0 hcq6 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_085 hcq12 hcq1 h hcq0 hcq6 hcq5)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_086 hcq12 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_087 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_088 hcq12 hcq1 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_089 hcq12 hcq1 hcq0 h hcq6)
      · exact absurd h (by exact astra4wPowerNat102_090 hcq12 hcq0 hcq6 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_091 h hcq12 hcq1 hcq0 hcq6 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_092 hcq12 hcq1 h hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat102_093 hcq6 h)
      · exact Or.inr (by exact astra4wPowerNat102_094 hcq1 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_095 hcq12 hcq0 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat102_096 hcq12 hcq0 h hcq6)
      · exact absurd h (by exact astra4wPowerNat102_097 hcq12 hcq0 hcq6 hFn)
      · exact Or.inr (by exact astra4wPowerNat102_098 h hcq12 hcq1 hcq0 hcq6 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat102_099 h hcq12 hcq1 hcq0)
  have hr1 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by exact astra4wPowerNat102_007 hcq12) (by exact astra4wPowerNat102_008 hcq1 hcq0 hcq6) (by exact astra4wPowerNat102_009 hcq12 hcq0 hcq6) (by exact astra4wPowerNat102_010 hcq12 hcq1 hcq0) (by exact astra4wPowerNat102_011 hcq12 hcq1 hcq5) (by exact astra4wPowerNat102_012 hcq12 hcq0 hcq6) (by exact astra4wPowerNat102_013 hcq12 hcq1 hcq0 hcq6) (by exact astra4wPowerNat102_014 hcq1 hcq5) hz1l hz1beta (Or.inr (by exact astra4wPowerNat102_015 hcq12 hcq1 hcq0 hcq6)) hz1delta (Or.inr (by exact astra4wPowerNat102_016 hcq12 hcq1 hcq0 hcq6 hcq5)) (Or.inr (by exact astra4wPowerNat102_017 hcq12 hcq1 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat102_018 hcq12 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat102_019 hcq12 hcq0 hcq6))
  have hct1 := xiQuarticChamberFace5810_coeff_top_S00 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat102_020 hcq1 hcq0)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS00810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS00810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
