import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch

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
private theorem astra4wPowerNat109_000
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_001
    {a b c f g : ℕ}
    (h0 : c + f < b + g)
    (h1 : g = a + 2 * b)
    : c + f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_002
    {a b d e g : ℕ}
    (h0 : d + e < b + g)
    (h1 : g = a + 2 * b)
    : d + e < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_003
    {a b c d e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_004
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_005
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_006
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : b + 2 * c = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_007
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : b + g = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_008
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_009
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d + e < b + g)
    : a + b + c + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_010
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_011
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_012
    {a b c d e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : a + d + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_013
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : g = a + 2 * b)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_014
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_015
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : b + d + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_016
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : c + e < a + g)
    (h2 : d + e < b + g)
    (h3 : g = a + 2 * b)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_017
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_018
    {a b c d e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_019
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_020
    {a b c d e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_021
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_022
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_023
    {a b c e : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : 2 * c + e = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_024
    {a b e g : ℕ}
    (h0 : g = a + 2 * b)
    : e + g = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_025
    {a b c d e g : ℕ}
    (h0 : 6 * a ≤ d + g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_026
    {a b c e f g : ℕ}
    (h0 : 6 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_027
    {a b c d e g : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_028
    {a b c e f g : ℕ}
    (h0 : 6 * a ≤ 2 * b + f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_029
    {a b c e g : ℕ}
    (h0 : 6 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_030
    {a b c d e g : ℕ}
    (h0 : 6 * a ≤ b + 2 * d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_031
    {a b c d e g : ℕ}
    (h0 : 6 * a ≤ 2 * c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_032
    {a b c e g : ℕ}
    (h0 : 6 * a ≤ 3 * b + c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_033
    {a b c d e f g : ℕ}
    (h0 : 5 * a < a + 3 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d + e < b + g)
    (h6 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_034
    {a b c d e g : ℕ}
    (h0 : 5 * a ≤ d + g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_035
    {a b c e f g : ℕ}
    (h0 : 5 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_036
    {a b c d e g : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_037
    {a b c e f g : ℕ}
    (h0 : 5 * a ≤ 2 * b + f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_038
    {a b c e g : ℕ}
    (h0 : 5 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_039
    {a b c d e g : ℕ}
    (h0 : 5 * a ≤ b + 2 * d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_040
    {a b c d e g : ℕ}
    (h0 : 5 * a ≤ 2 * c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_041
    {a b c e g : ℕ}
    (h0 : 5 * a ≤ 3 * b + c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_042
    {a b c d e g : ℕ}
    (h0 : 4 * a < a + 3 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_043
    {a b c d e g : ℕ}
    (h0 : 4 * a ≤ d + g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_044
    {a b c e f g : ℕ}
    (h0 : 4 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_045
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_046
    {a b c e f g : ℕ}
    (h0 : 4 * a ≤ 2 * b + f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_047
    {a b c e g : ℕ}
    (h0 : 4 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_048
    {a b c d e g : ℕ}
    (h0 : 4 * a ≤ b + 2 * d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_049
    {a b c d e g : ℕ}
    (h0 : 4 * a ≤ 2 * c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_050
    {a b c e g : ℕ}
    (h0 : 4 * a ≤ 3 * b + c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_051
    {a b c e g : ℕ}
    (h0 : 4 * a ≤ b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_052
    {a b c d e g : ℕ}
    (h0 : 4 * a ≤ c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_053
    {a b c e g : ℕ}
    (h0 : 4 * a ≤ 3 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_054
    {a b c e g : ℕ}
    (h0 : 3 * a < a + 3 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_055
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_056
    {a b c e f g : ℕ}
    (h0 : 3 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_057
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_058
    {a b c e f g : ℕ}
    (h0 : 3 * a ≤ 2 * b + f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_059
    {a b c e g : ℕ}
    (h0 : 3 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_060
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ b + 2 * d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_061
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ 2 * c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_062
    {a b c e g : ℕ}
    (h0 : 3 * a ≤ 3 * b + c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_063
    {a b c e g : ℕ}
    (h0 : 3 * a ≤ b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_064
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_065
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_066
    {a b c e f g : ℕ}
    (h0 : 3 * a ≤ f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_067
    {a b c e g : ℕ}
    (h0 : 3 * a ≤ b + c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_068
    {a b c e g : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_069
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_070
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_071
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ 2 * b + d)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_072
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_073
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_074
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_075
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_076
    {a b c e g : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_077
    {a b c e g : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_078
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_079
    {a b c e g : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_080
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_081
    {a b c e g : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_082
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_083
    {a b c d e g : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_084
    {a b c d e g : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_085
    {a b c d e g : ℕ}
    (h0 : 9 * a ≤ 4 * d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_086
    {a b c d e g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_087
    {a b c d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d + e < b + g)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_088
    {a b c d e g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_089
    {a b c d e f g : ℕ}
    (h0 : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d + e < b + g)
    (h6 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_090
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_091
    {a b c d e g : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_092
    {a b c d e g : ℕ}
    (h0 : 7 * a ≤ 4 * d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_093
    {a b c d e g : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_094
    {a b c d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d + e < b + g)
    (h6 : g = a + 2 * b)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_095
    {a b c d e g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_096
    {a b c d e f g : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d + e < b + g)
    (h6 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_097
    {a b d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a ≤ 4 * b)
    (h2 : d + e < b + g)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_098
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ 4 * c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d + e < b + g)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_099
    {a b c d e g : ℕ}
    (h0 : 5 * a ≤ 4 * d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_100
    {a b c d e g : ℕ}
    (h0 : 7 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_101
    {a b c d e f g : ℕ}
    (h0 : 9 * a ≤ 4 * f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d + e < b + g)
    (h6 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_102
    {a b c d e g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_103
    {a b c d e f g : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d + e < b + g)
    (h6 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_104
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_105
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_106
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_107
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : a + b + c < (a + 2 * b + e) ∧ 3 * b < (a + 2 * b + e) ∧ a + f < (a + 2 * b + e) ∧ b + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_108
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_109
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_110
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_111
    {a b d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_112
    {a b d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_113
    {a b d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 6 * a ≤ b + 2 * d)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_114
    {a b c d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 6 * a ≤ 2 * c + d)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : a + 2 * b = 2 * c)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_115
    {a b c e f g : ℕ}
    (h0 : 5 * a < a + 3 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_116
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 5 * a ≤ d + g)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d = 0)
    (h4 : e + f < a + b + g)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_117
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d = 0)
    (h4 : e + f < a + b + g)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_118
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 5 * a ≤ b + 2 * d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d = 0)
    (h4 : e + f < a + b + g)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_119
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : e + f < a + b + g)
    (h6 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_120
    {a b c e g : ℕ}
    (h0 : 4 * a < a + 3 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_121
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 4 * a ≤ d + g)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : c + f < b + g)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_122
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : c + f < b + g)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_123
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d = 0)
    (h4 : e + f < a + b + g)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_124
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : c + f < b + g)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_125
    {a b c d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 4 * a ≤ c + d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : c + e < a + g)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_126
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_127
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_128
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d = 0)
    (h4 : e + f < a + b + g)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_129
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ 2 * c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_130
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ c + d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : e + f < a + b + g)
    (h6 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_131
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_132
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ 2 * b + d)
    (h3 : c + e < a + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_133
    {a b c e g : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_134
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d = 0)
    (h4 : e + f < a + b + g)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_135
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_136
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : c + f < b + g)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_137
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d = 0)
    (h4 : e + f < a + b + g)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_138
    {a b c e g : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : c + e < a + g)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_139
    {a b c e g : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_140
    {a b c d e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : ¬ (9 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_141
    {a b c e g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_142
    {a b c e f g : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_143
    {a b c e g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_144
    {a b c e f g : ℕ}
    (h0 : 3 * a + b + c < a + 2 * b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_145
    {a b c e g : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : c + e < a + g)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_146
    {a b c e g : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_147
    {a b c d e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : ¬ (7 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_148
    {a b c e g : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_149
    {a b c e f g : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_150
    {a b c e g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_151
    {a b c e f g : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_152
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : b + c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_153
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_154
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_155
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 6 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_156
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 6 * a ≤ 2 * b + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_157
    {a b c d e g : ℕ}
    (h0 : 5 * a < a + 3 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_158
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 5 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_159
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_160
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 4 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_161
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_162
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d + e < b + g)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_163
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d + e < b + g)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_164
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_165
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_166
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_167
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_168
    {a b c d e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : ¬ (13 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_169
    {a b c d e g : ℕ}
    (h0 : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_170
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_171
    {a b c d e g : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_172
    {a b c d e g : ℕ}
    (h0 : 7 * a ≤ 4 * d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_173
    {a b c d e g : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_174
    {a b c d e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : ¬ (11 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_175
    {a b c d e g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_176
    {a b c d e g : ℕ}
    (h0 : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_177
    {a b c d e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d + e < b + g)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : ¬ (9 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_178
    {a b c d e g : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d + e < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_179
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : g = a + 2 * b)
    : b + c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_180
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : g = a + 2 * b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_181
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : g = a + 2 * b)
    : 2 * b + c < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_182
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : g = a + 2 * b)
    : a + b + c < (a + 2 * b + e) ∧ 3 * b < (a + 2 * b + e) ∧ b + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_183
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_184
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : g = a + 2 * b)
    : b + c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_185
    {a b c e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : g = a + 2 * b)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_186
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : 6 * a ≤ e + f)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_187
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : 6 * a ≤ 2 * b + f)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_188
    {a b c e g : ℕ}
    (h0 : 5 * a < a + 3 * b)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_189
    {a b d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_190
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : 5 * a ≤ e + f)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_191
    {a b d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_192
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : 5 * a ≤ 2 * b + f)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_193
    {a b d e g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 5 * a ≤ b + 2 * d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_194
    {a b c d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 5 * a ≤ 2 * c + d)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : a + 2 * b = 2 * c)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_195
    {a b d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 4 * a ≤ d + g)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_196
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 4 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_197
    {a b d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_198
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * a ≤ 2 * b + f)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_199
    {a b d e g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_200
    {a b c d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : a + 2 * b + 2 * g = 4 * e)
    (h4 : a + 2 * b = 2 * c)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_201
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_202
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_203
    {a b d e g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_204
    {a b c d e g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ c + d)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_205
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b + 2 * g = 4 * e)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_206
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_207
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_208
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_209
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_210
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : ¬ (9 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_211
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : ¬ (13 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_212
    {a b c e g : ℕ}
    (h0 : 3 * a + b + c < a + 2 * b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ b + c + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_213
    {a b c d e g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : ¬ (7 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_214
    {a b c e f g : ℕ}
    (h0 : a + 2 * b + 2 * g = 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : ¬ (11 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat109_215
    {a b c e g : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e)
    (h1 : a + 2 * b + 2 * g = 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEG` / `BG·CG·EE·BBB·BBC·BCC·CCC` dies on power system `S11` (carriers κ, ξ). -/
theorem quarticChamberBCEG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEG7810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat109_111 hAD hcq6 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_186 hcq6 hAF h hcq1 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_112 hAD hcq6 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_187 hcq6 hAF h hcq1 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_029 h hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_113 hAD hcq6 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_114 hAD hcq6 h hcq1 hcq0 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_032 h hcq1 hcq0 hcq9 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_188 h hcq1 hcq0 hcq9 hcq2)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_189 hAD hcq6 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_190 hcq6 hAF h hcq1 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_191 hAD hcq6 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_192 hcq6 hAF h hcq1 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_038 h hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_193 hcq6 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_194 hAD hcq6 h hcq1 hcq0 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_041 h hcq1 hcq0 hcq9 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_120 h hcq1 hcq0 hcq9 hcq2)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_195 hAD hcq6 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_196 hcq6 h hcq1 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_197 hAD hcq6 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_198 hcq6 hAF h hcq1 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_047 h hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_199 hcq6 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_200 hAD hcq6 h hcq1 hcq0 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_050 h hcq1 hcq0 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_051 h hcq1 hcq0 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_125 hAD h hcq1 hcq0 hcq9 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_053 h hcq1 hcq0 hcq9 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_054 h hcq1 hcq0 hcq9 hcq2)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_126 h hcq1 hcq0 hcq9 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_201 hcq6 h hcq1 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_127 h hcq1 hcq0 hcq9 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_202 hcq6 h hcq1 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_059 h hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_203 hcq6 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_129 h hcq1 hcq0 hcq9 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_062 h hcq1 hcq0 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_063 h hcq1 hcq0 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_204 hcq6 h hcq1 hcq0 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_065 hcq1 hcq0 h hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_205 hcq6 h hcq1 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_067 h hcq1 hcq0 hcq9 hcq2)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_068 h hcq1 hcq0 hcq9 hcq2)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_131 h hcq1 hcq0 hcq9 hDn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_165 h hcq1 hcq0 hcq9 hFn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_132 hcq1 hcq0 h hcq9 hDn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_166 h hcq1 hcq0 hcq9 hFn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_133 h hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_206 h hcq1 hcq0 hcq9 hDn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_135 h hcq1 hcq0 hcq9 hDn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_076 h hcq1 hcq0 hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_077 h hcq1 hcq0 hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_207 h hcq1 hcq0 hcq9 hDn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_079 h hcq1 hcq0 hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_208 h hcq1 hcq0 hcq9 hFn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_081 h hcq1 hcq0 hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_209 h hcq1 hcq0 hcq9 hDn hcq2)
  have hr0 : (kappaQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hFz hz0l hz0beta (Or.inr (by exact astra4wPowerNat109_179 hcq1 hcq0 hcq9 hcq2)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat109_180 hcq1 hcq0 hcq9 hcq2)) hz0theta
  have hct0 := kappaQuarticChamberFace9810_coeff_top_S11 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat109_006 hcq0) (by exact astra4wPowerNat109_007 hcq2)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face9_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS11810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_138 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat109_139 h hcq1 hcq0 hcq9)
      · exact absurd h (by exact astra4wPowerNat109_210 hcq1 hcq0 hcq9 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_141 h hcq1 hcq0 hcq9 hcq2)
      · exact absurd h (by exact astra4wPowerNat109_211 hcq1 hcq0 hcq9 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_143 h hcq1 hcq0 hcq9 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_212 h hcq1 hcq0 hcq9 hcq2)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_145 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat109_146 h hcq1 hcq0 hcq9)
      · exact absurd h (by exact astra4wPowerNat109_213 hcq1 hcq0 hcq9 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_148 h hcq1 hcq0 hcq9 hcq2)
      · exact absurd h (by exact astra4wPowerNat109_214 hcq1 hcq0 hcq9 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_150 h hcq1 hcq0 hcq9 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_215 h hcq1 hcq0 hcq9 hcq2)
  have hr1 : (xiQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest16810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hFz (by exact astra4wPowerNat109_008 hcq1 hcq0 hcq9) (by exact astra4wPowerNat109_011 hcq1 hcq0 hcq9) (by exact astra4wPowerNat109_013 hcq1 hcq0 hcq9 hcq2) hz1l hz1beta (Or.inr (by exact astra4wPowerNat109_181 hcq1 hcq0 hcq9 hcq2)) (Or.inr (by exact astra4wPowerNat109_182 hcq1 hcq0 hcq9 hcq2)) (Or.inr (by exact astra4wPowerNat109_183 hcq1 hcq0 hcq9 hcq2)) (Or.inr (by exact astra4wPowerNat109_184 hcq1 hcq0 hcq9 hcq2)) (Or.inr (by exact astra4wPowerNat109_185 hcq1 hcq0 hcq9 hcq2))
  have hct1 := xiQuarticChamberFace16810_coeff_top_S11 hAne hBne hCne hEne hGne (D := D) (F := F) (by exact astra4wPowerNat109_023 hcq0) (by exact astra4wPowerNat109_024 hcq2)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face16_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS11810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS11810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc hGc


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
/-- Chamber `BCDEG` / `BG·CG·EE·BBB·BBC·BCC·CCC` dies on power system `S11` (carriers κ, ξ). -/
theorem quarticChamberBCDEG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG13810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat109_025 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_155 hcq9 h hcq1 hcq8 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_027 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_156 hcq9 h hcq1 hcq8 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_029 h hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_030 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_031 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_032 h hcq1 hcq0 hcq14 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_157 h hcq1 hcq0 hcq14 hcq7 hcq2)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_034 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_158 hcq9 h hcq1 hcq8 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_036 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_159 hcq9 h hcq1 hcq8 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_038 h hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_039 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_040 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_041 h hcq1 hcq0 hcq14 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_042 h hcq1 hcq0 hcq14 hcq7 hcq2)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_043 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_160 hcq9 h hcq1 hcq8 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_045 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_161 hcq9 h hcq1 hcq8 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_047 h hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_048 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_049 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_050 h hcq1 hcq0 hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_051 h hcq1 hcq0 hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_052 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_053 h hcq1 hcq0 hcq14 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_054 h hcq1 hcq0 hcq14 hcq2)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_055 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_162 hcq9 h hcq1 hcq7 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_057 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_163 hcq9 h hcq1 hcq7 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_059 h hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_060 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_061 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_062 h hcq1 hcq0 hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_063 h hcq1 hcq0 hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_064 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_065 hcq1 hcq0 h hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_164 hcq9 h hcq1 hcq8 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_067 h hcq1 hcq0 hcq14 hcq2)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_068 h hcq1 hcq0 hcq14 hcq2)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_069 h hcq1 hcq0 hcq14 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_165 h hcq1 hcq0 hcq14 hFn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_071 hcq1 hcq0 h hcq14 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_166 h hcq1 hcq0 hcq14 hFn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_073 h hcq1 hcq0 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_074 h hcq1 hcq0 hcq14 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_075 h hcq1 hcq0 hcq14 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_076 h hcq1 hcq0 hcq14 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_077 h hcq1 hcq0 hcq14 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_078 h hcq1 hcq0 hcq14 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_079 h hcq1 hcq0 hcq14 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_167 h hcq9 hcq1 hcq8 hFn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_081 h hcq1 hcq0 hcq14 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_082 h hcq1 hcq0 hcq14 hcq7 hcq2)
  have hr0 : (kappaQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by exact astra4wPowerNat109_000 hcq1 hcq0 hcq14 hcq7 hcq2) (by exact astra4wPowerNat109_002 hcq7 hcq2) hz0l hz0beta (Or.inr (by exact astra4wPowerNat109_152 hcq1 hcq0 hcq14 hcq7 hcq2)) hz0delta (Or.inr (by exact astra4wPowerNat109_004 hcq1 hcq0 hcq14 hcq7 hcq2)) hz0zeta (Or.inr (by exact astra4wPowerNat109_005 hcq1 hcq0 hcq14 hcq7 hcq2)) hz0theta
  have hct0 := kappaQuarticChamberFace9810_coeff_top_S11 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat109_006 hcq0) (by exact astra4wPowerNat109_007 hcq2)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face9_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS11810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_083 h hcq1 hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat109_084 h hcq1 hcq0 hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat109_085 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_086 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact absurd h (by exact astra4wPowerNat109_168 hcq1 hcq0 hcq14 hcq7 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_088 h hcq1 hcq0 hcq14 hcq7 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_169 h hcq1 hcq0 hcq14 hcq7 hcq2)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_170 h hcq1 hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat109_171 h hcq1 hcq0 hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat109_172 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_173 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact absurd h (by exact astra4wPowerNat109_174 hcq1 hcq0 hcq14 hcq7 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_175 h hcq1 hcq0 hcq14 hcq7 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_176 h hcq1 hcq0 hcq14 hcq2)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_097 hcq1 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat109_098 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat109_099 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_100 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact absurd h (by exact astra4wPowerNat109_177 hcq1 hcq0 hcq14 hcq7 hFn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_102 h hcq1 hcq0 hcq14 hcq7 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_178 h hcq1 hcq0 hcq14 hcq7 hcq2)
  have hr1 : (xiQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest16810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by exact astra4wPowerNat109_008 hcq1 hcq0 hcq14) (by exact astra4wPowerNat109_009 hcq1 hcq0 hcq7) (by exact astra4wPowerNat109_010 hcq1 hcq0 hcq14 hcq7 hcq2) (by exact astra4wPowerNat109_011 hcq1 hcq0 hcq14) (by exact astra4wPowerNat109_013 hcq1 hcq0 hcq14 hcq2) (by exact astra4wPowerNat109_015 hcq1 hcq0 hcq14 hcq7 hcq2) (by exact astra4wPowerNat109_016 hcq1 hcq14 hcq7 hcq2) hz1l hz1beta (Or.inr (by exact astra4wPowerNat109_153 hcq1 hcq0 hcq14 hcq7 hcq2)) hz1delta (Or.inr (by exact astra4wPowerNat109_019 hcq1 hcq0 hcq14 hcq7 hcq2)) (Or.inr (by exact astra4wPowerNat109_154 hcq1 hcq0 hcq14 hcq7 hcq2)) (Or.inr (by exact astra4wPowerNat109_021 hcq1 hcq0 hcq14 hcq7 hcq2)) (Or.inr (by exact astra4wPowerNat109_022 hcq1 hcq0 hcq14 hcq7 hcq2))
  have hct1 := xiQuarticChamberFace16810_coeff_top_S11 hAne hBne hCne hEne hGne (D := D) (F := F) (by exact astra4wPowerNat109_023 hcq0) (by exact astra4wPowerNat109_024 hcq2)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face16_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS11810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS11810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc hGc


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
/-- Chamber `BCEFG` / `BG·CG·EE·BBB·BBC·BCC·CCC` dies on power system `S11` (carriers κ, ξ). -/
theorem quarticChamberBCEFG31810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG31810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_111 hAD hcq9 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_026 h hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_112 hAD hcq9 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_028 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_029 h hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_113 hAD hcq9 h hcq1 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_114 hAD hcq9 h hcq1 hcq0 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_032 h hcq1 hcq0 hcq14 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_115 h hcq1 hcq0 hcq14 hcq7 hcq2)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_116 hcq9 h hcq1 hDn hcq8 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_035 h hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_117 hcq9 h hcq1 hDn hcq8 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_037 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_038 h hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_118 hcq9 h hcq1 hDn hcq8 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_119 hcq9 h hcq1 hcq0 hDn hcq8 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_041 h hcq1 hcq0 hcq14 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_120 h hcq1 hcq0 hcq14 hcq2)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_121 hcq9 h hcq1 hcq0 hcq7 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_044 h hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_122 hcq9 h hcq1 hcq0 hcq7 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_046 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_047 h hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_123 hcq9 h hcq1 hDn hcq8 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_124 hcq9 h hcq1 hcq0 hcq7 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_050 h hcq1 hcq0 hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_051 h hcq1 hcq0 hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_125 hAD h hcq1 hcq0 hcq14 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_053 h hcq1 hcq0 hcq14 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_054 h hcq1 hcq0 hcq14 hcq2)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_126 h hcq1 hcq0 hcq14 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_056 h hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_127 h hcq1 hcq0 hcq14 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_058 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_059 h hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_128 hcq9 h hcq1 hDn hcq8 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_129 h hcq1 hcq0 hcq14 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_062 h hcq1 hcq0 hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_063 h hcq1 hcq0 hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_130 hcq9 h hcq1 hcq0 hDn hcq8 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_065 hcq1 hcq0 h hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_066 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_067 h hcq1 hcq0 hcq14 hcq2)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_068 h hcq1 hcq0 hcq14 hcq2)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_131 h hcq1 hcq0 hcq14 hDn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_070 h hcq0 hcq14 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_132 hcq1 hcq0 h hcq14 hDn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_072 h hcq1 hcq0 hcq14 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_133 h hcq14 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_134 h hcq9 hcq1 hDn hcq8 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_135 h hcq1 hcq0 hcq14 hDn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_076 h hcq1 hcq0 hcq14 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_077 h hcq1 hcq0 hcq14 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_136 h hcq9 hcq1 hcq0 hcq7 hDn hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_079 h hcq1 hcq0 hcq14 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_080 h hcq1 hcq0 hcq14 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_081 h hcq1 hcq0 hcq14 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_137 h hcq9 hcq1 hDn hcq8 hcq2)
  have hr0 : (kappaQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by exact astra4wPowerNat109_001 hcq7 hcq2) hz0l hz0beta (Or.inr (by exact astra4wPowerNat109_104 hcq1 hcq0 hcq14 hcq7 hcq2)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat109_105 hcq1 hcq0 hcq14 hcq7 hcq2)) hz0theta
  have hct0 := kappaQuarticChamberFace9810_coeff_top_S11 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat109_006 hcq0) (by exact astra4wPowerNat109_007 hcq2)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face9_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS11810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_138 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat109_139 h hcq1 hcq0 hcq14)
      · exact absurd h (by exact astra4wPowerNat109_140 hcq1 hcq0 hcq14 hcq7 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_141 h hcq1 hcq0 hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_142 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_143 h hcq1 hcq0 hcq14 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_144 h hcq1 hcq0 hcq14 hcq7 hcq2)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_145 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat109_146 h hcq1 hcq0 hcq14)
      · exact absurd h (by exact astra4wPowerNat109_147 hcq1 hcq0 hcq14 hcq7 hDn hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_148 h hcq1 hcq0 hcq14 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_149 h hcq1 hcq0 hcq14 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_150 h hcq1 hcq0 hcq14 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_151 h hcq1 hcq0 hcq14 hcq7 hcq2)
  have hr1 : (xiQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest16810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by exact astra4wPowerNat109_008 hcq1 hcq0 hcq14) (by exact astra4wPowerNat109_011 hcq1 hcq0 hcq14) (by exact astra4wPowerNat109_013 hcq1 hcq0 hcq14 hcq2) (by exact astra4wPowerNat109_014 hcq1 hcq0 hcq14 hcq7 hcq2) (by exact astra4wPowerNat109_017 hcq1 hcq0 hcq14 hcq7 hcq2) hz1l hz1beta (Or.inr (by exact astra4wPowerNat109_106 hcq1 hcq0 hcq14 hcq7 hcq2)) (Or.inr (by exact astra4wPowerNat109_107 hcq1 hcq0 hcq14 hcq7 hcq2)) (Or.inr (by exact astra4wPowerNat109_108 hcq1 hcq0 hcq14 hcq7 hcq2)) (Or.inr (by exact astra4wPowerNat109_109 hcq1 hcq0 hcq14 hcq7 hcq2)) (Or.inr (by exact astra4wPowerNat109_110 hcq1 hcq0 hcq14 hcq7 hcq2))
  have hct1 := xiQuarticChamberFace16810_coeff_top_S11 hAne hBne hCne hEne hGne (D := D) (F := F) (by exact astra4wPowerNat109_023 hcq0) (by exact astra4wPowerNat109_024 hcq2)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face16_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS11810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS11810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc hGc


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
/-- Chamber `BCDEFG` / `BG·CG·EE·BBB·BBC·BCC·CCC` dies on power system `S11` (carriers κ, ξ). -/
theorem quarticChamberBCDEFG61810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG61810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_025 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_026 h hcq0 hcq20 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_027 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_028 h hcq1 hcq0 hcq20 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_029 h hcq20 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_030 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_031 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_032 h hcq1 hcq0 hcq20 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_033 h hcq1 hcq0 hcq20 hcq7 hcq9 hcq2)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_034 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_035 h hcq0 hcq20 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_036 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_037 h hcq1 hcq0 hcq20 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_038 h hcq20 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_039 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_040 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_041 h hcq1 hcq0 hcq20 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_042 h hcq1 hcq0 hcq20 hcq9 hcq2)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_043 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_044 h hcq0 hcq20 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_045 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_046 h hcq1 hcq0 hcq20 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_047 h hcq20 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_048 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_049 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_050 h hcq1 hcq0 hcq20 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_051 h hcq1 hcq0 hcq20 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_052 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_053 h hcq1 hcq0 hcq20 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_054 h hcq1 hcq0 hcq20 hcq2)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_055 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_056 h hcq0 hcq20 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_057 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_058 h hcq1 hcq0 hcq20 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_059 h hcq20 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_060 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_061 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_062 h hcq1 hcq0 hcq20 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_063 h hcq1 hcq0 hcq20 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_064 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_065 hcq1 hcq0 h hcq20 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_066 h hcq1 hcq0 hcq20 hcq7 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_067 h hcq1 hcq0 hcq20 hcq2)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_068 h hcq1 hcq0 hcq20 hcq2)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_069 h hcq1 hcq0 hcq20 hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_070 h hcq0 hcq20 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_071 hcq1 hcq0 h hcq20 hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_072 h hcq1 hcq0 hcq20 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_073 h hcq1 hcq0 hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_074 h hcq1 hcq0 hcq20 hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_075 h hcq1 hcq0 hcq20 hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_076 h hcq1 hcq0 hcq20 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_077 h hcq1 hcq0 hcq20 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_078 h hcq1 hcq0 hcq20 hcq9 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_079 h hcq1 hcq0 hcq20 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_080 h hcq1 hcq0 hcq20 hcq7 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_081 h hcq1 hcq0 hcq20 hcq2)
    · exact Or.inr (by exact astra4wPowerNat109_082 h hcq1 hcq0 hcq20 hcq9 hcq2)
  have hr0 : (kappaQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat109_000 hcq1 hcq0 hcq20 hcq9 hcq2) (by exact astra4wPowerNat109_001 hcq7 hcq2) (by exact astra4wPowerNat109_002 hcq9 hcq2) hz0l hz0beta (Or.inr (by exact astra4wPowerNat109_003 hcq1 hcq0 hcq20 hcq7 hcq9 hcq2)) hz0delta (Or.inr (by exact astra4wPowerNat109_004 hcq1 hcq0 hcq20 hcq9 hcq2)) hz0zeta (Or.inr (by exact astra4wPowerNat109_005 hcq1 hcq0 hcq20 hcq9 hcq2)) hz0theta
  have hct0 := kappaQuarticChamberFace9810_coeff_top_S11 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat109_006 hcq0) (by exact astra4wPowerNat109_007 hcq2)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face9_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS11810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_083 h hcq1 hcq20 hcq9)
      · exact Or.inr (by exact astra4wPowerNat109_084 h hcq1 hcq0 hcq20 hcq9)
      · exact Or.inr (by exact astra4wPowerNat109_085 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_086 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_087 h hcq1 hcq0 hcq20 hcq7 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_088 h hcq1 hcq0 hcq20 hcq9 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_089 h hcq1 hcq0 hcq20 hcq7 hcq9 hcq2)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_090 h hcq1 hcq20 hcq9)
      · exact Or.inr (by exact astra4wPowerNat109_091 h hcq1 hcq0 hcq20 hcq9)
      · exact Or.inr (by exact astra4wPowerNat109_092 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_093 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_094 h hcq1 hcq0 hcq20 hcq7 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_095 h hcq1 hcq0 hcq20 hcq9 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_096 h hcq1 hcq0 hcq20 hcq7 hcq9 hcq2)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat109_097 hcq1 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat109_098 h hcq1 hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat109_099 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_100 h hcq1 hcq0 hcq20 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_101 h hcq1 hcq0 hcq20 hcq7 hcq9 hcq2)
      · exact Or.inr (by exact astra4wPowerNat109_102 h hcq1 hcq0 hcq20 hcq9 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat109_103 h hcq1 hcq0 hcq20 hcq7 hcq9 hcq2)
  have hr1 : (xiQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest16810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat109_008 hcq1 hcq0 hcq20) (by exact astra4wPowerNat109_009 hcq1 hcq0 hcq9) (by exact astra4wPowerNat109_010 hcq1 hcq0 hcq20 hcq9 hcq2) (by exact astra4wPowerNat109_011 hcq1 hcq0 hcq20) (by exact astra4wPowerNat109_012 hcq1 hcq0 hcq7 hcq9 hcq2) (by exact astra4wPowerNat109_013 hcq1 hcq0 hcq20 hcq2) (by exact astra4wPowerNat109_014 hcq1 hcq0 hcq20 hcq7 hcq2) (by exact astra4wPowerNat109_015 hcq1 hcq0 hcq20 hcq9 hcq2) (by exact astra4wPowerNat109_016 hcq1 hcq20 hcq9 hcq2) (by exact astra4wPowerNat109_017 hcq1 hcq0 hcq20 hcq7 hcq2) hz1l hz1beta (Or.inr (by exact astra4wPowerNat109_018 hcq1 hcq0 hcq20 hcq7 hcq9 hcq2)) hz1delta (Or.inr (by exact astra4wPowerNat109_019 hcq1 hcq0 hcq20 hcq9 hcq2)) (Or.inr (by exact astra4wPowerNat109_020 hcq1 hcq0 hcq20 hcq7 hcq9 hcq2)) (Or.inr (by exact astra4wPowerNat109_021 hcq1 hcq0 hcq20 hcq9 hcq2)) (Or.inr (by exact astra4wPowerNat109_022 hcq1 hcq0 hcq20 hcq9 hcq2))
  have hct1 := xiQuarticChamberFace16810_coeff_top_S11 hAne hBne hCne hEne hGne (D := D) (F := F) (by exact astra4wPowerNat109_023 hcq0) (by exact astra4wPowerNat109_024 hcq2)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face16_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS11810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS11810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hCc hEc hGc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
