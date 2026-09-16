import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch

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
private theorem astra4wPowerNat106_000
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    : b + c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_001
    {a b : ℕ}
    (h0 : 0 < a)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_002
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : b + 2 * c = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_003
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : b + g = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_004
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : g = a + 2 * b)
    : 4 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_005
    {a b c e g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 2 * b + e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_006
    {a b c e g : ℕ}
    (h0 : 4 * e < a + 2 * b + 2 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : g = a + 2 * b)
    : 2 * e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_007
    {a b c g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) ∧ g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_008
    {a b c e g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : g = a + 2 * b)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_009
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    : a + b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_010
    {a b c : ℕ}
    (h0 : 0 < a)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_011
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_012
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : 3 * c = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_013
    {a b c g : ℕ}
    (h0 : g = a + 2 * b)
    : c + g = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_014
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : g = a + 2 * b)
    : 4 * b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_015
    {a b c e g : ℕ}
    (h0 : c + e < a + g)
    (h1 : g = a + 2 * b)
    : 2 * b + c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_016
    {a b c e g : ℕ}
    (h0 : 4 * e < a + 2 * b + 2 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : g = a + 2 * b)
    : c + 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_017
    {a b c e g : ℕ}
    (h0 : 0 < a)
    (h1 : 4 * e < a + 2 * b + 2 * g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_018
    {a b c e g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : g = a + 2 * b)
    : 2 * b + c < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_019
    {a b c e g : ℕ}
    (h0 : 0 < a)
    (h1 : 4 * e < a + 2 * b + 2 * g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_020
    {a b c g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : g = a + 2 * b)
    : a + 2 * b < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_021
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    : b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_022
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : a + 2 * b + 2 * c = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_023
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : a + 2 * b + g = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_024
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : 4 * c = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_025
    {a b c g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : g = a + 2 * b)
    : 2 * c + g = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_026
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : 2 * g = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_027
    {a b d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_028
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : 2 * g < 5 * a + 2 * b)
    (h3 : 6 * a ≤ e + f)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_029
    {a b d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_030
    {a b f g : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 6 * a ≤ 2 * b + f)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_031
    {a b c e g : ℕ}
    (h0 : 6 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_032
    {a b d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 6 * a ≤ b + 2 * d)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_033
    {a b c d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 6 * a ≤ 2 * c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_034
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 6 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_035
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_036
    {a b d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_037
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : 2 * g < 5 * a + 2 * b)
    (h3 : 5 * a ≤ e + f)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_038
    {a b d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_039
    {a b f g : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ 2 * b + f)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_040
    {a b c e g : ℕ}
    (h0 : 5 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_041
    {a b d e g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_042
    {a b c d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ 2 * c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_043
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_044
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_045
    {a b d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ d + g)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_046
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ e + f)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_047
    {a b d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_048
    {a b f g : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ 2 * b + f)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_049
    {a b c e g : ℕ}
    (h0 : 4 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_050
    {a b d e g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ b + 2 * d)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_051
    {a b c d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_052
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_053
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_054
    {a b c d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_055
    {a b g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_056
    {a b c e g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : c + e < a + g)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_057
    {a b d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ d + g)
    (h2 : d = 0)
    (h3 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_058
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ e + f)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_059
    {a b d g : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d = 0)
    (h3 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_060
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ 2 * b + f)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_061
    {a b c e g : ℕ}
    (h0 : 3 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_062
    {a b d e g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ b + 2 * d)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_063
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_064
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_065
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_066
    {a b c d e g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_067
    {a b g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a ≤ b)
    (h2 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_068
    {a b e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ f)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_069
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_070
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_071
    {a b d g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ d + g)
    (h2 : d = 0)
    (h3 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_072
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_073
    {a b d : ℕ}
    (h0 : 0 < a)
    (h1 : a ≤ 2 * b + d)
    (h2 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_074
    {a b f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 2 * b + f)
    (h2 : f = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_075
    {a b c e g : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_076
    {a b d g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ b + 2 * d)
    (h2 : 2 * g < 5 * a + 2 * b)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_077
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 2 * c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_078
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_079
    {a b c e g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ b + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_080
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ c + d)
    (h2 : 2 * g < 5 * a + 2 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_081
    {a b : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 3 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_082
    {a b f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ f)
    (h2 : f = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_083
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_084
    {a b d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ d)
    (h2 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_085
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_086
    {a b c f g : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ c + f)
    (h3 : a + 2 * b = 2 * c)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_087
    {a b c d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * g < 5 * a + 2 * b)
    (h3 : 5 * a ≤ d + e)
    (h4 : a + 2 * b = 2 * c)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_088
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_089
    {a b c d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_090
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_091
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_092
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_093
    {a b c e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ c + f)
    (h3 : a + 2 * b = 2 * c)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_094
    {a b c d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * g < 5 * a + 2 * b)
    (h3 : 4 * a ≤ d + e)
    (h4 : a + 2 * b = 2 * c)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_095
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_096
    {a b c d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_097
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_098
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ b + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_099
    {a b c g : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_100
    {a b c e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ c + f)
    (h3 : a + 2 * b = 2 * c)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_101
    {a b c d e g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ d + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_102
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_103
    {a b c d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_104
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_105
    {a b c e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ f)
    (h3 : a + 2 * b = 2 * c)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_106
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_107
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a + b < a + 2 * b + c ∧ b + c < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_108
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_109
    {a b c f g : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ c + f)
    (h3 : a + 2 * b = 2 * c)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_110
    {a b c d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * g < 5 * a + 2 * b)
    (h3 : 5 * a ≤ d + e)
    (h4 : a + 2 * b = 2 * c)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_111
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_112
    {a b c d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_113
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_114
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_115
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_116
    {a b c e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ c + f)
    (h3 : a + 2 * b = 2 * c)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_117
    {a b c d e g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * g < 5 * a + 2 * b)
    (h3 : 4 * a ≤ d + e)
    (h4 : a + 2 * b = 2 * c)
    (h5 : d = 0)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_118
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_119
    {a b c d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_120
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_121
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_122
    {a b c g : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_123
    {a b c e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ c + f)
    (h3 : a + 2 * b = 2 * c)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_124
    {a b c d e g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ d + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_125
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_126
    {a b c d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_127
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_128
    {a b c e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ f)
    (h3 : a + 2 * b = 2 * c)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_129
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_130
    {a b c e g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_131
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_132
    {a b c d g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 4 * d < 2 * b + 2 * g)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : b + c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_133
    {a b d g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 4 * d < 2 * b + 2 * g)
    (h2 : g = a + 2 * b)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_134
    {a b d g : ℕ}
    (h0 : a + 4 * d < 2 * b + 2 * g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_135
    {a b c d g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 4 * d < 2 * b + 2 * g)
    (h2 : g = a + 2 * b)
    : a + 2 * d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_136
    {a b c d : ℕ}
    (h0 : d < a + b)
    : b + c + d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_137
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) ∧ g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_138
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    : 2 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_139
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + b < (a + 2 * b + c) ∧ d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_140
    {a b c d g : ℕ}
    (h0 : a + 4 * d < 2 * b + 2 * g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_141
    {a b d : ℕ}
    (h0 : d < a + b)
    : a + 3 * b + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_142
    {a b c d g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 4 * d < 2 * b + 2 * g)
    (h2 : g = a + 2 * b)
    : a + c + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_143
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_144
    {a b c d : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : d < a + b)
    : b + 2 * c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_145
    {a b d g : ℕ}
    (h0 : d < a + b)
    (h1 : g = a + 2 * b)
    : b + d + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_146
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_147
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : g = a + 2 * b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_148
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_149
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_150
    {a b d g : ℕ}
    (h0 : 6 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_151
    {a b d e f g : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 6 * a ≤ e + f)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_152
    {a b d : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_153
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 6 * a ≤ 2 * b + f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_154
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 6 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_155
    {a b d : ℕ}
    (h0 : 6 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_156
    {a b c d : ℕ}
    (h0 : 6 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_157
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_158
    {a b d g : ℕ}
    (h0 : 5 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_159
    {a b d e f g : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_160
    {a b d : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_161
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_162
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_163
    {a b d : ℕ}
    (h0 : 5 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_164
    {a b c d : ℕ}
    (h0 : 5 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_165
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_166
    {a b d g : ℕ}
    (h0 : 4 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_167
    {a b d e f g : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ e + f)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_168
    {a b d : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_169
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_170
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_171
    {a b d : ℕ}
    (h0 : 4 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_172
    {a b c d : ℕ}
    (h0 : 4 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_173
    {a b e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + e)
    (h2 : e < 3 * a)
    (h3 : e = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_174
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_175
    {a b c g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_176
    {a b d g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_177
    {a b d e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : d < a + b)
    (h3 : e = 0)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_178
    {a b d : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_179
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_180
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : e = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_181
    {a b d : ℕ}
    (h0 : 3 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_182
    {a b c d : ℕ}
    (h0 : 3 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_183
    {a b d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : d < a + b)
    (h3 : e = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_184
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_185
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_186
    {a b d g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_187
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d < a + b)
    (h3 : e = 0)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_188
    {a b d : ℕ}
    (h0 : a ≤ 2 * b + d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_189
    {a b f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : f = 0)
    (h3 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_190
    {a b c e : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : e = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_191
    {a b d : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_192
    {a b c d : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_193
    {a b d e g : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d < a + b)
    (h3 : e = 0)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_194
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_195
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_196
    {a b d g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_197
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_198
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e < 3 * a)
    (h5 : e = 0)
    (h6 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_199
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_200
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_201
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_202
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e < 3 * a)
    (h5 : e = 0)
    (h6 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_203
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_204
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_205
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_206
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_207
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_208
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_209
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    : 2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_210
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_211
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e < 3 * a)
    (h5 : e = 0)
    (h6 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_212
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_213
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_214
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_215
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e < 3 * a)
    (h5 : e = 0)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_216
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_217
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_218
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_219
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_220
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_221
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_222
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_223
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + g < a + b + f)
    : b + g < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_224
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    : d + e < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_225
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_226
    {a b d : ℕ}
    (h0 : d < a + b)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_227
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_228
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : c + f = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_229
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_230
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b + e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_231
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + g < a + b + f)
    : c + g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_232
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : d + f < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_233
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    : 2 * e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_234
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) ∧ g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_235
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_236
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b < (a + 2 * b + c) ∧ d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_237
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_238
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_239
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : a + b + f = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_240
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    : a + 2 * d = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_241
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 4 * b < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_242
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    : a + 2 * b + e < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_243
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * b + d < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_244
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b + 2 * c < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_245
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + f = 2 * d)
    (h2 : c + g < a + b + f)
    (h3 : d < a + b)
    : 2 * b + g < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_246
    {a b c d f : ℕ}
    (h0 : b + f = 2 * d)
    (h1 : d < a + b)
    : b + c + f < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_247
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + d + e < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_248
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    : 2 * c + e < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_249
    {a b c d : ℕ}
    (h0 : d < a + b)
    : c + 2 * d < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_250
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    : e + g < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_251
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * f < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_252
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + d < (a + b + c + d) ∧ 2 * b + c < (a + b + c + d) ∧ b + f < (a + b + c + d) ∧ c + e < (a + b + c + d) ∧ 2 * d < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_253
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : a + 2 * b < (a + b + c + d) ∧ b + d < (a + b + c + d) ∧ 2 * c < (a + b + c + d) ∧ g < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_254
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + d < (a + b + c + d) ∧ b + c < (a + b + c + d) ∧ f < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_255
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * b < (a + b + c + d) ∧ e < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_256
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : d < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_257
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : a + d + f = a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_258
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_259
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + g < a + b + f)
    : a + 2 * b + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_260
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    : a + b + d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_261
    {a b d f : ℕ}
    (h0 : b + f = 2 * d)
    (h1 : d < a + b)
    : 3 * b + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_262
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b + c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_263
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + g < a + b + f)
    (h3 : d < a + b)
    : b + d + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_264
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + e + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_265
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + g < a + b + f)
    : 2 * c + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_266
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : c + d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_267
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    : c + 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_268
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : d < a + b)
    : 2 * d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_269
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + g < a + b + f)
    : 2 * g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_270
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_271
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_272
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_273
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_274
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + c < (2 * a + 4 * b) ∧ f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_275
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : a + b + c + f = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_276
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    : a + c + 2 * d = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_277
    {a b f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    : a + 2 * f = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_278
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ d + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_279
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ e + f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_280
    {a b d f : ℕ}
    (h0 : 6 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_281
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 6 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_282
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_283
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : c + g < a + b + f)
    (h6 : d < a + b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_284
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ d + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_285
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_286
    {a b d f : ℕ}
    (h0 : 5 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_287
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 5 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_288
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_289
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : c + g < a + b + f)
    (h6 : d < a + b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_290
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ d + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_291
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ e + f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_292
    {a b d f : ℕ}
    (h0 : 4 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_293
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_294
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_295
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_296
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_297
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_298
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_299
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_300
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ e + f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_301
    {a b d f : ℕ}
    (h0 : 3 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_302
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_303
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_304
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_305
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_306
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a ≤ b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_307
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_308
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_309
    {a b c d f : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_310
    {a b c d f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_311
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_312
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_313
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_314
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_315
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_316
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_317
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_318
    {a b d f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_319
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_320
    {a b d f : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_321
    {a b c d f g : ℕ}
    (h0 : 5 * a ≤ b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_322
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_323
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_324
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_325
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_326
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_327
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a + b < a + 2 * b + c)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : c + g < a + b + f)
    (h6 : d < a + b)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_328
    {a b c d f g : ℕ}
    (h0 : 4 * a ≤ b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_329
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_330
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_331
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_332
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_333
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_334
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a + b < a + 2 * b + c)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_335
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_336
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_337
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_338
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_339
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_340
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_341
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_342
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_343
    {a b c d f : ℕ}
    (h0 : 2 * a + b < a + 2 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_344
    {a b c d f g : ℕ}
    (h0 : 5 * a ≤ b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_345
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_346
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_347
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_348
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_349
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_350
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a + d < a + b + c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : c + g < a + b + f)
    (h6 : d < a + b)
    : 4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 3 * a + f < a + b + c + d ∧ 2 * a + b + e < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + c + f < a + b + c + d ∧ a + d + e < a + b + c + d ∧ 2 * b + f < a + b + c + d ∧ b + c + e < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d ∧ d + g < a + b + c + d ∧ e + f < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_351
    {a b c d f g : ℕ}
    (h0 : 4 * a ≤ b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_352
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_353
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_354
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_355
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_356
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_357
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a + d < a + b + c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a + d < a + b + c + d ∧ 2 * a + b + c < a + b + c + d ∧ a + 3 * b < a + b + c + d ∧ 2 * a + f < a + b + c + d ∧ a + b + e < a + b + c + d ∧ a + c + d < a + b + c + d ∧ 2 * b + d < a + b + c + d ∧ b + 2 * c < a + b + c + d ∧ c + f < a + b + c + d ∧ d + e < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_358
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c + g < a + b + f)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_359
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_360
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_361
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_362
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_363
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_364
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_365
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_366
    {a b c d e f : ℕ}
    (h0 : 2 * a + d < a + b + c + d)
    (h1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 2 * a + d < a + b + c + d ∧ a + b + c < a + b + c + d ∧ 3 * b < a + b + c + d ∧ a + f < a + b + c + d ∧ b + e < a + b + c + d ∧ c + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_367
    {a b c d f g : ℕ}
    (h0 : 5 * a ≤ b + g)
    (h1 : b + f = 2 * d)
    (h2 : c + g < a + b + f)
    (h3 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_368
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ c + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_369
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_370
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_371
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_372
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_373
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a + b + c < 2 * a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : c + g < a + b + f)
    (h6 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_374
    {a b c d f g : ℕ}
    (h0 : 4 * a ≤ b + g)
    (h1 : b + f = 2 * d)
    (h2 : c + g < a + b + f)
    (h3 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_375
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ c + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_376
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_377
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_378
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_379
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_380
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a + b + c < 2 * a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_381
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ b + g)
    (h1 : b + f = 2 * d)
    (h2 : c + g < a + b + f)
    (h3 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_382
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ c + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_383
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_384
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_385
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_386
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_387
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_388
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_389
    {a b c d e f : ℕ}
    (h0 : 2 * a + b + c < 2 * a + 4 * b)
    (h1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_390
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_391
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b + d < (a + b + c + d) ∧ 2 * b + c < (a + b + c + d) ∧ b + f < (a + b + c + d) ∧ 2 * d < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_392
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_393
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_394
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_395
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_396
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ e + f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : e < 3 * a)
    (h5 : e = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_397
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e < 3 * a)
    (h6 : e = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_398
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_399
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ e + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    (h6 : e = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_400
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    (h6 : e = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_401
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_402
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ e + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    (h6 : e = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_403
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    (h6 : e = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_404
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : e < 3 * a)
    (h5 : e = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_405
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_406
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : e = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_407
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_408
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    (h6 : e = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_409
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    (h3 : e = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_410
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_411
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : e = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_412
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e < 3 * a)
    (h6 : e = 0)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_413
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_414
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e < 3 * a)
    (h6 : e = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_415
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_416
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    (h6 : e = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_417
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e < 3 * a)
    (h6 : e = 0)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_418
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + d < a + b + c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    : 4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 3 * a + f < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + c + f < a + b + c + d ∧ 2 * b + f < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d ∧ d + g < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_419
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e < 3 * a)
    (h6 : e = 0)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_420
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + d < a + b + c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d ∧ 2 * a + b + c < a + b + c + d ∧ a + 3 * b < a + b + c + d ∧ 2 * a + f < a + b + c + d ∧ a + c + d < a + b + c + d ∧ 2 * b + d < a + b + c + d ∧ b + 2 * c < a + b + c + d ∧ c + f < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_421
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    (h6 : e = 0)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_422
    {a b c d f : ℕ}
    (h0 : 2 * a + d < a + b + c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d ∧ a + b + c < a + b + c + d ∧ 3 * b < a + b + c + d ∧ a + f < a + b + c + d ∧ c + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_423
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e < 3 * a)
    (h6 : e = 0)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_424
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_425
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e < 3 * a)
    (h6 : e = 0)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_426
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_427
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c + g < a + b + f)
    (h5 : d < a + b)
    (h6 : e = 0)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat106_428
    {a b c d f : ℕ}
    (h0 : 2 * a + b + c < 2 * a + 4 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDFG` / `BF·CF·DD·BBB·BBC·BCC·CCC` dies on power system `S07` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDFG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_278 hcq2 h hcq0 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_396 hcq2 h hcq1 hcq8 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat106_152 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_280 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_397 hcq2 h hcq0 hcq1 hcq8 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat106_155 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_156 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_282 hcq2 h hcq0 hcq1 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_398 hcq2 h hcq0 hcq1 hcq7 hcq8)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_284 hcq2 h hcq0 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_399 hcq2 h hcq0 hcq1 hcq7 hcq8 hEn)
      · exact Or.inr (by exact astra4wPowerNat106_160 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_286 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_400 hcq2 h hcq0 hcq1 hcq7 hcq8 hEn)
      · exact Or.inr (by exact astra4wPowerNat106_163 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_164 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_288 hcq2 h hcq0 hcq1 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_401 hcq2 h hcq0 hcq1 hcq7 hcq8)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_290 hcq2 h hcq0 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_402 hcq2 h hcq0 hcq1 hcq7 hcq8 hEn)
      · exact Or.inr (by exact astra4wPowerNat106_168 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_292 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_403 hcq2 h hcq0 hcq1 hcq7 hcq8 hEn)
      · exact Or.inr (by exact astra4wPowerNat106_171 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_172 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_294 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_404 hcq2 h hcq1 hcq8 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat106_296 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_297 hcq2 h hcq1 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_405 hcq2 h hcq0 hcq1 hcq8)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_299 hcq2 h hcq0 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_406 hcq2 h hcq1 hcq8 hEn)
      · exact Or.inr (by exact astra4wPowerNat106_178 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_301 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_407 hcq2 h hcq0 hcq1 hcq8 hEn)
      · exact Or.inr (by exact astra4wPowerNat106_181 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_182 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_303 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_408 hcq2 h hcq0 hcq1 hcq7 hcq8 hEn)
      · exact Or.inr (by exact astra4wPowerNat106_305 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_306 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_307 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_308 hcq2 h hcq0 hcq1 hcq8)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_309 h hcq2 hcq0 hcq1 hcq8)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_310 h hcq2 hcq0 hcq7 hcq8)
    · exact Or.inr (by exact astra4wPowerNat106_409 h hcq1 hcq8 hEn)
    · exact Or.inr (by exact astra4wPowerNat106_188 h hcq8)
    · exact Or.inr (by exact astra4wPowerNat106_312 h hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat106_410 h hcq2 hcq0 hcq1 hcq8 hEn)
    · exact Or.inr (by exact astra4wPowerNat106_191 h hcq8)
    · exact Or.inr (by exact astra4wPowerNat106_192 h hcq0 hcq8)
    · exact Or.inr (by exact astra4wPowerNat106_314 h hcq2 hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat106_411 h hcq2 hcq1 hcq8 hEn)
    · exact Or.inr (by exact astra4wPowerNat106_316 h hcq2 hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat106_317 h hcq2 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat106_318 h hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat106_319 h hcq2 hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat106_320 h hcq2 hcq1 hcq8)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by exact astra4wPowerNat106_131 hcq8) (by exact astra4wPowerNat106_223 hcq2 hcq0 hcq7) hz0l hz0beta (Or.inr (by exact astra4wPowerNat106_225 hcq2 hcq0 hcq1 hcq8)) hz0delta (Or.inr (by exact astra4wPowerNat106_226 hcq8)) hz0zeta (Or.inr (by exact astra4wPowerNat106_227 hcq2 hcq1 hcq8)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top_S07 hAne hBne hCne hFne (D := D) (E := E) (G := G) (by exact astra4wPowerNat106_002 hcq0) (by exact astra4wPowerNat106_228 hcq2 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_321 h hcq0 hcq1 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_322 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_412 hcq2 h hcq0 hcq1 hcq8 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat106_324 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_325 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_326 hcq2 h hcq0 hcq1 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_413 hcq2 h hcq0 hcq1 hcq7 hcq8)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_328 h hcq0 hcq1 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_329 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_414 hcq2 h hcq0 hcq1 hcq8 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat106_331 hcq2 hcq0 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_332 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_333 hcq2 h hcq0 hcq1 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_415 hcq2 h hcq0 hcq1 hcq8)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_335 h hcq0 hcq1 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_336 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_416 hcq2 h hcq0 hcq1 hcq7 hcq8 hEn)
      · exact Or.inr (by exact astra4wPowerNat106_338 h hcq2 hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_339 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_340 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_341 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_342 hcq2 h hcq0 hcq1 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_343 h hcq2 hcq0 hcq1 hcq8)
  have hr1 : (muQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest14810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz (by exact astra4wPowerNat106_229 hcq2 hcq0 hcq1 hcq8) (by exact astra4wPowerNat106_136 hcq8) (by exact astra4wPowerNat106_231 hcq2 hcq0 hcq7) (by exact astra4wPowerNat106_232 hcq2 hcq0 hcq8) hz1l hz1beta (Or.inr (by exact astra4wPowerNat106_234 hcq2 hcq0 hcq1 hcq7 hcq8)) hz1delta (Or.inr (by exact astra4wPowerNat106_390 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat106_236 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat106_237 hcq2 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat106_238 hcq2 hcq0 hcq1 hcq8))
  have hct1 := muQuarticChamberFace14810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat106_239 hcq2 hcq0) (by exact astra4wPowerNat106_240 hcq2 hcq0 hcq1) (by exact astra4wPowerNat106_012 hcq0)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_344 h hcq0 hcq1 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_345 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_417 hcq2 h hcq0 hcq1 hcq8 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat106_347 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_348 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_349 hcq2 h hcq0 hcq1 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_418 hcq2 h hcq0 hcq1 hcq7 hcq8)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_351 h hcq0 hcq1 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_352 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_419 hcq2 h hcq0 hcq1 hcq8 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat106_354 hcq2 hcq0 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_355 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_356 hcq2 h hcq0 hcq1 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_420 hcq2 h hcq0 hcq1 hcq8)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_358 h hcq0 hcq1 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_359 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_421 hcq2 h hcq0 hcq1 hcq7 hcq8 hEn)
      · exact Or.inr (by exact astra4wPowerNat106_361 h hcq2 hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_362 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_363 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_364 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_365 hcq2 h hcq0 hcq1 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_422 h hcq2 hcq0 hcq1 hcq8)
  have hr2 : (xiQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest14810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hEz (by exact astra4wPowerNat106_241 hcq2 hcq0 hcq1 hcq8) (by exact astra4wPowerNat106_243 hcq2 hcq0 hcq1 hcq8) (by exact astra4wPowerNat106_244 hcq2 hcq0 hcq1 hcq8) (by exact astra4wPowerNat106_245 hcq0 hcq1 hcq7 hcq8) (by exact astra4wPowerNat106_246 hcq1 hcq8) (by exact astra4wPowerNat106_249 hcq8) (by exact astra4wPowerNat106_251 hcq2 hcq0 hcq1 hcq8) hz2l hz2beta (Or.inr (by exact astra4wPowerNat106_391 hcq2 hcq0 hcq1 hcq8)) hz2delta (Or.inr (by exact astra4wPowerNat106_253 hcq2 hcq0 hcq1 hcq7 hcq8)) (Or.inr (by exact astra4wPowerNat106_254 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat106_392 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat106_256 hcq2 hcq0 hcq1 hcq8))
  have hct2 := xiQuarticChamberFace14810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat106_257 hcq2 hcq0)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_367 h hcq1 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_368 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_423 hcq2 h hcq0 hcq1 hcq8 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat106_370 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_371 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_372 hcq2 h hcq0 hcq1 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_424 hcq2 h hcq0 hcq1 hcq7 hcq8)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_374 h hcq1 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_375 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_425 hcq2 h hcq0 hcq1 hcq8 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat106_377 hcq2 hcq0 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_378 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_379 hcq2 h hcq0 hcq1 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_426 hcq2 h hcq0 hcq1 hcq8)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_381 h hcq1 hcq7 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_382 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_427 hcq2 h hcq0 hcq1 hcq7 hcq8 hEn)
      · exact Or.inr (by exact astra4wPowerNat106_384 h hcq2 hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_385 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_386 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_387 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat106_388 hcq2 h hcq0 hcq1 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_428 h hcq2 hcq0 hcq1 hcq8)
  have hr3 : (piQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest7810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hEz (by exact astra4wPowerNat106_141 hcq8) (by exact astra4wPowerNat106_258 hcq2 hcq0 hcq1 hcq8) (by exact astra4wPowerNat106_259 hcq2 hcq0 hcq7) (by exact astra4wPowerNat106_261 hcq1 hcq8) (by exact astra4wPowerNat106_143 hcq8) (by exact astra4wPowerNat106_144 hcq0 hcq8) (by exact astra4wPowerNat106_263 hcq2 hcq0 hcq7 hcq8) (by exact astra4wPowerNat106_265 hcq2 hcq0 hcq7) (by exact astra4wPowerNat106_266 hcq2 hcq0 hcq8) (by exact astra4wPowerNat106_269 hcq2 hcq0 hcq7) hz3l hz3beta (Or.inr (by exact astra4wPowerNat106_393 hcq2 hcq0 hcq1 hcq8)) hz3delta (Or.inr (by exact astra4wPowerNat106_394 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat106_395 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat106_273 hcq2 hcq0 hcq1 hcq7 hcq8)) (Or.inr (by exact astra4wPowerNat106_274 hcq2 hcq0 hcq1 hcq8))
  have hct3 := piQuarticChamberFace7810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat106_022 hcq0) (by exact astra4wPowerNat106_275 hcq2 hcq0) (by exact astra4wPowerNat106_276 hcq2 hcq0 hcq1) (by exact astra4wPowerNat106_024 hcq0) (by exact astra4wPowerNat106_277 hcq2)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : piQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact quarticPowerInnerS07810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hAc hBc hCc hDc hFc


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
/-- Chamber `BCDEFG` / `BF·CF·DD·BBB·BBC·BCC·CCC` dies on power system `S07` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEFG31810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG31810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
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
      · exact Or.inr (by exact astra4wPowerNat106_278 hcq2 h hcq0 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_279 hcq8 hcq2 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_152 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_280 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_281 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_155 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_156 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_282 hcq2 h hcq0 hcq1 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_283 hcq8 hcq2 h hcq0 hcq1 hcq7 hcq9)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_284 hcq2 h hcq0 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_285 hcq8 hcq2 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_160 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_286 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_287 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_163 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_164 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_288 hcq2 h hcq0 hcq1 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_289 hcq8 hcq2 h hcq0 hcq1 hcq7 hcq9)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_290 hcq2 h hcq0 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_291 hcq8 hcq2 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_168 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_292 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_293 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_171 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_172 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_294 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_295 hcq8 hcq2 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_296 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_297 hcq2 h hcq1 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_298 hcq8 hcq2 h hcq0 hcq1 hcq9)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_299 hcq2 h hcq0 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_300 hcq8 hcq2 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_178 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_301 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_302 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_181 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_182 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_303 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_304 hcq8 hcq2 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_305 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_306 hcq2 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_307 hcq2 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_308 hcq2 h hcq0 hcq1 hcq9)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_309 h hcq2 hcq0 hcq1 hcq9)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_310 h hcq2 hcq0 hcq7 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_311 h hcq8 hcq2 hcq1 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_188 h hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_312 h hcq1 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_313 h hcq8 hcq0 hcq1 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_191 h hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_192 h hcq0 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_314 h hcq2 hcq0 hcq1 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_315 h hcq8 hcq2 hcq1 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_316 h hcq2 hcq0 hcq1 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_317 h hcq2 hcq1 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_318 h hcq1 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_319 h hcq2 hcq0 hcq1 hcq9)
    · exact Or.inr (by exact astra4wPowerNat106_320 h hcq2 hcq1 hcq9)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat106_131 hcq9) (by exact astra4wPowerNat106_223 hcq2 hcq0 hcq7) (by exact astra4wPowerNat106_224 hcq8 hcq2) hz0l hz0beta (Or.inr (by exact astra4wPowerNat106_225 hcq2 hcq0 hcq1 hcq9)) hz0delta (Or.inr (by exact astra4wPowerNat106_226 hcq9)) hz0zeta (Or.inr (by exact astra4wPowerNat106_227 hcq2 hcq1 hcq9)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top_S07 hAne hBne hCne hFne (D := D) (E := E) (G := G) (by exact astra4wPowerNat106_002 hcq0) (by exact astra4wPowerNat106_228 hcq2 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_321 h hcq0 hcq1 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_322 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_323 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_324 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_325 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_326 hcq2 h hcq0 hcq1 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_327 hcq8 hcq2 h hcq0 hcq1 hcq7 hcq9)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_328 h hcq0 hcq1 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_329 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_330 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_331 hcq2 hcq0 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_332 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_333 hcq2 h hcq0 hcq1 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_334 hcq8 hcq2 h hcq0 hcq1 hcq9)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_335 h hcq0 hcq1 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_336 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_337 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_338 h hcq2 hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_339 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_340 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_341 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_342 hcq2 h hcq0 hcq1 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_343 h hcq2 hcq0 hcq1 hcq9)
  have hr1 : (muQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest14810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat106_229 hcq2 hcq0 hcq1 hcq9) (by exact astra4wPowerNat106_230 hcq8 hcq0 hcq1 hcq9) (by exact astra4wPowerNat106_136 hcq9) (by exact astra4wPowerNat106_231 hcq2 hcq0 hcq7) (by exact astra4wPowerNat106_232 hcq2 hcq0 hcq9) (by exact astra4wPowerNat106_233 hcq8 hcq2 hcq0 hcq1) hz1l hz1beta (Or.inr (by exact astra4wPowerNat106_234 hcq2 hcq0 hcq1 hcq7 hcq9)) hz1delta (Or.inr (by exact astra4wPowerNat106_235 hcq8 hcq2 hcq0 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat106_236 hcq2 hcq0 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat106_237 hcq2 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat106_238 hcq2 hcq0 hcq1 hcq9))
  have hct1 := muQuarticChamberFace14810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat106_239 hcq2 hcq0) (by exact astra4wPowerNat106_240 hcq2 hcq0 hcq1) (by exact astra4wPowerNat106_012 hcq0)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_344 h hcq0 hcq1 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_345 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_346 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_347 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_348 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_349 hcq2 h hcq0 hcq1 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_350 hcq8 hcq2 h hcq0 hcq1 hcq7 hcq9)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_351 h hcq0 hcq1 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_352 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_353 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_354 hcq2 hcq0 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_355 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_356 hcq2 h hcq0 hcq1 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_357 hcq8 hcq2 h hcq0 hcq1 hcq9)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_358 h hcq0 hcq1 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_359 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_360 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_361 h hcq2 hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_362 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_363 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_364 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_365 hcq2 h hcq0 hcq1 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_366 h hcq8 hcq2 hcq0 hcq1 hcq9)
  have hr2 : (xiQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest14810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by exact astra4wPowerNat106_241 hcq2 hcq0 hcq1 hcq9) (by exact astra4wPowerNat106_242 hcq8 hcq0 hcq1) (by exact astra4wPowerNat106_243 hcq2 hcq0 hcq1 hcq9) (by exact astra4wPowerNat106_244 hcq2 hcq0 hcq1 hcq9) (by exact astra4wPowerNat106_245 hcq0 hcq1 hcq7 hcq9) (by exact astra4wPowerNat106_246 hcq1 hcq9) (by exact astra4wPowerNat106_247 hcq8 hcq0 hcq1 hcq9) (by exact astra4wPowerNat106_248 hcq8 hcq0 hcq1) (by exact astra4wPowerNat106_249 hcq9) (by exact astra4wPowerNat106_250 hcq8 hcq2 hcq0 hcq1 hcq7) (by exact astra4wPowerNat106_251 hcq2 hcq0 hcq1 hcq9) hz2l hz2beta (Or.inr (by exact astra4wPowerNat106_252 hcq8 hcq2 hcq0 hcq1 hcq9)) hz2delta (Or.inr (by exact astra4wPowerNat106_253 hcq2 hcq0 hcq1 hcq7 hcq9)) (Or.inr (by exact astra4wPowerNat106_254 hcq2 hcq0 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat106_255 hcq8 hcq2 hcq0 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat106_256 hcq2 hcq0 hcq1 hcq9))
  have hct2 := xiQuarticChamberFace14810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat106_257 hcq2 hcq0)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_367 h hcq1 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_368 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_369 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_370 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_371 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_372 hcq2 h hcq0 hcq1 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_373 hcq8 hcq2 h hcq0 hcq1 hcq7 hcq9)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_374 h hcq1 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_375 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_376 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_377 hcq2 hcq0 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_378 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_379 hcq2 h hcq0 hcq1 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_380 hcq8 hcq2 h hcq0 hcq1 hcq9)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_381 h hcq1 hcq7 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_382 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_383 hcq8 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_384 h hcq2 hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_385 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_386 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_387 hcq2 h hcq0 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat106_388 hcq2 h hcq0 hcq1 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_389 h hcq8 hcq2 hcq0 hcq1 hcq9)
  have hr3 : (piQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest7810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 (by exact astra4wPowerNat106_141 hcq9) (by exact astra4wPowerNat106_258 hcq2 hcq0 hcq1 hcq9) (by exact astra4wPowerNat106_259 hcq2 hcq0 hcq7) (by exact astra4wPowerNat106_260 hcq8 hcq2) (by exact astra4wPowerNat106_261 hcq1 hcq9) (by exact astra4wPowerNat106_262 hcq8 hcq0 hcq1 hcq9) (by exact astra4wPowerNat106_143 hcq9) (by exact astra4wPowerNat106_144 hcq0 hcq9) (by exact astra4wPowerNat106_263 hcq2 hcq0 hcq7 hcq9) (by exact astra4wPowerNat106_264 hcq8 hcq2 hcq1 hcq9) (by exact astra4wPowerNat106_265 hcq2 hcq0 hcq7) (by exact astra4wPowerNat106_266 hcq2 hcq0 hcq9) (by exact astra4wPowerNat106_267 hcq8 hcq2 hcq0 hcq1) (by exact astra4wPowerNat106_268 hcq8 hcq2 hcq9) (by exact astra4wPowerNat106_269 hcq2 hcq0 hcq7) hz3l hz3beta (Or.inr (by exact astra4wPowerNat106_270 hcq8 hcq2 hcq0 hcq1 hcq9)) hz3delta (Or.inr (by exact astra4wPowerNat106_271 hcq8 hcq2 hcq0 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat106_272 hcq8 hcq2 hcq0 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat106_273 hcq2 hcq0 hcq1 hcq7 hcq9)) (Or.inr (by exact astra4wPowerNat106_274 hcq2 hcq0 hcq1 hcq9))
  have hct3 := piQuarticChamberFace7810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat106_022 hcq0) (by exact astra4wPowerNat106_275 hcq2 hcq0) (by exact astra4wPowerNat106_276 hcq2 hcq0 hcq1) (by exact astra4wPowerNat106_024 hcq0) (by exact astra4wPowerNat106_277 hcq2)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : piQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact quarticPowerInnerS07810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hAc hBc hCc hDc hFc


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
/-- Chamber `BCDG` / `BG·CG·BBB·BBC·BCC·CCC` dies on power system `S08` (carriers κ, μ, π). -/
theorem quarticChamberBCDG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_150 h hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_151 hAF hcq7 h hcq6 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_152 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_153 hcq7 h hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_154 hcq7 h hcq0 hcq6 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_155 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_156 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_034 hcq7 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_157 hcq7 h hcq0 hcq6 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_158 h hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_159 hAF hcq7 h hcq6 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_160 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_161 hcq7 h hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_162 hcq7 h hcq0 hcq6 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_163 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_164 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_043 hcq7 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_165 hcq7 h hcq0 hcq6 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_166 h hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_167 hAF hcq7 h hcq6 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_168 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_169 hcq7 h hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_170 hcq7 h hcq0 hcq6 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_171 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_172 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_052 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_173 hcq7 h hAE hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_174 hcq7 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_055 hcq7 h hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_175 hApos hcq7 h hcq0 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_176 h hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_177 hcq7 h hcq6 hEn hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_178 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_179 hcq7 h hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_180 hcq7 h hcq0 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_181 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_182 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat106_064 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_183 hcq7 h hcq6 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_184 hcq7 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_067 hcq7 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_185 hcq7 h hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_069 hcq7 h hcq0 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_070 hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_186 h hcq6 hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_187 h hcq7 hcq6 hEn hFn hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_188 h hcq6)
    · exact Or.inr (by exact astra4wPowerNat106_189 h hcq7 hFn hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_190 hApos h hcq0 hEn)
    · exact Or.inr (by exact astra4wPowerNat106_191 h hcq6)
    · exact Or.inr (by exact astra4wPowerNat106_192 h hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat106_078 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat106_193 h hcq7 hcq6 hEn hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_194 hApos h hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat106_081 hApos h)
    · exact Or.inr (by exact astra4wPowerNat106_195 h hcq7 hcq6 hFn hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_083 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat106_196 h hcq7 hcq6 hcq1)
  have hr0 : (kappaQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz hFz (by exact astra4wPowerNat106_131 hcq6) hz0l hz0beta (Or.inr (by exact astra4wPowerNat106_132 hcq0 hcq5 hcq6 hcq1)) hz0delta (Or.inr (by exact astra4wPowerNat106_133 hApos hcq5 hcq1)) hz0zeta (Or.inr (by exact astra4wPowerNat106_134 hcq5 hcq6 hcq1)) hz0theta
  have hct0 := kappaQuarticChamberFace9810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat106_002 hcq0) (by exact astra4wPowerNat106_003 hcq1)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face9_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS08810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_085 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_197 hcq7 h hcq0 hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_198 hcq7 h hcq0 hcq6 hAE hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_088 hcq7 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_199 hcq7 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_090 hcq7 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_200 hcq7 h hcq0 hcq6 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_092 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_201 hcq7 h hcq0 hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_202 hcq7 h hcq0 hcq6 hAE hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_095 hcq7 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_203 hcq7 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_097 hcq7 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_204 hcq7 h hcq0 hcq6 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_099 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_205 hcq7 h hcq0 hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_206 hcq7 h hcq0 hcq6 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_102 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_207 hcq7 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_104 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_208 hcq7 h hcq0 hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_106 hcq7 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_209 hApos h hcq0 hcq6)
  have hr1 : (muQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest10810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz hFz (by exact astra4wPowerNat106_004 hcq7 hcq0 hcq1) (by exact astra4wPowerNat106_135 hcq0 hcq5 hcq1) (by exact astra4wPowerNat106_136 hcq6) hz1l hz1beta (Or.inr (by exact astra4wPowerNat106_137 hApos hcq0 hcq5 hcq6 hcq1)) hz1delta (Or.inr (by exact astra4wPowerNat106_138 hApos hcq0)) (Or.inr (by exact astra4wPowerNat106_139 hApos hcq0 hcq5 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat106_140 hcq5 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat106_011 hApos hcq0))
  have hct1 := muQuarticChamberFace10810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat106_012 hcq0) (by exact astra4wPowerNat106_013 hcq1)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face10_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS08810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_108 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_210 hcq7 h hcq0 hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_211 hcq7 h hcq0 hcq6 hAE hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_111 hcq7 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_212 hcq7 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_113 hcq7 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_213 hcq7 h hcq0 hcq6 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_115 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_214 hcq7 h hcq0 hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_215 hcq7 h hcq0 hcq6 hAE hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_118 hcq7 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_216 hcq7 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_120 hcq7 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_217 hcq7 h hcq0 hcq6 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_122 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_218 hcq7 h hcq0 hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_219 hcq7 h hcq0 hcq6 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_125 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_220 hcq7 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_127 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_221 hcq7 h hcq0 hcq6 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_129 hcq7 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_222 hApos h hcq0 hcq6)
  have hr2 : (piQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest8810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hEz hFz (by exact astra4wPowerNat106_141 hcq6) (by exact astra4wPowerNat106_014 hcq7 hcq0 hcq1) (by exact astra4wPowerNat106_142 hcq0 hcq5 hcq1) (by exact astra4wPowerNat106_143 hcq6) (by exact astra4wPowerNat106_144 hcq0 hcq6) (by exact astra4wPowerNat106_145 hcq6 hcq1) hz2l hz2beta (Or.inr (by exact astra4wPowerNat106_146 hApos hcq0 hcq5 hcq6 hcq1)) hz2delta (Or.inr (by exact astra4wPowerNat106_147 hApos hcq0 hcq5 hcq1)) (Or.inr (by exact astra4wPowerNat106_148 hApos hcq0 hcq5 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat106_149 hApos hcq0 hcq5 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat106_021 hApos hcq0))
  have hct2 := piQuarticChamberFace8810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat106_022 hcq0) (by exact astra4wPowerNat106_023 hcq1) (by exact astra4wPowerNat106_024 hcq0) (by exact astra4wPowerNat106_025 hcq0 hcq1) (by exact astra4wPowerNat106_026 hcq1)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face8_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticPowerInnerS08810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact quarticPowerInnerS08810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hCc


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
/-- Chamber `BCEG` / `BG·CG·BBB·BBC·BCC·CCC` dies on power system `S08` (carriers κ, μ, π). -/
theorem quarticChamberBCEG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
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
      · exact Or.inr (by exact astra4wPowerNat106_027 hAD hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_028 hcq6 hAF hcq7 h hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_029 hAD hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_030 hAF hcq7 h hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_031 h hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_032 hAD hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_033 hAD hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_034 hcq7 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_035 hcq7 h hcq0 hcq9 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_036 hAD hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_037 hcq6 hAF hcq7 h hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_038 hAD hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_039 hAF hcq7 h hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_040 h hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_041 hcq6 hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_042 hAD hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_043 hcq7 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_044 hcq7 h hcq0 hcq9 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_045 hAD hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_046 hcq6 hcq7 h hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_047 hAD hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_048 hAF hcq7 h hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_049 h hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_050 hcq6 hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_051 hAD hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_052 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_053 hcq7 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_054 hAD hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_055 hcq7 h hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_056 hApos hcq7 h hcq0 hcq9 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_057 hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_058 hcq6 hcq7 h hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_059 h hcq7 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_060 hcq6 hcq7 h hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_061 h hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_062 hcq6 hcq7 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_063 hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_064 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_065 hcq7 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_066 hcq6 hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_067 hcq7 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_068 hcq6 hcq7 h hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_069 hcq7 h hcq0 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_070 hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_071 hApos h hDn hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_072 h hcq7 hcq0 hcq9 hFn hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_073 hApos h hDn)
    · exact Or.inr (by exact astra4wPowerNat106_074 hApos h hFn)
    · exact Or.inr (by exact astra4wPowerNat106_075 h hcq9 hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_076 hApos h hcq7 hDn hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_077 hApos h hcq0 hDn)
    · exact Or.inr (by exact astra4wPowerNat106_078 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat106_079 hApos h hcq0 hcq9 hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_080 hApos h hcq7 hcq0 hDn hcq1)
    · exact Or.inr (by exact astra4wPowerNat106_081 hApos h)
    · exact Or.inr (by exact astra4wPowerNat106_082 hApos h hFn)
    · exact Or.inr (by exact astra4wPowerNat106_083 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat106_084 hApos h hDn)
  have hr0 : (kappaQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hFz hz0l hz0beta (Or.inr (by exact astra4wPowerNat106_000 hApos hcq0)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat106_001 hApos)) hz0theta
  have hct0 := kappaQuarticChamberFace9810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat106_002 hcq0) (by exact astra4wPowerNat106_003 hcq1)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face9_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS08810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_085 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_086 hAF hcq7 h hcq0 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_087 hAD hcq6 hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_088 hcq7 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_089 hAD hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_090 hcq7 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_091 hcq7 h hcq0 hcq9 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_092 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_093 hcq6 hcq7 h hcq0 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_094 hAD hcq6 hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_095 hcq7 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_096 hAD hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_097 hcq7 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_098 hcq7 h hcq0 hcq9 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_099 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_100 hcq6 hcq7 h hcq0 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_101 hcq6 hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_102 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_103 hAD hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_104 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_105 hcq6 hcq7 h hcq0 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_106 hcq7 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_107 hApos h hcq0)
  have hr1 : (muQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest10810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hFz (by exact astra4wPowerNat106_004 hcq7 hcq0 hcq1) (by exact astra4wPowerNat106_005 hcq0 hcq9 hcq1) (by exact astra4wPowerNat106_006 hcq5 hcq0 hcq1) hz1l hz1beta (Or.inr (by exact astra4wPowerNat106_007 hApos hcq0 hcq1)) hz1delta (Or.inr (by exact astra4wPowerNat106_008 hApos hcq0 hcq9 hcq1)) (Or.inr (by exact astra4wPowerNat106_009 hApos hcq0)) (Or.inr (by exact astra4wPowerNat106_010 hApos)) (Or.inr (by exact astra4wPowerNat106_011 hApos hcq0))
  have hct1 := muQuarticChamberFace10810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat106_012 hcq0) (by exact astra4wPowerNat106_013 hcq1)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face10_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS08810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_108 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_109 hAF hcq7 h hcq0 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_110 hAD hcq6 hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_111 hcq7 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_112 hAD hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_113 hcq7 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_114 hcq7 h hcq0 hcq9 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_115 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_116 hcq6 hcq7 h hcq0 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_117 hAD hcq6 hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_118 hcq7 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_119 hAD hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_120 hcq7 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_121 hcq7 h hcq0 hcq9 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat106_122 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_123 hcq6 hcq7 h hcq0 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_124 hcq6 hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_125 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_126 hAD hcq7 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_127 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat106_128 hcq6 hcq7 h hcq0 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat106_129 hcq7 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat106_130 hApos h hcq0 hcq9 hcq1)
  have hr2 : (piQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest8810_natDegree_lt_of_live_BCEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz hFz (by exact astra4wPowerNat106_014 hcq7 hcq0 hcq1) (by exact astra4wPowerNat106_015 hcq9 hcq1) (by exact astra4wPowerNat106_016 hcq5 hcq0 hcq1) hz2l hz2beta (Or.inr (by exact astra4wPowerNat106_017 hApos hcq5 hcq0 hcq9 hcq1)) hz2delta (Or.inr (by exact astra4wPowerNat106_018 hApos hcq0 hcq9 hcq1)) (Or.inr (by exact astra4wPowerNat106_019 hApos hcq5 hcq0 hcq1)) (Or.inr (by exact astra4wPowerNat106_020 hApos hcq0 hcq1)) (Or.inr (by exact astra4wPowerNat106_021 hApos hcq0))
  have hct2 := piQuarticChamberFace8810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat106_022 hcq0) (by exact astra4wPowerNat106_023 hcq1) (by exact astra4wPowerNat106_024 hcq0) (by exact astra4wPowerNat106_025 hcq0 hcq1) (by exact astra4wPowerNat106_026 hcq1)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face8_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticPowerInnerS08810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact quarticPowerInnerS08810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hCc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
