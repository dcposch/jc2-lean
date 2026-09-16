import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
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
private theorem astra4wPowerNat111_000
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_001
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_002
    {a b d : ℕ}
    (h0 : d < a + b)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_003
    {a b d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_004
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : b + g = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_005
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : g = a + 2 * b)
    : d + e = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_006
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_007
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_008
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : b + g = d + e)
    (h3 : g = a + 2 * b)
    : a + d + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_009
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_010
    {a b d e : ℕ}
    (h0 : d < a + b)
    : b + d + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_011
    {a b d e f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_012
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + b + d < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_013
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_014
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + d < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_015
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_016
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_017
    {a b e g : ℕ}
    (h0 : g = a + 2 * b)
    : e + g = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_018
    {a b d : ℕ}
    (h0 : d < a + b)
    : a + 3 * b + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_019
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : d < a + b)
    : 3 * b + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_020
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_021
    {a b f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : g = a + 2 * b)
    : a + 2 * f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_022
    {a b d g : ℕ}
    (h0 : d < a + b)
    (h1 : g = a + 2 * b)
    : b + d + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_023
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : b + e + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_024
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 2 * d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_025
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_026
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : d < a + b)
    : a + b + d < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_027
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_028
    {a b d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_029
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : d < a + b)
    : f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_030
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : a + 2 * b + g = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_031
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : g = a + 2 * b)
    : a + b + d + e = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_032
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : 2 * g = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_033
    {a b d g : ℕ}
    (h0 : 6 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_034
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 6 * a ≤ e + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_035
    {a b d : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_036
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 6 * a ≤ 2 * b + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_037
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 6 * a ≤ b + c + e)
    (h2 : b + g = d + e)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_038
    {a b d : ℕ}
    (h0 : 6 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_039
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 6 * a ≤ 2 * c + d)
    (h2 : c < 2 * a)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_040
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 6 * a ≤ 3 * b + c)
    (h2 : c < 2 * a)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_041
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_042
    {a b d g : ℕ}
    (h0 : 5 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_043
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a ≤ e + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_044
    {a b d : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_045
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a ≤ 2 * b + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_046
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a ≤ b + c + e)
    (h2 : b + g = d + e)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_047
    {a b d : ℕ}
    (h0 : 5 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_048
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : c < 2 * a)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_049
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a ≤ 3 * b + c)
    (h2 : c < 2 * a)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_050
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a < a + 3 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_051
    {a b d g : ℕ}
    (h0 : 4 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_052
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ e + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_053
    {a b d : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_054
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_055
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : b + g = d + e)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_056
    {a b d : ℕ}
    (h0 : 4 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_057
    {a b c d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * d + 2 * f < a + 2 * b + 2 * g)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_058
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : c = 0)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_059
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ b + e)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_060
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ c + d)
    (h2 : c < 2 * a)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_061
    {a b d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_062
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a < a + 3 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_063
    {a b d g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_064
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ e + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_065
    {a b d : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_066
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_067
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : b + g = d + e)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_068
    {a b d : ℕ}
    (h0 : 3 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_069
    {a b c d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * d + 2 * f < a + 2 * b + 2 * g)
    (h2 : 3 * a ≤ 2 * c + d)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_070
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : c = 0)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_071
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ b + e)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_072
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ c + d)
    (h2 : c < 2 * a)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_073
    {a b d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a ≤ b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_074
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_075
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ b + c)
    (h2 : c < 2 * a)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_076
    {a b d g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_077
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_078
    {a b d : ℕ}
    (h0 : a ≤ 2 * b + d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_079
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_080
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : b + g = d + e)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_081
    {a b d : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_082
    {a b c d g : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : c = 0)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_083
    {a b c d g : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : c = 0)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_084
    {a b d e g : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_085
    {a b c d g : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : c = 0)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_086
    {a b d g : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_087
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_088
    {a b c d g : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : c < 2 * a)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_089
    {a b d g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_090
    {a b d e g : ℕ}
    (h0 : 5 * a ≤ b + g)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_091
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * d + 2 * f < a + 2 * b + 2 * g)
    (h2 : 5 * a ≤ c + f)
    (h3 : b + g = d + e)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : d < a + b)
    (h7 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_092
    {a b d e : ℕ}
    (h0 : 5 * a ≤ d + e)
    (h1 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_093
    {a b d e g : ℕ}
    (h0 : 4 * a ≤ 3 * b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_094
    {a b d e g : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_095
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : b + g = d + e)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_096
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a + d < a + 2 * b + e)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_097
    {a b d e g : ℕ}
    (h0 : 4 * a ≤ b + g)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_098
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * d + 2 * f < a + 2 * b + 2 * g)
    (h2 : 4 * a ≤ c + f)
    (h3 : b + g = d + e)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : d < a + b)
    (h7 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_099
    {a b d e : ℕ}
    (h0 : 4 * a ≤ d + e)
    (h1 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_100
    {a b d e g : ℕ}
    (h0 : a ≤ b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_101
    {a b d e g : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_102
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * d + 2 * f < a + 2 * b + 2 * g)
    (h2 : 4 * a ≤ b + 2 * c)
    (h3 : b + g = d + e)
    (h4 : c = 0)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_103
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a + d < a + 2 * b + e)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_104
    {a b d e g : ℕ}
    (h0 : 3 * a ≤ b + g)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_105
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : c = 0)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_106
    {a b d e : ℕ}
    (h0 : 3 * a ≤ d + e)
    (h1 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_107
    {a b d e g : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_108
    {a b d e g : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_109
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * d + 2 * f < a + 2 * b + 2 * g)
    (h2 : 3 * a ≤ b + 2 * c)
    (h3 : b + g = d + e)
    (h4 : c = 0)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_110
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_111
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ b + c)
    (h2 : b + g = d + e)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_112
    {a b d e f g : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_113
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a ≤ 4 * b)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_114
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : c = 0)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : ¬ (7 * a ≤ 4 * c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_115
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_116
    {a b d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_117
    {a b d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_118
    {a b d e f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_119
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_120
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ 4 * b)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_121
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : c = 0)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : ¬ (5 * a ≤ 4 * c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_122
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_123
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 9 * a ≤ 4 * e)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_124
    {a b d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_125
    {a b d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_126
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_127
    {a b f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a ≤ 4 * b)
    (h2 : g = a + 2 * b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_128
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : c = 0)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : ¬ (3 * a ≤ 4 * c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_129
    {a b d f g : ℕ}
    (h0 : 5 * a ≤ 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_130
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 7 * a ≤ 4 * e)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_131
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 9 * a ≤ 4 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_132
    {a b d f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_133
    {a b d e f g : ℕ}
    (h0 : 2 * a + f < 2 * a + 4 * b)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_134
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : b + 2 * c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_135
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : b + c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_136
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    : a + b + c + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_137
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_138
    {a b c e : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : 2 * c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_139
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_140
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_141
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_142
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_143
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : a + 2 * b + 2 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_144
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 4 * b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_145
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : g = a + 2 * b)
    : a + c + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_146
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : 2 * b + c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_147
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : d < a + b)
    : b + 2 * c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_148
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : 4 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_149
    {a b c g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : g = a + 2 * b)
    : 2 * c + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_150
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : g = a + 2 * b)
    : c + 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_151
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_152
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_153
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_154
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_155
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_156
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * f < 7 * a)
    (h2 : 6 * a ≤ e + f)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : f = 0)
    (h6 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_157
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * f < 7 * a)
    (h2 : 6 * a ≤ 2 * b + f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_158
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 6 * a ≤ b + c + e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_159
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 6 * a ≤ 2 * c + d)
    (h2 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_160
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 6 * a ≤ 3 * b + c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_161
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a < a + 3 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_162
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : f = 0)
    (h6 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_163
    {a b c d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a ≤ 2 * b + f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_164
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a ≤ b + c + e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_165
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_166
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a ≤ 3 * b + c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_167
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a < a + 3 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_168
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a ≤ e + f)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : f = 0)
    (h6 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_169
    {a b c d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a ≤ 2 * b + f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_170
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a ≤ b + c + e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_171
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_172
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a ≤ 3 * b + c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_173
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a ≤ c + d)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_174
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a < a + 3 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_175
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ e + f)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : f = 0)
    (h6 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_176
    {a b c d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ 2 * b + f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_177
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ b + c + e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_178
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_179
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ 3 * b + c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_180
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ c + d)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_181
    {a b c d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_182
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ b + c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_183
    {a b c d g : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_184
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_185
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_186
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_187
    {a b c d : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_188
    {a b c d g : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_189
    {a b c d g : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_190
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_191
    {a b c d g : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_192
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 2 * f < 7 * a)
    (h3 : 5 * a ≤ c + f)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : f = 0)
    (h7 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_193
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_194
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a + d < a + 2 * b + e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_195
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a ≤ c + f)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : f = 0)
    (h6 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_196
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_197
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a + d < a + 2 * b + e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_198
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ c + f)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : f = 0)
    (h6 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_199
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_200
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ f)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : f = 0)
    (h6 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_201
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ b + c)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_202
    {a b c d e g : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_203
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a ≤ 4 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_204
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 7 * a ≤ 4 * c)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_205
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 9 * a ≤ 4 * d)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_206
    {a b c d e g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_207
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : d < a + b)
    (h2 : f = 0)
    (h3 : g = a + 2 * b)
    : ¬ (13 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_208
    {a b c d e g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_209
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_210
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ 4 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_211
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a ≤ 4 * c)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_212
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 7 * a ≤ 4 * d)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_213
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 9 * a ≤ 4 * e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_214
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : d < a + b)
    (h2 : f = 0)
    (h3 : g = a + 2 * b)
    : ¬ (11 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_215
    {a b c d e g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_216
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_217
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a ≤ 4 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_218
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a ≤ 4 * c)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_219
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_220
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 7 * a ≤ 4 * e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_221
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : d < a + b)
    (h2 : f = 0)
    (h3 : g = a + 2 * b)
    : ¬ (9 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_222
    {a b c d g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_223
    {a b c d e g : ℕ}
    (h0 : 2 * a + b + c < 2 * a + 4 * b)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_224
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a + b + d < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_225
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_226
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_227
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a + 3 * b < (2 * a + 4 * b) ∧ a + b + e < (2 * a + 4 * b) ∧ 2 * b + d < (2 * a + 4 * b) ∧ d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_228
    {a b d : ℕ}
    (h0 : d < a + b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_229
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 3 * b < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_230
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a < a + 3 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + g < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_231
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * f < 7 * a)
    (h2 : 5 * a ≤ e + f)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : f = 0)
    (h6 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_232
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * f < 7 * a)
    (h2 : 5 * a ≤ 2 * b + f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_233
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ e + f)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_234
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * a ≤ 2 * b + f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_235
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : c = 0)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_236
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ e + f)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_237
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_238
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : c = 0)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_239
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_240
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * f < 7 * a)
    (h2 : 5 * a ≤ c + f)
    (h3 : b + g = d + e)
    (h4 : c = 0)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_241
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a + d < a + 2 * b + e)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ d + g < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_242
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * a ≤ c + f)
    (h3 : b + g = d + e)
    (h4 : c = 0)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_243
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : b + g = d + e)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_244
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a + d < a + 2 * b + e)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_245
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ c + f)
    (h2 : b + g = d + e)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : f = 0)
    (h6 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_246
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : b + g = d + e)
    (h3 : c = 0)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_247
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_248
    {a b d e g : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ b + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_249
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a ≤ 4 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : 3 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_250
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : 3 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_251
    {a b d e g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : 3 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_252
    {a b d e g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : 3 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_253
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a + b + e < 2 * a + 4 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_254
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ 4 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_255
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_256
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 9 * a ≤ 4 * e)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_257
    {a b d e g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_258
    {a b d e g : ℕ}
    (h0 : 2 * a + b + e < 2 * a + 4 * b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_259
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : b + 2 * c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_260
    {a b f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    : b + g < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_261
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : c + f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_262
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_263
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_264
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_265
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    : d + e = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_266
    {a b c f : ℕ}
    (h0 : b + c < f)
    : a + 2 * b + c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_267
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_268
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b + e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_269
    {a b c d f : ℕ}
    (h0 : b + c < f)
    (h1 : d < a + b)
    : b + c + d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_270
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : 3 * c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_271
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : b + c < f)
    : c + g < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_272
    {a b d f : ℕ}
    (h0 : d < a + b)
    : d + f < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_273
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : a + 2 * b < (a + b + f) ∧ b + d < (a + b + f) ∧ 2 * c < (a + b + f) ∧ g < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_274
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * b < (a + b + f) ∧ e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_275
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b < (a + b + f) ∧ d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_276
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_277
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_278
    {a b d f : ℕ}
    (h0 : b + f = 2 * d)
    : a + 2 * d = a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_279
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_280
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    : a + b + c + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_281
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_282
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_283
    {a b d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_284
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_285
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : 2 * c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_286
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_287
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    : e + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_288
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_289
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_290
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_291
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_292
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_293
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_294
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    : a + d + f = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_295
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : a + 2 * b + 2 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_296
    {a b c d f : ℕ}
    (h0 : b + c < f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_297
    {a b f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    : a + 2 * b + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_298
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : a + b + c + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_299
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    : a + c + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_300
    {a b d f : ℕ}
    (h0 : b + f = 2 * d)
    (h1 : d < a + b)
    : 3 * b + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_301
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * b + c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_302
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : d < a + b)
    : b + 2 * c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_303
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : 4 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_304
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : d < a + b)
    : b + d + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_305
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + e + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_306
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : b + c < f)
    : 2 * c + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_307
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : d < a + b)
    : c + d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_308
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    : c + 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_309
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : 2 * d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_310
    {a b f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    : 2 * g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_311
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_312
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_313
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_314
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_315
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + c < (2 * a + 4 * b) ∧ f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_316
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    : a + b + d + e = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_317
    {a b f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    : a + 2 * f = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_318
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 6 * a ≤ d + g)
    (h3 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_319
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_320
    {a b d f : ℕ}
    (h0 : 6 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_321
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ b + c + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_322
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 2 * c + d)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_323
    {a b c d f : ℕ}
    (h0 : 6 * a ≤ 3 * b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_324
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a < a + 3 * b)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + c < f)
    (h5 : b + f = 2 * d)
    (h6 : d < a + b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_325
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a ≤ d + g)
    (h3 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_326
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_327
    {a b d f : ℕ}
    (h0 : 5 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_328
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + c + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_329
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_330
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ 3 * b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_331
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a < a + 3 * b)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + c < f)
    (h5 : b + f = 2 * d)
    (h6 : d < a + b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_332
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ d + g)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_333
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_334
    {a b d f : ℕ}
    (h0 : 4 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_335
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_336
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_337
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ 3 * b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_338
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_339
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + d)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_340
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_341
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a < a + 3 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_342
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ d + g)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_343
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_344
    {a b d f : ℕ}
    (h0 : 3 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_345
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_346
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_347
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ 3 * b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_348
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_349
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + d)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_350
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a ≤ b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_351
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_352
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_353
    {a b c d f : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_354
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 2 * g < a + 2 * f)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_355
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_356
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_357
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_358
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_359
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_360
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_361
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_362
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_363
    {a b d f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_364
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_365
    {a b d f : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_366
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_367
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ c + f)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_368
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_369
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_370
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_371
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_372
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a + b < a + b + f)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + c < f)
    (h5 : b + f = 2 * d)
    (h6 : d < a + b)
    : 4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_373
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_374
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ c + f)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_375
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_376
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a ≤ b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_377
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_378
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_379
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + b < a + b + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f ∧ c + d < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_380
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_381
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ c + f)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_382
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_383
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_384
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_385
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_386
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_387
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_388
    {a b c d f : ℕ}
    (h0 : 2 * a + b < a + b + f)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f ∧ a + d < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_389
    {a b d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_390
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_391
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_392
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_393
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_394
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a + d < a + 2 * b + e)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + c < f)
    (h5 : b + f = 2 * d)
    (h6 : d < a + b)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_395
    {a b d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_396
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_397
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a ≤ b)
    (h3 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_398
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_399
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_400
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + d < a + 2 * b + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_401
    {a b d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_402
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_403
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_404
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_405
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_406
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_407
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_408
    {a b c d e f : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_409
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_410
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_411
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_412
    {a b d f : ℕ}
    (h0 : 4 * a ≤ 3 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_413
    {a b d f : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_414
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_415
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a + f < 2 * a + 4 * b)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + c < f)
    (h5 : b + f = 2 * d)
    (h6 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_416
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_417
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_418
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_419
    {a b d f : ℕ}
    (h0 : a ≤ b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_420
    {a b d f : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_421
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_422
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + f < 2 * a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_423
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_424
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_425
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_426
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_427
    {a b d f : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_428
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_429
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_430
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat111_431
    {a b c d e f : ℕ}
    (h0 : 2 * a + f < 2 * a + 4 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·DD·DE·EE·BBB` dies on power system `S13` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEFG44810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG44810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat111_318 hcq3 hcq4 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_319 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_035 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_320 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_321 hcq3 h hcq1 hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_038 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_322 hcq3 h hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_323 h hcq14 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_324 hcq3 hcq4 h hcq1 hcq14 hcq0 hcq7)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_325 hcq3 hcq4 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_326 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_044 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_327 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_328 hcq3 h hcq1 hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_047 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_329 hcq3 h hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_330 h hcq14 hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_331 hcq3 hcq4 h hcq1 hcq14 hcq0 hcq7)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_332 hcq3 hcq4 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_333 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_053 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_334 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_335 hcq3 h hcq1 hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_056 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_336 hcq3 h hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_337 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_338 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_339 hcq3 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_340 hcq3 h hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_341 hcq3 h hcq1 hcq14 hcq0 hcq7)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_342 hcq3 hcq4 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_343 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_065 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_344 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_345 hcq3 h hcq1 hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_068 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_346 hcq3 h hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_347 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_348 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_349 hcq3 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_350 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_351 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_352 hcq3 h hcq14 hcq0 hcq7)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_353 h hcq14 hcq0 hcq7)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_354 h hcq3 hcq4 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_355 h hcq3 hcq1 hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_078 h hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_356 h hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_357 h hcq3 hcq1 hcq14 hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_081 h hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_358 h hcq3 hcq14 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_359 h hcq14 hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_360 h hcq3 hcq1 hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_361 h hcq3 hcq14 hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_362 h hcq3 hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_363 h hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_364 h hcq14 hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat111_365 h hcq3 hcq0 hcq7)
  have hr0 : (kappaQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat111_000 hcq7) (by exact astra4wPowerNat111_259 hcq3 hcq14) (by exact astra4wPowerNat111_260 hcq3 hcq4) (by exact astra4wPowerNat111_261 hcq3 hcq14) hz0l hz0beta (Or.inr (by exact astra4wPowerNat111_262 hcq3 hcq14)) hz0delta (Or.inr (by exact astra4wPowerNat111_263 hcq3 hcq14 hcq0)) hz0zeta (Or.inr (by exact astra4wPowerNat111_264 hcq3 hcq14)) hz0theta
  have hct0 := kappaQuarticChamberFace12810_coeff_top_S13 hAne hBne hDne hEne (C := C) (F := F) (G := G) (by exact astra4wPowerNat111_265 hcq3 hcq1)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS13810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_366 hcq3 hcq4 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_367 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_368 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_369 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_370 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_371 h hcq14 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_372 hcq3 hcq4 h hcq1 hcq14 hcq0 hcq7)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_373 hcq3 hcq4 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_374 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_375 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_376 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_377 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_378 h hcq14 hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_379 hcq3 h hcq1 hcq14 hcq0 hcq7)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_380 hcq3 hcq4 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_381 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_382 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_383 h hcq3 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_384 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_385 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_386 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_387 hcq3 h hcq14 hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_388 h hcq14 hcq0 hcq7)
  have hr1 : (muQuarticChamberRest17810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest17810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat111_266 hcq14) (by exact astra4wPowerNat111_267 hcq3 hcq0 hcq7) (by exact astra4wPowerNat111_268 hcq3 hcq1 hcq0 hcq7) (by exact astra4wPowerNat111_269 hcq14 hcq7) (by exact astra4wPowerNat111_270 hcq3 hcq14) (by exact astra4wPowerNat111_271 hcq3 hcq4 hcq14) (by exact astra4wPowerNat111_272 hcq7) hz1l hz1beta (Or.inr (by exact astra4wPowerNat111_273 hcq3 hcq4 hcq14 hcq7)) hz1delta (Or.inr (by exact astra4wPowerNat111_274 hcq3 hcq1 hcq14 hcq0 hcq7)) (Or.inr (by exact astra4wPowerNat111_275 hcq3 hcq14 hcq0 hcq7)) (Or.inr (by exact astra4wPowerNat111_276 hcq3 hcq14)) (Or.inr (by exact astra4wPowerNat111_277 hcq3 hcq14 hcq0 hcq7))
  have hct1 := muQuarticChamberFace17810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat111_278 hcq0) (by exact hcq2.symm)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face17_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS13810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_389 hcq4 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_390 hcq3 h hcq1 hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_092 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_391 hcq3 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_392 hcq3 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_393 hcq3 h hcq1 hcq14 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_394 hcq3 hcq4 h hcq1 hcq14 hcq0 hcq7)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_395 hcq4 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_396 hcq3 h hcq1 hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_099 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_397 hcq3 hcq1 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_398 hcq3 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_399 hcq3 h hcq1 hcq14 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_400 hcq3 h hcq1 hcq14 hcq0 hcq7)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_401 hcq4 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_402 hcq3 h hcq1 hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_106 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_403 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_404 hcq3 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_405 hcq3 h hcq1 hcq14 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_406 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_407 hcq3 h hcq1 hcq14 hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_408 h hcq3 hcq1 hcq14 hcq0 hcq7)
  have hr2 : (xiQuarticChamberRest18810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest18810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by exact astra4wPowerNat111_279 hcq3 hcq1 hcq7) (by exact astra4wPowerNat111_280 hcq3 hcq1 hcq14 hcq0) (by exact astra4wPowerNat111_281 hcq3 hcq1 hcq7) (by exact astra4wPowerNat111_282 hcq3 hcq1 hcq14 hcq7) (by exact astra4wPowerNat111_283 hcq4 hcq1 hcq7) (by exact astra4wPowerNat111_284 hcq3 hcq1 hcq14 hcq7) (by exact astra4wPowerNat111_010 hcq7) (by exact astra4wPowerNat111_285 hcq3 hcq14) (by exact astra4wPowerNat111_286 hcq3 hcq1 hcq14 hcq0 hcq7) (by exact astra4wPowerNat111_287 hcq3 hcq4) (by exact astra4wPowerNat111_288 hcq3 hcq1 hcq7) hz2l hz2beta (Or.inr (by exact astra4wPowerNat111_289 hcq3 hcq1 hcq14 hcq0 hcq7)) hz2delta (Or.inr (by exact astra4wPowerNat111_290 hcq3 hcq4 hcq1 hcq14 hcq0 hcq7)) (Or.inr (by exact astra4wPowerNat111_291 hcq3 hcq1 hcq14 hcq0 hcq7)) (Or.inr (by exact astra4wPowerNat111_292 hcq3 hcq1 hcq14 hcq7)) (Or.inr (by exact astra4wPowerNat111_293 hcq3 hcq1 hcq14 hcq0 hcq7))
  have hct2 := xiQuarticChamberFace18810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat111_294 hcq3 hcq1 hcq0)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face18_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS13810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_409 hcq3 hcq4 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_410 hcq3 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_411 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_412 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_413 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_414 hcq3 h hcq14 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_415 hcq3 hcq4 h hcq1 hcq14 hcq0 hcq7)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_416 hcq3 hcq4 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_417 hcq3 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_418 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_419 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_420 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_421 hcq3 h hcq14 hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_422 hcq3 h hcq1 hcq14 hcq0 hcq7)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_423 hcq3 hcq4 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_424 hcq3 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_425 hcq3 h hcq1 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_426 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_427 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_428 hcq3 h hcq14 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_429 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat111_430 hcq3 h hcq14 hcq0 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_431 h hcq3 hcq1 hcq14 hcq0 hcq7)
  have hr3 : (piQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest10810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 (by exact astra4wPowerNat111_018 hcq7) (by exact astra4wPowerNat111_295 hcq3 hcq14) (by exact astra4wPowerNat111_296 hcq14 hcq0 hcq7) (by exact astra4wPowerNat111_297 hcq3 hcq4) (by exact astra4wPowerNat111_298 hcq3 hcq14) (by exact astra4wPowerNat111_299 hcq3 hcq14 hcq0) (by exact astra4wPowerNat111_300 hcq0 hcq7) (by exact astra4wPowerNat111_301 hcq3 hcq1 hcq14 hcq0 hcq7) (by exact astra4wPowerNat111_020 hcq7) (by exact astra4wPowerNat111_302 hcq3 hcq14 hcq7) (by exact astra4wPowerNat111_303 hcq3 hcq14) (by exact astra4wPowerNat111_304 hcq3 hcq4 hcq7) (by exact astra4wPowerNat111_305 hcq3 hcq1 hcq0 hcq7) (by exact astra4wPowerNat111_306 hcq3 hcq4 hcq14) (by exact astra4wPowerNat111_307 hcq3 hcq14 hcq7) (by exact astra4wPowerNat111_308 hcq3 hcq1 hcq14 hcq0) (by exact astra4wPowerNat111_309 hcq3 hcq1 hcq7) (by exact astra4wPowerNat111_310 hcq3 hcq4) hz3l hz3beta (Or.inr (by exact astra4wPowerNat111_311 hcq3 hcq1 hcq14 hcq0 hcq7)) hz3delta (Or.inr (by exact astra4wPowerNat111_312 hcq3 hcq1 hcq14 hcq0 hcq7)) (Or.inr (by exact astra4wPowerNat111_313 hcq3 hcq1 hcq14 hcq0 hcq7)) (Or.inr (by exact astra4wPowerNat111_314 hcq3 hcq4 hcq14 hcq7)) (Or.inr (by exact astra4wPowerNat111_315 hcq3 hcq14 hcq0 hcq7))
  have hct3 := piQuarticChamberFace10810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat111_316 hcq3 hcq1) (by exact astra4wPowerNat111_317 hcq3)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face10_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : piQuarticPowerInnerS13810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS13810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hEc


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
/-- Chamber `BDEG` / `BG·DD·DE·EE·BBB` dies on power system `S14` (carriers κ, ξ, π). -/
theorem quarticChamberBDEG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEG7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_033 h hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_156 hcq0 hAF h hcq1 hcq4 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_035 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_157 hcq0 hAF h hcq4 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_037 hcq0 h hcq1 hAC hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_038 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_039 hcq0 h hAC hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_040 hcq0 h hAC hCn hcq4 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_230 hcq0 h hcq1 hcq4 hcq3)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_042 h hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_231 hcq0 hAF h hcq1 hcq4 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_044 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_232 hcq0 hAF h hcq4 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_046 hcq0 h hcq1 hAC hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_047 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_048 hcq0 h hAC hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_049 hcq0 h hAC hCn hcq4 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_050 hcq0 h hcq1 hcq4 hcq3)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_051 h hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_233 hcq0 h hcq1 hcq4 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_053 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_234 hcq0 hAF h hcq4 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_055 hcq0 h hcq1 hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_056 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_235 hcq0 h hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_058 hcq0 h hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_059 hcq0 h hcq1 hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_060 hcq0 h hAC hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_061 hcq0 h hcq4 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_062 hcq0 h hcq1 hcq4 hcq3)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_063 h hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_236 hcq0 h hcq1 hcq4 hFn hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_065 h hcq4)
    · exact Or.inr (by exact astra4wPowerNat111_237 hcq0 h hcq4 hFn hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_067 hcq0 h hcq1 hCn hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_068 h hcq4)
    · exact Or.inr (by exact astra4wPowerNat111_238 hcq0 h hCn hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_070 hcq0 h hCn hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_071 hcq0 h hcq1 hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_072 hcq0 h hAC hCn hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_073 hcq0 h hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_239 hcq0 h hcq4 hFn hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_075 hcq0 h hAC hCn hcq4 hcq3)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_076 h hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_184 h hcq0 hcq1 hcq4 hFn hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_078 h hcq4)
    · exact Or.inr (by exact astra4wPowerNat111_185 h hcq0 hcq4 hFn hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_080 h hcq0 hcq1 hCn hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_081 h hcq4)
    · exact Or.inr (by exact astra4wPowerNat111_082 h hcq0 hCn hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_083 h hcq0 hCn hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_084 h hcq0 hcq1 hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_085 h hcq0 hCn hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_086 h hcq0 hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_190 h hcq0 hcq4 hFn hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_088 h hcq0 hAC hCn hcq4 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_089 h hcq0 hcq4 hcq3)
  have hr0 : (kappaQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest13810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz hFz (by exact astra4wPowerNat111_000 hcq4) hz0l hz0beta hz0delta (Or.inr (by exact astra4wPowerNat111_002 hcq4)) hz0zeta (Or.inr (by exact astra4wPowerNat111_003 hcq0 hcq4 hcq3)) hz0theta
  have hct0 := kappaQuarticChamberFace13810_coeff_top_S14 hAne hBne hDne hEne hGne (C := C) (F := F) (by exact astra4wPowerNat111_004 hcq3) (by exact astra4wPowerNat111_005 hcq1 hcq3)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_090 h hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_240 hcq0 hAF h hcq1 hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_092 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_093 h hcq1 hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_094 h hcq1 hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_095 hcq0 h hcq1 hAC hCn hcq4 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_241 hcq0 h hcq1 hcq4 hcq3)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_097 h hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_242 hcq0 hAF h hcq1 hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_099 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_100 h hcq1 hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_101 h hcq1 hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_243 hcq0 h hcq1 hCn hcq4 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_244 hcq0 h hcq1 hcq4 hcq3)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_104 h hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_245 hcq0 h hcq1 hCn hcq4 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_106 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_107 h hcq1 hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_108 h hcq1 hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_246 hcq0 h hcq1 hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_247 hcq0 h hcq1 hcq4 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_111 hcq0 h hcq1 hAC hCn hcq4 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_248 h hcq0 hcq1 hcq4 hcq3)
  have hr1 : (xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest19810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz hFz (by exact astra4wPowerNat111_006 hcq1 hcq4 hcq3) (by exact astra4wPowerNat111_007 hcq1 hcq4 hcq3) (by exact astra4wPowerNat111_009 hcq1 hcq4) (by exact astra4wPowerNat111_010 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat111_224 hcq0 hcq1 hcq4 hcq3)) hz1delta (Or.inr (by exact astra4wPowerNat111_013 hcq1 hcq4 hcq3)) (Or.inr (by exact astra4wPowerNat111_225 hcq0 hcq1 hcq4 hcq3)) (Or.inr (by exact astra4wPowerNat111_015 hcq0 hcq1 hcq4 hcq3)) (Or.inr (by exact astra4wPowerNat111_016 hcq1 hcq4 hcq3))
  have hct1 := xiQuarticChamberFace19810_coeff_top_S14 hAne hBne hEne hGne (C := C) (D := D) (F := F) (by exact astra4wPowerNat111_017 hcq3)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_249 hcq0 h hcq1 hcq4)
      · exact absurd h (by exact astra4wPowerNat111_114 hcq0 hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_250 hcq0 h hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_251 h hcq0 hcq1 hcq4)
      · exact absurd h (by exact astra4wPowerNat111_207 hcq0 hcq4 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_252 h hcq0 hcq1 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_253 hcq0 h hcq1 hcq4 hcq3)
  have hz2beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_254 hcq0 h hcq1 hcq4)
      · exact absurd h (by exact astra4wPowerNat111_121 hcq0 hCn hcq4 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_255 hcq0 h hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat111_256 hcq0 h hcq1 hcq4)
      · exact absurd h (by exact astra4wPowerNat111_214 hcq0 hcq4 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_257 h hcq0 hcq1 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_258 h hcq1 hcq4 hcq3)
  have hr2 : (piQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest11810_natDegree_lt_of_live_BDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hCz hFz (by exact astra4wPowerNat111_018 hcq4) (by exact astra4wPowerNat111_020 hcq4) (by exact astra4wPowerNat111_022 hcq4 hcq3) (by exact astra4wPowerNat111_024 hcq1 hcq4 hcq3) hz2l hz2beta (Or.inr (by exact astra4wPowerNat111_226 hcq0 hcq1 hcq4 hcq3)) (Or.inr (by exact astra4wPowerNat111_227 hcq0 hcq1 hcq4 hcq3)) (Or.inr (by exact astra4wPowerNat111_228 hcq4)) (Or.inr (by exact astra4wPowerNat111_229 hcq0 hcq1 hcq4 hcq3)) (Or.inr (by exact astra4wPowerNat111_028 hcq0 hcq4 hcq3))
  have hct2 := piQuarticChamberFace11810_coeff_top_S14 hAne hBne hDne hEne hGne (C := C) (F := F) (by exact astra4wPowerNat111_030 hcq3) (by exact astra4wPowerNat111_031 hcq1 hcq3) (by exact astra4wPowerNat111_032 hcq3)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face11_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS14810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hGc


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
/-- Chamber `BCDEG` / `BG·DD·DE·EE·BBB` dies on power system `S14` (carriers κ, ξ, π). -/
theorem quarticChamberBCDEG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
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
      · exact Or.inr (by exact astra4wPowerNat111_033 h hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_156 hcq0 hAF h hcq1 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_035 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_157 hcq0 hAF h hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_158 hcq0 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_038 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_159 hcq4 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_160 hcq0 hcq4 h hcq5 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_161 hcq0 hcq4 h hcq1 hcq5 hcq3)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_042 h hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_162 hcq0 hcq4 h hcq1 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_044 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_163 hcq0 hcq4 h hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_164 hcq0 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_047 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_165 hcq4 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_166 hcq0 hcq4 h hcq5 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_167 hcq0 hcq4 h hcq1 hcq5 hcq3)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_051 h hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_168 hcq0 hcq4 h hcq1 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_053 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_169 hcq0 hcq4 h hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_170 hcq0 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_056 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_171 hcq4 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_172 hcq0 hcq4 h hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_059 hcq0 h hcq1 hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_173 hcq0 hcq4 h hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_061 hcq0 h hcq5 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_174 hcq0 hcq4 h hcq1 hcq5 hcq3)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_063 h hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_175 hcq0 hcq4 h hcq1 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_065 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_176 hcq0 hcq4 h hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_177 hcq0 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_068 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_178 hcq4 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_179 hcq0 hcq4 h hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_071 hcq0 h hcq1 hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_180 hcq0 hcq4 h hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_073 hcq0 h hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_181 hcq0 hcq4 h hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_182 hcq0 hcq4 h hcq5 hcq3)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_183 h hcq0 hcq4 hcq5 hcq3)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_076 h hcq5 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_184 h hcq0 hcq1 hcq5 hFn hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_078 h hcq5)
    · exact Or.inr (by exact astra4wPowerNat111_185 h hcq0 hcq5 hFn hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_186 h hcq0 hcq4 hcq1 hcq5)
    · exact Or.inr (by exact astra4wPowerNat111_081 h hcq5)
    · exact Or.inr (by exact astra4wPowerNat111_187 h hcq4 hcq5)
    · exact Or.inr (by exact astra4wPowerNat111_188 h hcq0 hcq4 hcq5 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_084 h hcq0 hcq1 hcq5 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_189 h hcq0 hcq4 hcq5 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_086 h hcq0 hcq5 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_190 h hcq0 hcq5 hFn hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_191 h hcq0 hcq4 hcq5 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_089 h hcq0 hcq5 hcq3)
  have hr0 : (kappaQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest13810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by exact astra4wPowerNat111_000 hcq5) (by exact astra4wPowerNat111_134 hcq4) hz0l hz0beta (Or.inr (by exact astra4wPowerNat111_135 hcq0 hcq4 hcq5 hcq3)) hz0delta (Or.inr (by exact astra4wPowerNat111_002 hcq5)) hz0zeta (Or.inr (by exact astra4wPowerNat111_003 hcq0 hcq5 hcq3)) hz0theta
  have hct0 := kappaQuarticChamberFace13810_coeff_top_S14 hAne hBne hDne hEne hGne (C := C) (F := F) (by exact astra4wPowerNat111_004 hcq3) (by exact astra4wPowerNat111_005 hcq1 hcq3)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_090 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_192 hcq0 hcq4 hAF h hcq1 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_092 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_093 h hcq1 hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_094 h hcq1 hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_193 hcq4 h hcq1 hcq5 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_194 hcq0 hcq4 h hcq1 hcq5 hcq3)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_097 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_195 hcq0 hcq4 h hcq1 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_099 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_100 h hcq1 hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_101 h hcq1 hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_196 hcq4 h hcq1 hcq5 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_197 hcq0 hcq4 h hcq1 hcq5 hcq3)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_104 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_198 hcq0 hcq4 h hcq1 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_106 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_107 h hcq1 hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_108 h hcq1 hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_199 hcq4 h hcq1 hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_200 hcq0 hcq4 h hcq1 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_201 hcq0 hcq4 h hcq1 hcq5 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_202 h hcq0 hcq4 hcq1 hcq5 hcq3)
  have hr1 : (xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest19810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by exact astra4wPowerNat111_006 hcq1 hcq5 hcq3) (by exact astra4wPowerNat111_136 hcq0 hcq4 hcq1) (by exact astra4wPowerNat111_007 hcq1 hcq5 hcq3) (by exact astra4wPowerNat111_137 hcq4 hcq1 hcq5 hcq3) (by exact astra4wPowerNat111_009 hcq1 hcq5) (by exact astra4wPowerNat111_010 hcq5) (by exact astra4wPowerNat111_138 hcq4) (by exact astra4wPowerNat111_139 hcq0 hcq4 hcq1 hcq5) hz1l hz1beta (Or.inr (by exact astra4wPowerNat111_140 hcq0 hcq4 hcq1 hcq5 hcq3)) hz1delta (Or.inr (by exact astra4wPowerNat111_141 hcq4 hcq1 hcq5 hcq3)) (Or.inr (by exact astra4wPowerNat111_142 hcq0 hcq4 hcq1 hcq5 hcq3)) (Or.inr (by exact astra4wPowerNat111_015 hcq0 hcq1 hcq5 hcq3)) (Or.inr (by exact astra4wPowerNat111_016 hcq1 hcq5 hcq3))
  have hct1 := xiQuarticChamberFace19810_coeff_top_S14 hAne hBne hEne hGne (C := C) (D := D) (F := F) (by exact astra4wPowerNat111_017 hcq3)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_203 hcq0 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_204 hcq0 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_205 hcq0 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_206 h hcq0 hcq4 hcq1 hcq5)
      · exact absurd h (by exact astra4wPowerNat111_207 hcq0 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_208 h hcq0 hcq4 hcq1 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_209 hcq0 hcq4 h hcq1 hcq5 hcq3)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_210 hcq0 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_211 hcq0 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_212 hcq0 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_213 hcq0 hcq4 h hcq1 hcq5)
      · exact absurd h (by exact astra4wPowerNat111_214 hcq0 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_215 h hcq0 hcq4 hcq1 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_216 hcq0 hcq4 h hcq1 hcq5 hcq3)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_217 hcq4 h)
      · exact Or.inr (by exact astra4wPowerNat111_218 hcq4 h)
      · exact Or.inr (by exact astra4wPowerNat111_219 hcq4 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat111_220 hcq0 hcq4 h hcq1 hcq5)
      · exact absurd h (by exact astra4wPowerNat111_221 hcq0 hcq5 hFn hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_222 h hcq0 hcq4 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_223 h hcq0 hcq4 hcq1 hcq5 hcq3)
  have hr2 : (piQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest11810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hFz (by exact astra4wPowerNat111_018 hcq5) (by exact astra4wPowerNat111_143 hcq4) (by exact astra4wPowerNat111_144 hcq0 hcq4 hcq5 hcq3) (by exact astra4wPowerNat111_145 hcq0 hcq4 hcq3) (by exact astra4wPowerNat111_146 hcq0 hcq4 hcq1 hcq5) (by exact astra4wPowerNat111_020 hcq5) (by exact astra4wPowerNat111_147 hcq4 hcq5) (by exact astra4wPowerNat111_148 hcq4) (by exact astra4wPowerNat111_022 hcq5 hcq3) (by exact astra4wPowerNat111_149 hcq4 hcq3) (by exact astra4wPowerNat111_150 hcq0 hcq4 hcq1 hcq3) (by exact astra4wPowerNat111_024 hcq1 hcq5 hcq3) hz2l hz2beta (Or.inr (by exact astra4wPowerNat111_151 hcq0 hcq4 hcq1 hcq5 hcq3)) hz2delta (Or.inr (by exact astra4wPowerNat111_152 hcq0 hcq4 hcq1 hcq5 hcq3)) (Or.inr (by exact astra4wPowerNat111_153 hcq0 hcq4 hcq1 hcq5 hcq3)) (Or.inr (by exact astra4wPowerNat111_154 hcq0 hcq4 hcq5 hcq3)) (Or.inr (by exact astra4wPowerNat111_155 hcq0 hcq4 hcq5 hcq3))
  have hct2 := piQuarticChamberFace11810_coeff_top_S14 hAne hBne hDne hEne hGne (C := C) (F := F) (by exact astra4wPowerNat111_030 hcq3) (by exact astra4wPowerNat111_031 hcq1 hcq3) (by exact astra4wPowerNat111_032 hcq3)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face11_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS14810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hGc


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
/-- Chamber `BDEFG` / `BG·DD·DE·EE·BBB` dies on power system `S14` (carriers κ, ξ, π). -/
theorem quarticChamberBDEFG31810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG31810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_033 h hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_034 hcq0 h hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_035 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_036 hcq0 h hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_037 hcq0 h hcq1 hAC hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_038 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_039 hcq0 h hAC hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_040 hcq0 h hAC hCn hcq6 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_041 hcq0 h hcq4 hcq1 hcq6 hcq3)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_042 h hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_043 hcq0 h hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_044 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_045 hcq0 h hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_046 hcq0 h hcq1 hAC hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_047 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_048 hcq0 h hAC hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_049 hcq0 h hAC hCn hcq6 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_050 hcq0 h hcq1 hcq6 hcq3)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_051 h hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_052 hcq0 h hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_053 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_054 hcq0 h hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_055 hcq0 h hcq1 hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_056 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_057 hcq0 hcq5 h hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_058 hcq0 h hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_059 hcq0 h hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_060 hcq0 h hAC hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_061 hcq0 h hcq6 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_062 hcq0 h hcq1 hcq6 hcq3)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_063 h hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_064 hcq0 h hcq4 hcq1 hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_065 h hcq6)
    · exact Or.inr (by exact astra4wPowerNat111_066 hcq0 h hcq4 hcq6)
    · exact Or.inr (by exact astra4wPowerNat111_067 hcq0 h hcq1 hCn hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_068 h hcq6)
    · exact Or.inr (by exact astra4wPowerNat111_069 hcq0 hcq5 h hCn hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_070 hcq0 h hCn hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_071 hcq0 h hcq1 hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_072 hcq0 h hAC hCn hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_073 hcq0 h hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_074 hcq0 h hcq4 hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_075 hcq0 h hAC hCn hcq6 hcq3)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_076 h hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_077 h hcq0 hcq4 hcq1 hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_078 h hcq6)
    · exact Or.inr (by exact astra4wPowerNat111_079 h hcq0 hcq4 hcq6)
    · exact Or.inr (by exact astra4wPowerNat111_080 h hcq0 hcq1 hCn hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_081 h hcq6)
    · exact Or.inr (by exact astra4wPowerNat111_082 h hcq0 hCn hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_083 h hcq0 hCn hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_084 h hcq0 hcq1 hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_085 h hcq0 hCn hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_086 h hcq0 hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_087 h hcq0 hcq4 hcq6)
    · exact Or.inr (by exact astra4wPowerNat111_088 h hcq0 hAC hCn hcq6 hcq3)
    · exact Or.inr (by exact astra4wPowerNat111_089 h hcq0 hcq6 hcq3)
  have hr0 : (kappaQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest13810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz (by exact astra4wPowerNat111_000 hcq6) hz0l hz0beta (Or.inr (by exact astra4wPowerNat111_001 hcq0 hcq4 hcq6 hcq3)) hz0delta (Or.inr (by exact astra4wPowerNat111_002 hcq6)) hz0zeta (Or.inr (by exact astra4wPowerNat111_003 hcq0 hcq6 hcq3)) hz0theta
  have hct0 := kappaQuarticChamberFace13810_coeff_top_S14 hAne hBne hDne hEne hGne (C := C) (F := F) (by exact astra4wPowerNat111_004 hcq3) (by exact astra4wPowerNat111_005 hcq1 hcq3)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_090 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_091 hcq0 hcq5 h hcq1 hAC hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_092 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_093 h hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_094 h hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_095 hcq0 h hcq1 hAC hCn hcq6 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_096 hcq0 h hcq4 hcq1 hcq6 hcq3)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_097 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_098 hcq0 hcq5 h hcq1 hAC hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_099 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_100 h hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_101 h hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_102 hcq0 hcq5 h hcq1 hCn hcq6 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_103 hcq0 h hcq4 hcq1 hcq6 hcq3)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_104 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_105 hcq0 h hcq4 hcq1 hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_106 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat111_107 h hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_108 h hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_109 hcq0 hcq5 h hcq1 hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_110 hcq0 h hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_111 hcq0 h hcq1 hAC hCn hcq6 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_112 h hcq0 hcq4 hcq1 hcq6 hcq3)
  have hr1 : (xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest19810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz (by exact astra4wPowerNat111_006 hcq1 hcq6 hcq3) (by exact astra4wPowerNat111_007 hcq1 hcq6 hcq3) (by exact astra4wPowerNat111_008 hcq0 hcq4 hcq1 hcq3) (by exact astra4wPowerNat111_009 hcq1 hcq6) (by exact astra4wPowerNat111_010 hcq6) (by exact astra4wPowerNat111_011 hcq4 hcq1 hcq6 hcq3) hz1l hz1beta (Or.inr (by exact astra4wPowerNat111_012 hcq0 hcq4 hcq1 hcq6 hcq3)) hz1delta (Or.inr (by exact astra4wPowerNat111_013 hcq1 hcq6 hcq3)) (Or.inr (by exact astra4wPowerNat111_014 hcq0 hcq4 hcq1 hcq6 hcq3)) (Or.inr (by exact astra4wPowerNat111_015 hcq0 hcq1 hcq6 hcq3)) (Or.inr (by exact astra4wPowerNat111_016 hcq1 hcq6 hcq3))
  have hct1 := xiQuarticChamberFace19810_coeff_top_S14 hAne hBne hEne hGne (C := C) (D := D) (F := F) (by exact astra4wPowerNat111_017 hcq3)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_113 hcq0 h hcq4 hcq1 hcq6 hcq3)
      · exact absurd h (by exact astra4wPowerNat111_114 hcq0 hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_115 hcq0 h hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_116 h hcq0 hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_117 h hcq0 hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_118 h hcq0 hcq4 hcq1 hcq6 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_119 hcq0 h hcq1 hcq6 hcq3)
  have hz2beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_120 hcq0 h hcq4 hcq1 hcq6 hcq3)
      · exact absurd h (by exact astra4wPowerNat111_121 hcq0 hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_122 hcq0 h hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_123 hcq0 h hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_124 h hcq0 hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_125 h hcq0 hcq4 hcq1 hcq6 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_126 hcq0 h hcq1 hcq6 hcq3)
  have hz2delta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat111_127 hcq4 h hcq3)
      · exact absurd h (by exact astra4wPowerNat111_128 hcq0 hCn hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_129 h hcq4 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_130 hcq0 h hcq4 hcq1 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_131 hcq0 h hcq4 hcq6 hcq3)
      · exact Or.inr (by exact astra4wPowerNat111_132 h hcq0 hcq4 hcq6 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat111_133 h hcq0 hcq1 hcq6 hcq3)
  have hr2 : (piQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest11810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hCz (by exact astra4wPowerNat111_018 hcq6) (by exact astra4wPowerNat111_019 hcq0 hcq4 hcq6) (by exact astra4wPowerNat111_020 hcq6) (by exact astra4wPowerNat111_021 hcq4 hcq3) (by exact astra4wPowerNat111_022 hcq6 hcq3) (by exact astra4wPowerNat111_023 hcq0 hcq4 hcq1 hcq6 hcq3) (by exact astra4wPowerNat111_024 hcq1 hcq6 hcq3) hz2l hz2beta (Or.inr (by exact astra4wPowerNat111_025 hcq0 hcq4 hcq1 hcq6 hcq3)) hz2delta (Or.inr (by exact astra4wPowerNat111_026 hcq0 hcq4 hcq6)) (Or.inr (by exact astra4wPowerNat111_027 hcq0 hcq4 hcq1 hcq6 hcq3)) (Or.inr (by exact astra4wPowerNat111_028 hcq0 hcq6 hcq3)) (Or.inr (by exact astra4wPowerNat111_029 hcq0 hcq4 hcq6))
  have hct2 := piQuarticChamberFace11810_coeff_top_S14 hAne hBne hDne hEne hGne (C := C) (F := F) (by exact astra4wPowerNat111_030 hcq3) (by exact astra4wPowerNat111_031 hcq1 hcq3) (by exact astra4wPowerNat111_032 hcq3)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face11_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticPowerInnerS14810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS14810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hGc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
