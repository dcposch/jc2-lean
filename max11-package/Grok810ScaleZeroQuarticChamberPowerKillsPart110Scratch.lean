import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
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
private theorem astra4wPowerNat110_000
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_001
    {a b f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    : b + g < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_002
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_003
    {a b d : ℕ}
    (h0 : d < a + b)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_004
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_005
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    : d + e = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_006
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_007
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b + e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_008
    {a b d f : ℕ}
    (h0 : d < a + b)
    : d + f < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_009
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 2 * b < (a + b + f) ∧ b + d < (a + b + f) ∧ g < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_010
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b < (a + b + f) ∧ e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_011
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a + b < (a + b + f) ∧ d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_012
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_013
    {a b d f : ℕ}
    (h0 : b + f = 2 * d)
    : a + 2 * d = a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_014
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_015
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_016
    {a b d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_017
    {a b d e : ℕ}
    (h0 : d < a + b)
    : b + d + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_018
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    : e + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_019
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_020
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b + d < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_021
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_022
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + d < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_023
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_024
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_025
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    : a + d + f = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_026
    {a b d : ℕ}
    (h0 : d < a + b)
    : a + 3 * b + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_027
    {a b f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    : a + 2 * b + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_028
    {a b d f : ℕ}
    (h0 : b + f = 2 * d)
    (h1 : d < a + b)
    : 3 * b + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_029
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_030
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : d < a + b)
    : b + d + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_031
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + e + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_032
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : 2 * d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_033
    {a b f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    : 2 * g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_034
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_035
    {a b d f : ℕ}
    (h0 : b + f = 2 * d)
    (h1 : d < a + b)
    : a + b + d < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_036
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_037
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_038
    {a b d f : ℕ}
    (h0 : b + f = 2 * d)
    (h1 : d < a + b)
    : f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_039
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    : a + b + d + e = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_040
    {a b f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    : a + 2 * f = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_041
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 6 * a ≤ d + g)
    (h3 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_042
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_043
    {a b d : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_044
    {a b d f : ℕ}
    (h0 : 6 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_045
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ b + c + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_046
    {a b d : ℕ}
    (h0 : 6 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_047
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 2 * c + d)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_048
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 3 * b + c)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_049
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a < a + 3 * b)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_050
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a ≤ d + g)
    (h3 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_051
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_052
    {a b d : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_053
    {a b d f : ℕ}
    (h0 : 5 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_054
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + c + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_055
    {a b d : ℕ}
    (h0 : 5 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_056
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_057
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 3 * b + c)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_058
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a < a + 3 * b)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_059
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ d + g)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_060
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_061
    {a b d : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_062
    {a b d f : ℕ}
    (h0 : 4 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_063
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_064
    {a b d : ℕ}
    (h0 : 4 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_065
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_066
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_067
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_068
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + d)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_069
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_070
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a < a + 3 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_071
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ d + g)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_072
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_073
    {a b d : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_074
    {a b d f : ℕ}
    (h0 : 3 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_075
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_076
    {a b d : ℕ}
    (h0 : 3 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_077
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ 2 * c + d)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_078
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_079
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_080
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + d)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_081
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a ≤ b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_082
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_083
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_084
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 2 * g < a + 2 * f)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_085
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_086
    {a b d : ℕ}
    (h0 : a ≤ 2 * b + d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_087
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_088
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_089
    {a b d : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_090
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_091
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_092
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_093
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_094
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_095
    {a b d f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_096
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_097
    {a b d f : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_098
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_099
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_100
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_101
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_102
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_103
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_104
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a + b < a + b + f)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ 2 * b + d < a + b + f ∧ b + g < a + b + f ∧ d + e < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_105
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_106
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_107
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_108
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a ≤ b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_109
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_110
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ b + 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_111
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + b < a + b + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_112
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_113
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_114
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_115
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_116
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_117
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ b + 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_118
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_119
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_120
    {a b d f : ℕ}
    (h0 : 2 * a + b < a + b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a + b < a + b + f ∧ a + d < a + b + f ∧ f < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_121
    {a b d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_122
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_123
    {a b d e : ℕ}
    (h0 : 5 * a ≤ d + e)
    (h1 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_124
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_125
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_126
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_127
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a + d < a + 2 * b + e)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a + d < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_128
    {a b d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_129
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_130
    {a b d e : ℕ}
    (h0 : 4 * a ≤ d + e)
    (h1 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_131
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a ≤ b)
    (h3 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_132
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_133
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ b + 2 * c)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + f = 2 * d)
    (h5 : c = 0)
    (h6 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_134
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + d < a + 2 * b + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_135
    {a b d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_136
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_137
    {a b d e : ℕ}
    (h0 : 3 * a ≤ d + e)
    (h1 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_138
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_139
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_140
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ b + 2 * c)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + f = 2 * d)
    (h5 : c = 0)
    (h6 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_141
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_142
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_143
    {a b d e f : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_144
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_145
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_146
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_147
    {a b d f : ℕ}
    (h0 : 4 * a ≤ 3 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_148
    {a b d f : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_149
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_150
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a + f < 2 * a + 4 * b)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_151
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_152
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_153
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_154
    {a b d f : ℕ}
    (h0 : a ≤ b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_155
    {a b d f : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_156
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ b + 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_157
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + f < 2 * a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_158
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_159
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_160
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_161
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_162
    {a b d f : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_163
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ b + 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_164
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_165
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : b + f = 2 * d)
    (h3 : c < 2 * a)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_166
    {a b d e f : ℕ}
    (h0 : 2 * a + f < 2 * a + 4 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_167
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : b + 2 * c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_168
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : c + f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_169
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_170
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_171
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_172
    {a b c f : ℕ}
    (h0 : b + c < f)
    : a + 2 * b + c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_173
    {a b c d f : ℕ}
    (h0 : b + c < f)
    (h1 : d < a + b)
    : b + c + d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_174
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : 3 * c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_175
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : d < a + b)
    : a + 2 * b < (a + b + f) ∧ b + d < (a + b + f) ∧ 2 * c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_176
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * b < (a + b + f) ∧ e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_177
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b < (a + b + f) ∧ d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_178
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_179
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_180
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    : a + b + c + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_181
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_182
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_183
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : 2 * c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_184
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_185
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_186
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_187
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_188
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_189
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_190
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : a + 2 * b + 2 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_191
    {a b c d f : ℕ}
    (h0 : b + c < f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_192
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : a + b + c + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_193
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    : a + c + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_194
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * b + c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_195
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : d < a + b)
    : b + 2 * c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_196
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    : 4 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_197
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : d < a + b)
    : c + d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_198
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    : c + 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_199
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_200
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_201
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_202
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : d < a + b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_203
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + c < (2 * a + 4 * b) ∧ f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_204
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ d + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_205
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
private theorem astra4wPowerNat110_206
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 2 * c + d)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_207
    {a b c d f : ℕ}
    (h0 : 6 * a ≤ 3 * b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_208
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_209
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_210
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
private theorem astra4wPowerNat110_211
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_212
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ 3 * b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_213
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_214
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ d + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_215
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
private theorem astra4wPowerNat110_216
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_217
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ 3 * b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_218
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + d)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_219
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
private theorem astra4wPowerNat110_220
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ d + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_221
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
private theorem astra4wPowerNat110_222
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_223
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ 3 * b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_224
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + d)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_225
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_226
    {a b c d f : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_227
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_228
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
private theorem astra4wPowerNat110_229
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_230
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_231
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_232
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_233
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_234
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ c + f)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_235
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_236
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + b < a + b + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_237
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_238
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ c + f)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_239
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_240
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
private theorem astra4wPowerNat110_241
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_242
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ c + f)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_243
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_244
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_245
    {a b c d f : ℕ}
    (h0 : 2 * a + b < a + b + f)
    (h1 : b + c < f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f ∧ a + d < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_246
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g < 4 * a)
    (h6 : g = 0)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_247
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_248
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_249
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + d < a + 2 * b + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_250
    {a b c d e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_251
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_252
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_253
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
private theorem astra4wPowerNat110_254
    {a b c d e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_255
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_256
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_257
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
private theorem astra4wPowerNat110_258
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
private theorem astra4wPowerNat110_259
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_260
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_261
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_262
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + f < 2 * a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + c < f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_263
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_264
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_265
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_266
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
private theorem astra4wPowerNat110_267
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_268
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_269
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_270
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : b + c < f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_271
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
private theorem astra4wPowerNat110_272
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a + 2 * b < (a + b + f) ∧ b + d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_273
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : d < a + b)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_274
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_275
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_276
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ d + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_277
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_278
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ d + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_279
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_280
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_281
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_282
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + b < a + b + f)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ 2 * b + d < a + b + f ∧ d + e < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_283
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g = 0)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_284
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_285
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g = 0)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_286
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_287
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + d < a + 2 * b + e)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_288
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_289
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_290
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_291
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_292
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + f < 2 * a + 4 * b)
    (h2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_293
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g = 0)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_294
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : 3 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_295
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g = 0)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat110_296
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : c = 0)
    (h4 : d < a + b)
    : 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BDEF` / `BF·DD·DE·EE·BBB` dies on power system `S13` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBDEF7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEF7810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_204 hcq3 h hcq0 hcq4 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat110_042 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_043 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_044 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_045 hcq3 h hcq1 hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_046 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_047 hcq3 h hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_048 hcq3 h hcq0 hAC hCn hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_275 hcq3 h hcq1 hcq0 hcq4)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_276 hcq3 h hcq0 hcq4 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat110_051 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_052 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_053 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_054 hcq3 h hcq1 hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_055 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_056 hcq3 h hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_057 hcq3 h hcq0 hAC hCn hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_277 hcq3 h hcq1 hcq0 hcq4)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_278 hcq3 h hcq0 hcq4 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_060 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_061 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_062 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_063 hcq3 h hcq1 hcq0 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_064 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_279 hcq3 h hcq0 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_066 hcq3 h hcq0 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_067 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_068 hcq3 h hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_069 hcq3 h hcq0 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_070 hcq3 h hcq1 hcq0 hcq4)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_280 hcq3 h hcq0 hcq4 hGn)
    · exact Or.inr (by exact astra4wPowerNat110_072 hcq3 h hcq1 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_073 h hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_074 h hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_075 hcq3 h hcq1 hcq0 hCn hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_076 h hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_281 hcq3 h hcq0 hCn hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_078 hcq3 h hcq0 hCn hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_079 hcq3 h hcq1 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_080 hcq3 h hcq0 hAC hCn hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_081 hcq3 h hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_082 hcq3 h hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_083 hcq3 h hcq0 hAC hCn hcq4)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_227 h hcq3 hcq0 hcq4 hGn)
    · exact Or.inr (by exact astra4wPowerNat110_085 h hcq3 hcq1 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_086 h hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_087 h hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_088 h hcq3 hcq1 hcq0 hCn hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_089 h hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_090 h hcq3 hcq0 hCn hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_091 h hcq3 hcq0 hCn hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_092 h hcq3 hcq1 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_093 h hcq3 hcq0 hCn hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_094 h hcq3 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_095 h hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_096 h hcq3 hcq0 hAC hCn hcq4)
    · exact Or.inr (by exact astra4wPowerNat110_097 h hcq3 hcq0 hcq4)
  have hr0 : (kappaQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest12810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz hGz (by exact astra4wPowerNat110_000 hcq4) hz0l hz0beta (Or.inr (by exact astra4wPowerNat110_002 hcq3 hcq0 hcq4)) hz0delta (Or.inr (by exact astra4wPowerNat110_003 hcq4)) hz0zeta (Or.inr (by exact astra4wPowerNat110_004 hcq3 hcq0 hcq4)) hz0theta
  have hct0 := kappaQuarticChamberFace12810_coeff_top_S13 hAne hBne hDne hEne (C := C) (F := F) (G := G) (by exact astra4wPowerNat110_005 hcq3 hcq1)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_233 hcq3 h hcq0 hcq4 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat110_099 hcq3 h hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_100 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_101 hcq3 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_102 hcq3 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_103 hcq3 h hcq0 hAC hCn hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_282 hcq3 h hcq1 hcq0 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_283 hcq3 h hcq0 hcq4 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_106 hcq3 h hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_107 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_108 hcq3 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_109 hcq3 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_284 hcq3 h hcq0 hCn hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_111 hcq3 h hcq1 hcq0 hcq4)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_285 hcq3 h hcq0 hcq4 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_113 hcq3 h hcq0 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_114 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_115 h hcq3 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_116 hcq3 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_286 hcq3 h hcq0 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_118 hcq3 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_119 hcq3 h hcq0 hAC hCn hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_120 h hcq0 hcq4)
  have hr1 : (muQuarticChamberRest17810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest17810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz hGz (by exact astra4wPowerNat110_006 hcq3 hcq0 hcq4) (by exact astra4wPowerNat110_007 hcq3 hcq1 hcq0 hcq4) (by exact astra4wPowerNat110_008 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat110_272 hcq3 hcq0 hcq4)) hz1delta (Or.inr (by exact astra4wPowerNat110_010 hcq3 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat110_011 hcq3 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat110_012 hcq3 hcq0 hcq4))
  have hct1 := muQuarticChamberFace17810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat110_013 hcq0) (by exact hcq2.symm)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_246 hcq3 h hcq1 hcq0 hcq4 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat110_122 hcq3 h hcq1 hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_123 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_124 hcq3 h hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_125 hcq3 h hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_126 hcq3 h hcq1 hcq0 hAC hCn hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_287 hcq3 h hcq1 hcq0 hcq4)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_288 hcq3 h hcq1 hcq0 hcq4 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_129 hcq3 h hcq1 hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_130 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_131 hcq3 hcq1 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_132 hcq3 h hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_289 hcq3 h hcq1 hcq0 hCn hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_134 hcq3 h hcq1 hcq0 hcq4)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_290 hcq3 h hcq1 hcq0 hcq4 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_136 hcq3 h hcq1 hcq0 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_137 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_138 h hcq3 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_139 hcq3 h hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_291 hcq3 h hcq1 hcq0 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_141 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_142 hcq3 h hcq1 hcq0 hAC hCn hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_143 h hcq3 hcq1 hcq0 hcq4)
  have hr2 : (xiQuarticChamberRest18810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest18810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hCz hGz (by exact astra4wPowerNat110_014 hcq3 hcq1 hcq4) (by exact astra4wPowerNat110_015 hcq3 hcq1 hcq4) (by exact astra4wPowerNat110_017 hcq4) (by exact astra4wPowerNat110_019 hcq3 hcq1 hcq4) hz2l hz2beta (Or.inr (by exact astra4wPowerNat110_020 hcq3 hcq1 hcq0 hcq4)) hz2delta (Or.inr (by exact astra4wPowerNat110_273 hcq3 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat110_022 hcq3 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat110_023 hcq3 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat110_024 hcq3 hcq1 hcq4))
  have hct2 := xiQuarticChamberFace18810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat110_025 hcq3 hcq1 hcq0)
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
  have hz3l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_259 hcq3 h hcq0 hcq4 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat110_145 hcq3 h hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_146 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_147 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_148 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_149 hcq3 h hcq0 hAC hCn hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_292 hcq3 h hcq1 hcq0 hcq4)
  have hz3beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_293 hcq3 h hcq0 hcq4 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_152 hcq3 h hcq0 hAC hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_153 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_154 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_155 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_294 hcq3 h hcq0 hCn hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_157 hcq3 h hcq1 hcq0 hcq4)
  have hz3delta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_295 hcq3 h hcq0 hcq4 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_159 hcq3 h hcq0 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_160 hcq3 h hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_161 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_162 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_296 hcq3 h hcq0 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_164 hcq3 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat110_165 hcq3 h hcq0 hAC hCn hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_166 h hcq3 hcq1 hcq0 hcq4)
  have hr3 : (piQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest10810_natDegree_lt_of_live_BDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hCz hGz (by exact astra4wPowerNat110_026 hcq4) (by exact astra4wPowerNat110_028 hcq0 hcq4) (by exact astra4wPowerNat110_029 hcq4) (by exact astra4wPowerNat110_031 hcq3 hcq1 hcq0 hcq4) (by exact astra4wPowerNat110_032 hcq3 hcq1 hcq4) hz3l hz3beta (Or.inr (by exact astra4wPowerNat110_034 hcq3 hcq1 hcq0 hcq4)) hz3delta (Or.inr (by exact astra4wPowerNat110_035 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat110_036 hcq3 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat110_274 hcq3 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat110_038 hcq0 hcq4))
  have hct3 := piQuarticChamberFace10810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat110_039 hcq3 hcq1) (by exact astra4wPowerNat110_040 hcq3)
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
/-- Chamber `BCDEF` / `BF·DD·DE·EE·BBB` dies on power system `S13` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEF20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF20810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_204 hcq3 h hcq0 hcq5 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat110_042 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_043 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_044 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_205 hcq3 h hcq1 hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_046 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_206 hcq3 h hcq8 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_207 h hcq8 hcq0 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_208 hcq3 h hcq1 hcq8 hcq0 hcq5)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_209 hcq4 hcq3 h hcq0 hcq5 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_051 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_052 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_053 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_210 hcq3 h hcq1 hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_055 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_211 hcq3 h hcq8 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_212 h hcq8 hcq0 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_213 hcq3 h hcq1 hcq8 hcq0 hcq5)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_214 hcq4 hcq3 h hcq0 hcq5 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_060 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_061 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_062 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_215 hcq3 h hcq1 hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_064 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_216 hcq3 h hcq8 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_217 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_067 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_218 hcq3 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_069 hcq3 h hcq0 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_219 hcq3 h hcq1 hcq8 hcq0 hcq5)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_220 hcq4 hcq3 h hcq0 hcq5 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_072 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_073 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_074 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_221 hcq3 h hcq1 hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_076 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_222 hcq3 h hcq8 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_223 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_079 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_224 hcq3 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_081 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_082 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_225 hcq3 h hcq8 hcq0 hcq5)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_226 h hcq8 hcq0 hcq5)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_227 h hcq3 hcq0 hcq5 hGn)
    · exact Or.inr (by exact astra4wPowerNat110_085 h hcq3 hcq1 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_086 h hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_087 h hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_228 h hcq3 hcq1 hcq8 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_089 h hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_229 h hcq3 hcq8 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_230 h hcq8 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_092 h hcq3 hcq1 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_231 h hcq3 hcq8 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_094 h hcq3 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_095 h hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_232 h hcq8 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_097 h hcq3 hcq0 hcq5)
  have hr0 : (kappaQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest12810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hGz (by exact astra4wPowerNat110_000 hcq5) (by exact astra4wPowerNat110_167 hcq3 hcq8) (by exact astra4wPowerNat110_168 hcq3 hcq8) hz0l hz0beta (Or.inr (by exact astra4wPowerNat110_169 hcq3 hcq8)) hz0delta (Or.inr (by exact astra4wPowerNat110_170 hcq3 hcq8 hcq0)) hz0zeta (Or.inr (by exact astra4wPowerNat110_171 hcq3 hcq8)) hz0theta
  have hct0 := kappaQuarticChamberFace12810_coeff_top_S13 hAne hBne hDne hEne (C := C) (F := F) (G := G) (by exact astra4wPowerNat110_005 hcq3 hcq1)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_233 hcq3 h hcq0 hcq5 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat110_234 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_100 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_101 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_102 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_235 h hcq8 hcq0 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_236 hcq3 h hcq1 hcq8 hcq0 hcq5)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_237 hcq4 hcq3 h hcq0 hcq5 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_238 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_107 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_108 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_109 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_239 h hcq8 hcq0 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_240 hcq3 h hcq1 hcq8 hcq0 hcq5)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_241 hcq4 hcq3 h hcq0 hcq5 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_242 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_114 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_115 h hcq3 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_116 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_243 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_118 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_244 hcq3 h hcq8 hcq0 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_245 h hcq8 hcq0 hcq5)
  have hr1 : (muQuarticChamberRest17810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest17810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hGz (by exact astra4wPowerNat110_172 hcq8) (by exact astra4wPowerNat110_006 hcq3 hcq0 hcq5) (by exact astra4wPowerNat110_007 hcq3 hcq1 hcq0 hcq5) (by exact astra4wPowerNat110_173 hcq8 hcq5) (by exact astra4wPowerNat110_174 hcq3 hcq8) (by exact astra4wPowerNat110_008 hcq5) hz1l hz1beta (Or.inr (by exact astra4wPowerNat110_175 hcq3 hcq8 hcq5)) hz1delta (Or.inr (by exact astra4wPowerNat110_176 hcq3 hcq1 hcq8 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_177 hcq3 hcq8 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_178 hcq3 hcq8)) (Or.inr (by exact astra4wPowerNat110_179 hcq3 hcq8 hcq0 hcq5))
  have hct1 := muQuarticChamberFace17810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat110_013 hcq0) (by exact hcq2.symm)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_246 hcq3 h hcq1 hcq0 hcq5 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat110_247 hcq3 h hcq1 hcq8 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_123 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_124 hcq3 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_125 hcq3 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_248 hcq3 h hcq1 hcq8 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_249 hcq3 h hcq1 hcq8 hcq0 hcq5)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_250 hcq4 hcq3 h hcq1 hcq0 hcq5 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_251 hcq3 h hcq1 hcq8 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_130 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_131 hcq3 hcq1 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_132 hcq3 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_252 hcq3 h hcq1 hcq8 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_253 hcq3 h hcq1 hcq8 hcq0 hcq5)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_254 hcq4 hcq3 h hcq1 hcq0 hcq5 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_255 hcq3 h hcq1 hcq8 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_137 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_138 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_139 hcq3 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_256 hcq3 h hcq1 hcq8 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_141 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_257 hcq3 h hcq1 hcq8 hcq0 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_258 h hcq3 hcq1 hcq8 hcq0 hcq5)
  have hr2 : (xiQuarticChamberRest18810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest18810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hGz (by exact astra4wPowerNat110_014 hcq3 hcq1 hcq5) (by exact astra4wPowerNat110_180 hcq3 hcq1 hcq8 hcq0) (by exact astra4wPowerNat110_015 hcq3 hcq1 hcq5) (by exact astra4wPowerNat110_181 hcq3 hcq1 hcq8 hcq5) (by exact astra4wPowerNat110_182 hcq3 hcq1 hcq8 hcq5) (by exact astra4wPowerNat110_017 hcq5) (by exact astra4wPowerNat110_183 hcq3 hcq8) (by exact astra4wPowerNat110_184 hcq3 hcq1 hcq8 hcq0 hcq5) (by exact astra4wPowerNat110_019 hcq3 hcq1 hcq5) hz2l hz2beta (Or.inr (by exact astra4wPowerNat110_185 hcq3 hcq1 hcq8 hcq0 hcq5)) hz2delta (Or.inr (by exact astra4wPowerNat110_186 hcq3 hcq1 hcq8 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_187 hcq3 hcq1 hcq8 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_188 hcq3 hcq1 hcq8 hcq5)) (Or.inr (by exact astra4wPowerNat110_189 hcq3 hcq1 hcq8 hcq0 hcq5))
  have hct2 := xiQuarticChamberFace18810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat110_025 hcq3 hcq1 hcq0)
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_259 hcq3 h hcq0 hcq5 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat110_260 hcq3 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_146 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_147 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_148 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_261 hcq3 h hcq8 hcq0 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_262 hcq3 h hcq1 hcq8 hcq0 hcq5)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_263 hcq4 hcq3 h hcq0 hcq5 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_264 hcq3 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_153 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_154 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_155 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_265 hcq3 h hcq8 hcq0 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_266 hcq3 h hcq1 hcq8 hcq0 hcq5)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_267 hcq4 hcq3 h hcq0 hcq5 hGn)
      · exact Or.inr (by exact astra4wPowerNat110_268 hcq3 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_160 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_161 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_162 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_269 hcq3 h hcq8 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_164 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_270 hcq3 h hcq8 hcq0 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_271 h hcq3 hcq1 hcq8 hcq0 hcq5)
  have hr3 : (piQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest10810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hGz (by exact astra4wPowerNat110_026 hcq5) (by exact astra4wPowerNat110_190 hcq3 hcq8) (by exact astra4wPowerNat110_191 hcq8 hcq0 hcq5) (by exact astra4wPowerNat110_192 hcq3 hcq8) (by exact astra4wPowerNat110_193 hcq3 hcq8 hcq0) (by exact astra4wPowerNat110_028 hcq0 hcq5) (by exact astra4wPowerNat110_194 hcq3 hcq1 hcq8 hcq0 hcq5) (by exact astra4wPowerNat110_029 hcq5) (by exact astra4wPowerNat110_195 hcq3 hcq8 hcq5) (by exact astra4wPowerNat110_196 hcq3 hcq8) (by exact astra4wPowerNat110_031 hcq3 hcq1 hcq0 hcq5) (by exact astra4wPowerNat110_197 hcq3 hcq8 hcq5) (by exact astra4wPowerNat110_198 hcq3 hcq1 hcq8 hcq0) (by exact astra4wPowerNat110_032 hcq3 hcq1 hcq5) hz3l hz3beta (Or.inr (by exact astra4wPowerNat110_199 hcq3 hcq1 hcq8 hcq0 hcq5)) hz3delta (Or.inr (by exact astra4wPowerNat110_200 hcq3 hcq1 hcq8 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_201 hcq3 hcq1 hcq8 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_202 hcq3 hcq8 hcq5)) (Or.inr (by exact astra4wPowerNat110_203 hcq3 hcq8 hcq0 hcq5))
  have hct3 := piQuarticChamberFace10810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat110_039 hcq3 hcq1) (by exact astra4wPowerNat110_040 hcq3)
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
/-- Chamber `BDEFG` / `BF·DD·DE·EE·BBB` dies on power system `S13` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBDEFG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG19810 A B C D E F G)
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
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_041 hcq3 hcq4 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_042 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_043 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_044 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_045 hcq3 h hcq1 hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_046 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_047 hcq3 h hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_048 hcq3 h hcq0 hAC hCn hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_049 hcq3 hcq4 h hcq1 hcq0 hcq5)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_050 hcq3 hcq4 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_051 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_052 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_053 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_054 hcq3 h hcq1 hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_055 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_056 hcq3 h hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_057 hcq3 h hcq0 hAC hCn hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_058 hcq3 hcq4 h hcq1 hcq0 hcq5)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_059 hcq3 hcq4 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_060 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_061 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_062 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_063 hcq3 h hcq1 hcq0 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_064 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_065 hcq3 hcq4 h hcq0 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_066 hcq3 h hcq0 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_067 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_068 hcq3 h hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_069 hcq3 h hcq0 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_070 hcq3 h hcq1 hcq0 hcq5)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_071 hcq3 hcq4 h hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_072 hcq3 h hcq1 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_073 h hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_074 h hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_075 hcq3 h hcq1 hcq0 hCn hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_076 h hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_077 hcq3 hcq4 h hcq0 hCn hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_078 hcq3 h hcq0 hCn hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_079 hcq3 h hcq1 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_080 hcq3 h hcq0 hAC hCn hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_081 hcq3 h hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_082 hcq3 h hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_083 hcq3 h hcq0 hAC hCn hcq5)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_084 h hcq3 hcq4 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_085 h hcq3 hcq1 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_086 h hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_087 h hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_088 h hcq3 hcq1 hcq0 hCn hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_089 h hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_090 h hcq3 hcq0 hCn hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_091 h hcq3 hcq0 hCn hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_092 h hcq3 hcq1 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_093 h hcq3 hcq0 hCn hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_094 h hcq3 hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_095 h hcq0 hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_096 h hcq3 hcq0 hAC hCn hcq5)
    · exact Or.inr (by exact astra4wPowerNat110_097 h hcq3 hcq0 hcq5)
  have hr0 : (kappaQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest12810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz (by exact astra4wPowerNat110_000 hcq5) (by exact astra4wPowerNat110_001 hcq3 hcq4) hz0l hz0beta (Or.inr (by exact astra4wPowerNat110_002 hcq3 hcq0 hcq5)) hz0delta (Or.inr (by exact astra4wPowerNat110_003 hcq5)) hz0zeta (Or.inr (by exact astra4wPowerNat110_004 hcq3 hcq0 hcq5)) hz0theta
  have hct0 := kappaQuarticChamberFace12810_coeff_top_S13 hAne hBne hDne hEne (C := C) (F := F) (G := G) (by exact astra4wPowerNat110_005 hcq3 hcq1)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_098 hcq3 hcq4 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_099 hcq3 h hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_100 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_101 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_102 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_103 hcq3 h hcq0 hAC hCn hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_104 hcq3 hcq4 h hcq1 hcq0 hcq5)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_105 hcq3 hcq4 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_106 hcq3 h hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_107 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_108 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_109 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_110 hcq3 hcq4 h hcq0 hCn hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_111 hcq3 h hcq1 hcq0 hcq5)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_112 hcq3 hcq4 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_113 hcq3 h hcq0 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_114 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_115 h hcq3 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_116 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_117 hcq3 hcq4 h hcq0 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_118 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_119 hcq3 h hcq0 hAC hCn hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_120 h hcq0 hcq5)
  have hr1 : (muQuarticChamberRest17810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest17810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz (by exact astra4wPowerNat110_006 hcq3 hcq0 hcq5) (by exact astra4wPowerNat110_007 hcq3 hcq1 hcq0 hcq5) (by exact astra4wPowerNat110_008 hcq5) hz1l hz1beta (Or.inr (by exact astra4wPowerNat110_009 hcq3 hcq4 hcq0 hcq5)) hz1delta (Or.inr (by exact astra4wPowerNat110_010 hcq3 hcq1 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_011 hcq3 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_012 hcq3 hcq0 hcq5))
  have hct1 := muQuarticChamberFace17810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat110_013 hcq0) (by exact hcq2.symm)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_121 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_122 hcq3 h hcq1 hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_123 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_124 hcq3 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_125 hcq3 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_126 hcq3 h hcq1 hcq0 hAC hCn hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_127 hcq3 hcq4 h hcq1 hcq0 hcq5)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_128 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_129 hcq3 h hcq1 hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_130 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_131 hcq3 hcq1 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_132 hcq3 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_133 hcq3 hcq4 h hcq1 hcq0 hCn hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_134 hcq3 h hcq1 hcq0 hcq5)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_135 hcq4 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_136 hcq3 h hcq1 hcq0 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_137 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_138 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_139 hcq3 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_140 hcq3 hcq4 h hcq1 hcq0 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_141 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_142 hcq3 h hcq1 hcq0 hAC hCn hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_143 h hcq3 hcq1 hcq0 hcq5)
  have hr2 : (xiQuarticChamberRest18810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest18810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hCz (by exact astra4wPowerNat110_014 hcq3 hcq1 hcq5) (by exact astra4wPowerNat110_015 hcq3 hcq1 hcq5) (by exact astra4wPowerNat110_016 hcq4 hcq1 hcq5) (by exact astra4wPowerNat110_017 hcq5) (by exact astra4wPowerNat110_018 hcq3 hcq4) (by exact astra4wPowerNat110_019 hcq3 hcq1 hcq5) hz2l hz2beta (Or.inr (by exact astra4wPowerNat110_020 hcq3 hcq1 hcq0 hcq5)) hz2delta (Or.inr (by exact astra4wPowerNat110_021 hcq3 hcq4 hcq1 hcq5)) (Or.inr (by exact astra4wPowerNat110_022 hcq3 hcq1 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_023 hcq3 hcq1 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_024 hcq3 hcq1 hcq5))
  have hct2 := xiQuarticChamberFace18810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat110_025 hcq3 hcq1 hcq0)
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
  have hz3l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_144 hcq3 hcq4 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_145 hcq3 h hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_146 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_147 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_148 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_149 hcq3 h hcq0 hAC hCn hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_150 hcq3 hcq4 h hcq1 hcq0 hcq5)
  have hz3beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_151 hcq3 hcq4 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_152 hcq3 h hcq0 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_153 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_154 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_155 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_156 hcq3 hcq4 h hcq0 hCn hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_157 hcq3 h hcq1 hcq0 hcq5)
  have hz3delta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat110_158 hcq3 hcq4 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_159 hcq3 h hcq0 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_160 hcq3 h hcq1 hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_161 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_162 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_163 hcq3 hcq4 h hcq0 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_164 hcq3 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat110_165 hcq3 h hcq0 hAC hCn hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat110_166 h hcq3 hcq1 hcq0 hcq5)
  have hr3 : (piQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest10810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hCz (by exact astra4wPowerNat110_026 hcq5) (by exact astra4wPowerNat110_027 hcq3 hcq4) (by exact astra4wPowerNat110_028 hcq0 hcq5) (by exact astra4wPowerNat110_029 hcq5) (by exact astra4wPowerNat110_030 hcq3 hcq4 hcq5) (by exact astra4wPowerNat110_031 hcq3 hcq1 hcq0 hcq5) (by exact astra4wPowerNat110_032 hcq3 hcq1 hcq5) (by exact astra4wPowerNat110_033 hcq3 hcq4) hz3l hz3beta (Or.inr (by exact astra4wPowerNat110_034 hcq3 hcq1 hcq0 hcq5)) hz3delta (Or.inr (by exact astra4wPowerNat110_035 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_036 hcq3 hcq1 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_037 hcq3 hcq4 hcq0 hcq5)) (Or.inr (by exact astra4wPowerNat110_038 hcq0 hcq5))
  have hct3 := piQuarticChamberFace10810_coeff_top_S13 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat110_039 hcq3 hcq1) (by exact astra4wPowerNat110_040 hcq3)
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
