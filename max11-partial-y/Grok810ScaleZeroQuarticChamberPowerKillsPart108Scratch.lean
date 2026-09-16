import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
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
private theorem astra4wPowerNat108_000
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_001
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + g < a + b + f)
    : b + g < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_002
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    : d + e < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_003
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_004
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_005
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_006
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : b + 2 * c = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_007
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : c + f = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_008
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 4 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_009
    {a b c d f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    : a + 2 * d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_010
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + e < a + f)
    : 2 * b + e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_011
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b + c + d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_012
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + g < a + b + f)
    : c + g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_013
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : d + f < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_014
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) ∧ g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_015
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_016
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a + b < (a + 2 * b + c) ∧ d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_017
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_018
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_019
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : a + b + f = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_020
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : 3 * c = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_021
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    : 2 * e = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_022
    {a b e f : ℕ}
    (h0 : a + b + f = 2 * e)
    (h1 : b + e < a + f)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_023
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    : a + b + c + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_024
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_025
    {a b c e f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_026
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    : a + d + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_027
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : c + g < a + b + f)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_028
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_029
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b + d + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_030
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_031
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + g < a + b + f)
    : e + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_032
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_033
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_034
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_035
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_036
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_037
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_038
    {a b c e : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : 2 * c + e = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_039
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_040
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ e + f)
    (h2 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_041
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_042
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 2 * b + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_043
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_044
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ b + 2 * d)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_045
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ 2 * c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_046
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_047
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_048
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_049
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ e + f)
    (h2 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_050
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_051
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_052
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_053
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_054
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ 2 * c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_055
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_056
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_057
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ d + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_058
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ e + f)
    (h2 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_059
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_060
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_061
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_062
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + 2 * d)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_063
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_064
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_065
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + e)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_066
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_067
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_068
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_069
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ d + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_070
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_071
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_072
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_073
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_074
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + 2 * d)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_075
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ 2 * c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_076
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_077
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_078
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_079
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : a ≤ b)
    (h3 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_080
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_081
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_082
    {a b c e f : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_083
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_084
    {a b e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_085
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : a ≤ 2 * b + d)
    (h4 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_086
    {a b e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_087
    {a b c e f : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_088
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_089
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_090
    {a b c e f : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_091
    {a b e f : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_092
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_093
    {a b e f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_094
    {a b e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_095
    {a b c e f : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_096
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_097
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_098
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_099
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ d + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_100
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_101
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_102
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_103
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a + b < a + 2 * b + c)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_104
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_105
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_106
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ d + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_107
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : a ≤ b)
    (h4 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_108
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_109
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_110
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a + b < a + 2 * b + c)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_111
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_112
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_113
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ d + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_114
    {a b c e f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_115
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_116
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_117
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_118
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_119
    {a b c d e f : ℕ}
    (h0 : 2 * a + b < a + 2 * b + c)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_120
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 5 * a ≤ 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_121
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 7 * a ≤ 4 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_122
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 9 * a ≤ 4 * d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_123
    {a b c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_124
    {a b c d e f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_125
    {a b c d e f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_126
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_127
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 3 * a ≤ 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_128
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 5 * a ≤ 4 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_129
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 7 * a ≤ 4 * d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_130
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 9 * a ≤ 4 * e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_131
    {a b c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_132
    {a b c d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_133
    {a b c d e f : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_134
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : a + b + f = 2 * e)
    (h2 : a ≤ 4 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_135
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 3 * a ≤ 4 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_136
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ 4 * d)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_137
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 7 * a ≤ 4 * e)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_138
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 9 * a ≤ 4 * f)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_139
    {a b c d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : c + g < a + b + f)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_140
    {a b c d e f : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_141
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_142
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_143
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : c + g < a + b + f)
    : a + 2 * b < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) ∧ g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_144
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_145
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a + b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_146
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_147
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_148
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_149
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a + b + c < (a + 2 * b + e) ∧ 3 * b < (a + 2 * b + e) ∧ a + f < (a + 2 * b + e) ∧ b + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_150
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : c + g < a + b + f)
    : a + 2 * b < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_151
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_152
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_153
    {a b c d e f g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 6 * a ≤ d + g)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : c + g < a + b + f)
    (h7 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_154
    {a b d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : a + b + f = 2 * e)
    (h5 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_155
    {a b d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 6 * a ≤ b + 2 * d)
    (h4 : a + b + f = 2 * e)
    (h5 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_156
    {a b c d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 6 * a ≤ 2 * c + d)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_157
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_158
    {a b c d e f g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 5 * a ≤ d + g)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : c + g < a + b + f)
    (h7 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_159
    {a b d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 4 * a ≤ 2 * b + d)
    (h4 : a + b + f = 2 * e)
    (h5 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_160
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_161
    {a b c d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 5 * a ≤ 2 * c + d)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_162
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_163
    {a b c d e f g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 4 * a ≤ d + g)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : c + g < a + b + f)
    (h7 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_164
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_165
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + 2 * d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_166
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_167
    {a b c d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    (h6 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_168
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_169
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_170
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + 2 * d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_171
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_172
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_173
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_174
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : a ≤ 2 * b + d)
    (h3 : b + e < a + f)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_175
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_176
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_177
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_178
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_179
    {a b c d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 5 * a ≤ d + e)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : d = 0)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_180
    {a b c d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : d = 0)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_181
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    : 4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_182
    {a b c d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 4 * a ≤ d + e)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : d = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_183
    {a b c d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 4 * a ≤ 2 * b + d)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : d = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_184
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_185
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ d + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_186
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_187
    {a b c e f : ℕ}
    (h0 : 2 * a + b < a + 2 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_188
    {a b c e f : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_189
    {a b c e f : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_190
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    (h3 : d = 0)
    : ¬ (9 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_191
    {a b c e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_192
    {a b c e f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_193
    {a b c e f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_194
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + b + c < a + 2 * b + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_195
    {a b c e f : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_196
    {a b c e f : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_197
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    (h3 : d = 0)
    : ¬ (7 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_198
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 9 * a ≤ 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_199
    {a b c e f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_200
    {a b c e f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : c + g < a + b + f)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_201
    {a b c e f : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_202
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_203
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_204
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : d < a + b)
    (h5 : g < 4 * a)
    (h6 : g = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_205
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_206
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : d < a + b)
    (h5 : g < 4 * a)
    (h6 : g = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_207
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_208
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_209
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_210
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    (h5 : g = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_211
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_212
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a + b < a + 2 * b + c)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_213
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_214
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_215
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : g = 0)
    : ¬ (15 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_216
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : b + e < a + f)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_217
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : g = 0)
    : ¬ (13 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat108_218
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : g = 0)
    : ¬ (11 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEF` / `BF·CF·EE·BBB·BBC·BCC·CCC` dies on power system `S10` (carriers κ, μ, ξ). -/
theorem quarticChamberBCDEF13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_204 hcq9 hcq2 h hcq1 hcq8 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat108_040 hcq2 h hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_041 hcq6 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_042 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_043 hcq2 h hcq0 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_044 hcq6 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_045 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_046 hcq2 h hcq0 hcq1 hcq12)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_205 hcq6 hcq2 h hcq0 hcq1 hcq12)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_206 hcq9 hcq2 h hcq1 hcq8 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat108_049 hcq2 h hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_050 hcq6 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_051 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_052 hcq2 h hcq0 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_053 hcq6 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_054 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_055 hcq2 h hcq0 hcq1 hcq12)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_207 hcq6 hcq2 h hcq0 hcq1 hcq12)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_208 hcq9 hcq2 h hcq1 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat108_058 hcq2 h hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_059 hcq6 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_060 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_061 hcq2 h hcq0 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_062 hcq6 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_063 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_064 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_065 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_066 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_067 hcq2 h hcq1 hcq12)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_068 hcq2 h hcq0 hcq1 hcq12)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_209 hcq9 hcq2 h hcq1 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat108_070 hcq2 h hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_071 h hcq6 hcq2 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_072 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_073 hcq2 h hcq0 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_074 hcq6 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_075 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_076 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_077 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_078 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_079 hcq2 hcq1 h hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_080 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_081 hcq2 h hcq0 hcq1 hcq12)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_082 h hcq2 hcq0 hcq1 hcq12)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_210 h hcq6 hcq2 hcq1 hcq12 hGn)
    · exact Or.inr (by exact astra4wPowerNat108_084 h hcq2 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_085 hcq6 hcq2 hcq1 h hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_086 h hcq2 hcq1 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_087 h hcq2 hcq0 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_088 h hcq6 hcq2 hcq1 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_089 h hcq6 hcq2 hcq0 hcq1 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_090 h hcq2 hcq0 hcq1 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_091 h hcq2 hcq1 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_092 h hcq6 hcq2 hcq0 hcq1 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_093 h hcq2 hcq1 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_094 h hcq2 hcq1 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_095 h hcq2 hcq0 hcq1 hcq12)
    · exact Or.inr (by exact astra4wPowerNat108_096 h hcq6 hcq2 hcq1 hcq12)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hGz (by exact astra4wPowerNat108_000 hcq6 hcq2 hcq1 hcq12) (by exact astra4wPowerNat108_002 hcq6 hcq2 hcq1) hz0l hz0beta (Or.inr (by exact astra4wPowerNat108_003 hcq6 hcq2 hcq0 hcq1 hcq12)) hz0delta (Or.inr (by exact astra4wPowerNat108_004 hcq6 hcq2 hcq1 hcq12)) hz0zeta (Or.inr (by exact astra4wPowerNat108_005 hcq6 hcq2 hcq1 hcq12)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top_S10 hAne hBne hCne hFne (D := D) (E := E) (G := G) (by exact astra4wPowerNat108_006 hcq0) (by exact astra4wPowerNat108_007 hcq2 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_211 hcq9 hcq2 h hcq0 hcq1 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat108_098 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_099 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_100 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_101 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_102 hcq2 h hcq0 hcq1 hcq12)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_212 hcq6 hcq2 h hcq0 hcq1 hcq12)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_213 hcq9 hcq2 h hcq0 hcq1 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat108_105 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_106 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_107 hcq2 hcq0 hcq1 h hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_108 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_109 hcq2 h hcq0 hcq1 hcq12)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_110 hcq6 hcq2 h hcq0 hcq1 hcq12)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_214 hcq9 hcq2 h hcq0 hcq1 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat108_112 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_113 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_114 h hcq2 hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_115 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_116 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_117 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_118 hcq2 h hcq0 hcq1 hcq12)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_119 h hcq6 hcq2 hcq0 hcq1 hcq12)
  have hr1 : (muQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest15810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hGz (by exact astra4wPowerNat108_008 hcq2 hcq0 hcq1 hcq12) (by exact astra4wPowerNat108_009 hcq6 hcq2 hcq0) (by exact astra4wPowerNat108_010 hcq2 hcq0 hcq12) (by exact astra4wPowerNat108_011 hcq6 hcq2 hcq1 hcq12) (by exact astra4wPowerNat108_013 hcq6 hcq2 hcq0 hcq1 hcq12) hz1l hz1beta (Or.inr (by exact astra4wPowerNat108_202 hcq6 hcq2 hcq0 hcq1 hcq12)) hz1delta (Or.inr (by exact astra4wPowerNat108_015 hcq6 hcq2 hcq0 hcq1 hcq12)) (Or.inr (by exact astra4wPowerNat108_016 hcq6 hcq2 hcq0 hcq1 hcq12)) (Or.inr (by exact astra4wPowerNat108_017 hcq6 hcq2 hcq1 hcq12)) (Or.inr (by exact astra4wPowerNat108_018 hcq6 hcq2 hcq0 hcq1 hcq12))
  have hct1 := muQuarticChamberFace15810_coeff_top_S10 hAne hBne hCne hEne hFne (D := D) (G := G) (by exact astra4wPowerNat108_019 hcq2 hcq0) (by exact astra4wPowerNat108_020 hcq0) (by exact astra4wPowerNat108_021 hcq2 hcq0 hcq1)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face15_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_120 hcq6 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_121 hcq6 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_122 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_123 h hcq6 hcq2 hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_124 h hcq6 hcq2 hcq0 hcq1 hcq12)
      · exact absurd h (by exact astra4wPowerNat108_215 hcq6 hcq2 hcq1 hcq12 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_216 hcq6 hcq2 h hcq0 hcq1 hcq12)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_127 hcq6 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_128 hcq6 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_129 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_130 hcq6 hcq2 h hcq0 hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_131 h hcq6 hcq2 hcq0 hcq1 hcq12)
      · exact absurd h (by exact astra4wPowerNat108_217 hcq6 hcq2 hcq1 hcq12 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_133 h hcq2 hcq0 hcq1 hcq12)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_134 hcq6 hcq1 h)
      · exact Or.inr (by exact astra4wPowerNat108_135 hcq6 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat108_136 hcq6 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_137 hcq6 hcq2 h hcq1 hcq12)
      · exact Or.inr (by exact astra4wPowerNat108_138 hcq6 hcq2 h hcq1 hcq12)
      · exact absurd h (by exact astra4wPowerNat108_218 hcq6 hcq2 hcq1 hcq12 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_140 h hcq2 hcq0 hcq1 hcq12)
  have hr2 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hGz (by exact astra4wPowerNat108_022 hcq1 hcq12) (by exact astra4wPowerNat108_023 hcq6 hcq0 hcq1) (by exact astra4wPowerNat108_024 hcq6 hcq2 hcq1 hcq12) (by exact astra4wPowerNat108_025 hcq0 hcq1 hcq12) (by exact astra4wPowerNat108_026 hcq6 hcq2 hcq1) (by exact astra4wPowerNat108_028 hcq2 hcq0 hcq1 hcq12) (by exact astra4wPowerNat108_029 hcq6 hcq2 hcq1 hcq12) (by exact astra4wPowerNat108_030 hcq6 hcq2 hcq0 hcq1 hcq12) (by exact astra4wPowerNat108_032 hcq2 hcq1 hcq12) hz2l hz2beta (Or.inr (by exact astra4wPowerNat108_033 hcq6 hcq2 hcq0 hcq1 hcq12)) hz2delta (Or.inr (by exact astra4wPowerNat108_203 hcq6 hcq2 hcq0 hcq1 hcq12)) (Or.inr (by exact astra4wPowerNat108_035 hcq6 hcq2 hcq0 hcq1 hcq12)) (Or.inr (by exact astra4wPowerNat108_036 hcq6 hcq2 hcq1 hcq12)) (Or.inr (by exact astra4wPowerNat108_037 hcq6 hcq2 hcq1 hcq12))
  have hct2 := xiQuarticChamberFace5810_coeff_top_S10 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat108_038 hcq0)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS10810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hEc


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
/-- Chamber `BCEFG` / `BF·CF·EE·BBB·BBC·BCC·CCC` dies on power system `S10` (carriers κ, μ, ξ). -/
theorem quarticChamberBCEFG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG19810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_153 hAD hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_040 hcq2 h hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_154 hAD hcq8 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_042 hcq2 h hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_043 hcq2 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_155 hAD hcq8 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_156 hAD hcq8 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_046 hcq2 h hcq0 hcq1 hcq13)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_157 hcq2 h hcq0 hcq1 hcq13 hcq7)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_158 hAD hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_049 hcq2 h hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_159 hAD hcq8 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_051 hcq2 h hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_052 hcq2 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_160 hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_161 hAD hcq8 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_055 hcq2 h hcq0 hcq1 hcq13)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_162 hcq2 h hcq0 hcq1 hcq13 hcq7)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_163 hAD hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_058 hcq2 h hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_164 hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_060 hcq2 h hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_061 hcq2 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_165 hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_166 hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_064 hcq2 h hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_065 hcq2 h hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_167 hAD hcq2 h hcq0 hcq1 hcq13 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_067 hcq2 h hcq1 hcq13)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_068 hcq2 h hcq0 hcq1 hcq13)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_168 hcq2 h hcq0 hcq1 hcq13 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_070 hcq2 h hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_169 h hcq2 hcq1 hcq13 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_072 hcq2 h hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_073 hcq2 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_170 hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_171 hcq2 h hcq0 hcq1 hcq13 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_076 hcq2 h hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_077 hcq2 h hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_172 hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_079 hcq2 hcq1 h hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_080 hcq2 h hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_081 hcq2 h hcq0 hcq1 hcq13)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_082 h hcq2 hcq0 hcq1 hcq13)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_173 h hcq2 hcq0 hcq1 hcq13 hcq7 hDn)
    · exact Or.inr (by exact astra4wPowerNat108_084 h hcq2 hcq13)
    · exact Or.inr (by exact astra4wPowerNat108_174 hcq2 hcq1 h hcq13 hDn)
    · exact Or.inr (by exact astra4wPowerNat108_086 h hcq2 hcq1 hcq13)
    · exact Or.inr (by exact astra4wPowerNat108_087 h hcq2 hcq0 hcq13)
    · exact Or.inr (by exact astra4wPowerNat108_175 h hcq2 hcq1 hcq13 hDn)
    · exact Or.inr (by exact astra4wPowerNat108_176 h hcq2 hcq0 hcq1 hcq13 hDn)
    · exact Or.inr (by exact astra4wPowerNat108_090 h hcq2 hcq0 hcq1 hcq13)
    · exact Or.inr (by exact astra4wPowerNat108_091 h hcq2 hcq1 hcq13)
    · exact Or.inr (by exact astra4wPowerNat108_177 h hcq2 hcq0 hcq1 hcq13 hDn)
    · exact Or.inr (by exact astra4wPowerNat108_093 h hcq2 hcq1 hcq13)
    · exact Or.inr (by exact astra4wPowerNat108_094 h hcq2 hcq1 hcq13)
    · exact Or.inr (by exact astra4wPowerNat108_095 h hcq2 hcq0 hcq1 hcq13)
    · exact Or.inr (by exact astra4wPowerNat108_178 h hcq2 hcq1 hcq13 hDn)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by exact astra4wPowerNat108_001 hcq2 hcq0 hcq7) hz0l hz0beta (Or.inr (by exact astra4wPowerNat108_141 hcq2 hcq0 hcq1 hcq13)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat108_142 hcq2 hcq1 hcq13)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top_S10 hAne hBne hCne hFne (D := D) (E := E) (G := G) (by exact astra4wPowerNat108_006 hcq0) (by exact astra4wPowerNat108_007 hcq2 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_097 hcq2 h hcq0 hcq1 hcq13 hcq7)
      · exact Or.inr (by exact astra4wPowerNat108_098 hcq2 h hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_179 hAD hcq8 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_100 hcq2 h hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_180 hAD hcq8 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_102 hcq2 h hcq0 hcq1 hcq13)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_181 hcq2 h hcq0 hcq1 hcq13 hcq7)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_104 hcq2 h hcq0 hcq1 hcq13 hcq7)
      · exact Or.inr (by exact astra4wPowerNat108_105 hcq2 h hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_182 hAD hcq8 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_107 hcq2 hcq0 hcq1 h hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_183 hAD hcq8 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_109 hcq2 h hcq0 hcq1 hcq13)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_184 hcq2 h hcq0 hcq1 hcq13)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_111 hcq2 h hcq0 hcq1 hcq13 hcq7)
      · exact Or.inr (by exact astra4wPowerNat108_112 hcq2 h hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_185 hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_114 h hcq2 hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_186 hcq8 hcq2 h hcq0 hcq1 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_116 hcq2 h hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_117 hcq2 h hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_118 hcq2 h hcq0 hcq1 hcq13)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_187 h hcq2 hcq0 hcq1 hcq13)
  have hr1 : (muQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest15810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by exact astra4wPowerNat108_008 hcq2 hcq0 hcq1 hcq13) (by exact astra4wPowerNat108_010 hcq2 hcq0 hcq13) (by exact astra4wPowerNat108_012 hcq2 hcq0 hcq7) hz1l hz1beta (Or.inr (by exact astra4wPowerNat108_143 hcq2 hcq0 hcq1 hcq13 hcq7)) hz1delta (Or.inr (by exact astra4wPowerNat108_144 hcq2 hcq0 hcq1 hcq13)) (Or.inr (by exact astra4wPowerNat108_145 hcq2 hcq0 hcq1 hcq13)) (Or.inr (by exact astra4wPowerNat108_146 hcq2 hcq1 hcq13)) (Or.inr (by exact astra4wPowerNat108_147 hcq2 hcq0 hcq1 hcq13))
  have hct1 := muQuarticChamberFace15810_coeff_top_S10 hAne hBne hCne hEne hFne (D := D) (G := G) (by exact astra4wPowerNat108_019 hcq2 hcq0) (by exact astra4wPowerNat108_020 hcq0) (by exact astra4wPowerNat108_021 hcq2 hcq0 hcq1)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face15_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_188 h hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_189 h hcq0 hcq1 hcq13)
      · exact absurd h (by exact astra4wPowerNat108_190 hcq2 hcq1 hcq13 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_191 h hcq2 hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_192 h hcq2 hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_193 h hcq2 hcq0 hcq1 hcq13 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_194 hcq2 h hcq0 hcq1 hcq13)
  have hz2beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_195 h hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_196 h hcq0 hcq1 hcq13)
      · exact absurd h (by exact astra4wPowerNat108_197 hcq2 hcq1 hcq13 hDn)
      · exact Or.inr (by exact astra4wPowerNat108_198 hcq2 h hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_199 h hcq2 hcq0 hcq1 hcq13)
      · exact Or.inr (by exact astra4wPowerNat108_200 h hcq2 hcq0 hcq1 hcq13 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_201 h hcq2 hcq0 hcq1 hcq13)
  have hr2 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz (by exact astra4wPowerNat108_022 hcq1 hcq13) (by exact astra4wPowerNat108_025 hcq0 hcq1 hcq13) (by exact astra4wPowerNat108_027 hcq2 hcq0 hcq1 hcq13 hcq7) (by exact astra4wPowerNat108_028 hcq2 hcq0 hcq1 hcq13) (by exact astra4wPowerNat108_031 hcq2 hcq0 hcq7) (by exact astra4wPowerNat108_032 hcq2 hcq1 hcq13) hz2l hz2beta (Or.inr (by exact astra4wPowerNat108_148 hcq2 hcq0 hcq1 hcq13)) (Or.inr (by exact astra4wPowerNat108_149 hcq2 hcq0 hcq1 hcq13)) (Or.inr (by exact astra4wPowerNat108_150 hcq2 hcq0 hcq1 hcq13 hcq7)) (Or.inr (by exact astra4wPowerNat108_151 hcq2 hcq0 hcq1 hcq13)) (Or.inr (by exact astra4wPowerNat108_152 hcq2 hcq1 hcq13))
  have hct2 := xiQuarticChamberFace5810_coeff_top_S10 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat108_038 hcq0)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS10810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hEc


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
/-- Chamber `BCDEFG` / `BF·CF·EE·BBB·BBC·BCC·CCC` dies on power system `S10` (carriers κ, μ, ξ). -/
theorem quarticChamberBCDEFG37810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG37810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_039 hcq8 hcq2 h hcq0 hcq1 hcq18 hcq7)
      · exact Or.inr (by exact astra4wPowerNat108_040 hcq2 h hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_041 hcq8 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_042 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_043 hcq2 h hcq0 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_044 hcq8 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_045 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_046 hcq2 h hcq0 hcq1 hcq18)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_047 hcq8 hcq2 h hcq0 hcq1 hcq18 hcq7)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_048 hcq8 hcq2 h hcq0 hcq1 hcq18 hcq7)
      · exact Or.inr (by exact astra4wPowerNat108_049 hcq2 h hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_050 hcq8 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_051 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_052 hcq2 h hcq0 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_053 hcq8 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_054 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_055 hcq2 h hcq0 hcq1 hcq18)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_056 hcq8 hcq2 h hcq0 hcq1 hcq18 hcq7)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_057 hcq8 hcq2 h hcq0 hcq1 hcq18 hcq7)
      · exact Or.inr (by exact astra4wPowerNat108_058 hcq2 h hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_059 hcq8 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_060 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_061 hcq2 h hcq0 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_062 hcq8 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_063 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_064 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_065 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_066 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_067 hcq2 h hcq1 hcq18)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_068 hcq2 h hcq0 hcq1 hcq18)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_069 hcq8 hcq2 h hcq0 hcq1 hcq18 hcq7)
      · exact Or.inr (by exact astra4wPowerNat108_070 hcq2 h hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_071 h hcq8 hcq2 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_072 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_073 hcq2 h hcq0 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_074 hcq8 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_075 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_076 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_077 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_078 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_079 hcq2 hcq1 h hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_080 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_081 hcq2 h hcq0 hcq1 hcq18)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_082 h hcq2 hcq0 hcq1 hcq18)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_083 h hcq8 hcq2 hcq0 hcq1 hcq18 hcq7)
    · exact Or.inr (by exact astra4wPowerNat108_084 h hcq2 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_085 hcq8 hcq2 hcq1 h hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_086 h hcq2 hcq1 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_087 h hcq2 hcq0 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_088 h hcq8 hcq2 hcq1 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_089 h hcq8 hcq2 hcq0 hcq1 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_090 h hcq2 hcq0 hcq1 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_091 h hcq2 hcq1 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_092 h hcq8 hcq2 hcq0 hcq1 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_093 h hcq2 hcq1 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_094 h hcq2 hcq1 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_095 h hcq2 hcq0 hcq1 hcq18)
    · exact Or.inr (by exact astra4wPowerNat108_096 h hcq8 hcq2 hcq1 hcq18)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat108_000 hcq8 hcq2 hcq1 hcq18) (by exact astra4wPowerNat108_001 hcq2 hcq0 hcq7) (by exact astra4wPowerNat108_002 hcq8 hcq2 hcq1) hz0l hz0beta (Or.inr (by exact astra4wPowerNat108_003 hcq8 hcq2 hcq0 hcq1 hcq18)) hz0delta (Or.inr (by exact astra4wPowerNat108_004 hcq8 hcq2 hcq1 hcq18)) hz0zeta (Or.inr (by exact astra4wPowerNat108_005 hcq8 hcq2 hcq1 hcq18)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top_S10 hAne hBne hCne hFne (D := D) (E := E) (G := G) (by exact astra4wPowerNat108_006 hcq0) (by exact astra4wPowerNat108_007 hcq2 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_097 hcq2 h hcq0 hcq1 hcq18 hcq7)
      · exact Or.inr (by exact astra4wPowerNat108_098 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_099 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_100 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_101 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_102 hcq2 h hcq0 hcq1 hcq18)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_103 hcq8 hcq2 h hcq0 hcq1 hcq18 hcq7)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_104 hcq2 h hcq0 hcq1 hcq18 hcq7)
      · exact Or.inr (by exact astra4wPowerNat108_105 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_106 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_107 hcq2 hcq0 hcq1 h hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_108 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_109 hcq2 h hcq0 hcq1 hcq18)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_110 hcq8 hcq2 h hcq0 hcq1 hcq18)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_111 hcq2 h hcq0 hcq1 hcq18 hcq7)
      · exact Or.inr (by exact astra4wPowerNat108_112 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_113 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_114 h hcq2 hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_115 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_116 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_117 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_118 hcq2 h hcq0 hcq1 hcq18)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_119 h hcq8 hcq2 hcq0 hcq1 hcq18)
  have hr1 : (muQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest15810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat108_008 hcq2 hcq0 hcq1 hcq18) (by exact astra4wPowerNat108_009 hcq8 hcq2 hcq0) (by exact astra4wPowerNat108_010 hcq2 hcq0 hcq18) (by exact astra4wPowerNat108_011 hcq8 hcq2 hcq1 hcq18) (by exact astra4wPowerNat108_012 hcq2 hcq0 hcq7) (by exact astra4wPowerNat108_013 hcq8 hcq2 hcq0 hcq1 hcq18) hz1l hz1beta (Or.inr (by exact astra4wPowerNat108_014 hcq8 hcq2 hcq0 hcq1 hcq18 hcq7)) hz1delta (Or.inr (by exact astra4wPowerNat108_015 hcq8 hcq2 hcq0 hcq1 hcq18)) (Or.inr (by exact astra4wPowerNat108_016 hcq8 hcq2 hcq0 hcq1 hcq18)) (Or.inr (by exact astra4wPowerNat108_017 hcq8 hcq2 hcq1 hcq18)) (Or.inr (by exact astra4wPowerNat108_018 hcq8 hcq2 hcq0 hcq1 hcq18))
  have hct1 := muQuarticChamberFace15810_coeff_top_S10 hAne hBne hCne hEne hFne (D := D) (G := G) (by exact astra4wPowerNat108_019 hcq2 hcq0) (by exact astra4wPowerNat108_020 hcq0) (by exact astra4wPowerNat108_021 hcq2 hcq0 hcq1)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face15_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_120 hcq8 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_121 hcq8 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_122 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_123 h hcq8 hcq2 hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_124 h hcq8 hcq2 hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_125 h hcq8 hcq2 hcq0 hcq1 hcq18 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_126 hcq8 hcq2 h hcq0 hcq1 hcq18 hcq7)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_127 hcq8 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_128 hcq8 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_129 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_130 hcq8 hcq2 h hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_131 h hcq8 hcq2 hcq0 hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_132 h hcq8 hcq2 hcq0 hcq1 hcq18 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_133 h hcq2 hcq0 hcq1 hcq18)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat108_134 hcq8 hcq1 h)
      · exact Or.inr (by exact astra4wPowerNat108_135 hcq8 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat108_136 hcq8 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_137 hcq8 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_138 hcq8 hcq2 h hcq1 hcq18)
      · exact Or.inr (by exact astra4wPowerNat108_139 h hcq8 hcq2 hcq0 hcq1 hcq18 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat108_140 h hcq2 hcq0 hcq1 hcq18)
  have hr2 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by exact astra4wPowerNat108_022 hcq1 hcq18) (by exact astra4wPowerNat108_023 hcq8 hcq0 hcq1) (by exact astra4wPowerNat108_024 hcq8 hcq2 hcq1 hcq18) (by exact astra4wPowerNat108_025 hcq0 hcq1 hcq18) (by exact astra4wPowerNat108_026 hcq8 hcq2 hcq1) (by exact astra4wPowerNat108_027 hcq2 hcq0 hcq1 hcq18 hcq7) (by exact astra4wPowerNat108_028 hcq2 hcq0 hcq1 hcq18) (by exact astra4wPowerNat108_029 hcq8 hcq2 hcq1 hcq18) (by exact astra4wPowerNat108_030 hcq8 hcq2 hcq0 hcq1 hcq18) (by exact astra4wPowerNat108_031 hcq2 hcq0 hcq7) (by exact astra4wPowerNat108_032 hcq2 hcq1 hcq18) hz2l hz2beta (Or.inr (by exact astra4wPowerNat108_033 hcq8 hcq2 hcq0 hcq1 hcq18)) hz2delta (Or.inr (by exact astra4wPowerNat108_034 hcq8 hcq2 hcq0 hcq1 hcq18 hcq7)) (Or.inr (by exact astra4wPowerNat108_035 hcq8 hcq2 hcq0 hcq1 hcq18)) (Or.inr (by exact astra4wPowerNat108_036 hcq8 hcq2 hcq1 hcq18)) (Or.inr (by exact astra4wPowerNat108_037 hcq8 hcq2 hcq1 hcq18))
  have hct2 := xiQuarticChamberFace5810_coeff_top_S10 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat108_038 hcq0)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS10810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS10810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
