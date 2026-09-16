import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch

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
private theorem astra4wPowerNat107_000
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_001
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_002
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : b + 2 * c = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_003
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : c + f = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_004
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 4 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_005
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + e < a + f)
    : 2 * b + e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_006
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a + 2 * b < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_007
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_008
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a + b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_009
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_010
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_011
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : a + b + f = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_012
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : 3 * c = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_013
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    : 2 * e = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_014
    {a b e f : ℕ}
    (h0 : a + b + f = 2 * e)
    (h1 : b + e < a + f)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_015
    {a b c e f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_016
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_017
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_018
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_019
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a + b + c < (a + 2 * b + e) ∧ 3 * b < (a + 2 * b + e) ∧ a + f < (a + 2 * b + e) ∧ b + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_020
    {a b c e f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : a + 2 * b < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_021
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_022
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_023
    {a b c e : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : 2 * c + e = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_024
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : d = 0)
    (h5 : g < 4 * a)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_025
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ e + f)
    (h2 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_026
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
private theorem astra4wPowerNat107_027
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 2 * b + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_028
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_029
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
private theorem astra4wPowerNat107_030
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
private theorem astra4wPowerNat107_031
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_032
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_033
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : d = 0)
    (h5 : g < 4 * a)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_034
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ e + f)
    (h2 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_035
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
private theorem astra4wPowerNat107_036
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_037
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_038
    {a b d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : a + b + f = 2 * e)
    (h4 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_039
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
private theorem astra4wPowerNat107_040
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_041
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_042
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : d = 0)
    (h5 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_043
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ e + f)
    (h2 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_044
    {a b d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 3 * a ≤ 2 * b + d)
    (h4 : a + b + f = 2 * e)
    (h5 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_045
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_046
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_047
    {a b d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + 2 * d)
    (h3 : a + b + f = 2 * e)
    (h4 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_048
    {a b c d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 4 * a ≤ 2 * c + d)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_049
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_050
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + e)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_051
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
private theorem astra4wPowerNat107_052
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_053
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_054
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : d = 0)
    (h5 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_055
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_056
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_057
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_058
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_059
    {a b d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + 2 * d)
    (h3 : a + b + f = 2 * e)
    (h4 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_060
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
private theorem astra4wPowerNat107_061
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_062
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_063
    {a b c d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_064
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : a ≤ b)
    (h3 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_065
    {a b e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_066
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_067
    {a b c e f : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_068
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : d = 0)
    (h5 : g = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_069
    {a b e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_070
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : a ≤ 2 * b + d)
    (h3 : b + e < a + f)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_071
    {a b e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_072
    {a b c e f : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_073
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_074
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
private theorem astra4wPowerNat107_075
    {a b c e f : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_076
    {a b e f : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_077
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
private theorem astra4wPowerNat107_078
    {a b e f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_079
    {a b e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_080
    {a b c e f : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_081
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_082
    {a b c e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : g < 4 * a)
    (h6 : g = 0)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_083
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_084
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
private theorem astra4wPowerNat107_085
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_086
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
private theorem astra4wPowerNat107_087
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_088
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_089
    {a b c e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : g = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_090
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_091
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
private theorem astra4wPowerNat107_092
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : a ≤ b)
    (h4 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_093
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
private theorem astra4wPowerNat107_094
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_095
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_096
    {a b c e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : g = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_097
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_098
    {a b c d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ d + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : a + b + f = 2 * e)
    (h5 : d = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_099
    {a b c e f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_100
    {a b c d e f : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 3 * a ≤ 2 * b + d)
    (h4 : a + 2 * b = 2 * c)
    (h5 : a + b + f = 2 * e)
    (h6 : d = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_101
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_102
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_103
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_104
    {a b c e f : ℕ}
    (h0 : 2 * a + b < a + 2 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_105
    {a b c e f : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_106
    {a b c e f : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_107
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    (h3 : d = 0)
    : ¬ (9 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_108
    {a b c e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_109
    {a b c e f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_110
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    (h3 : g = 0)
    : ¬ (15 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_111
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + b + c < a + 2 * b + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_112
    {a b c e f : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_113
    {a b c e f : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + b + f = 2 * e)
    (h3 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_114
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    (h3 : d = 0)
    : ¬ (7 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_115
    {a b c e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 9 * a ≤ 4 * e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_116
    {a b c e f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_117
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + b + f = 2 * e)
    (h2 : b + e < a + f)
    (h3 : g = 0)
    : ¬ (13 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_118
    {a b c e f : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + b + f = 2 * e)
    (h4 : b + e < a + f)
    : 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_119
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_120
    {a b c f g : ℕ}
    (h0 : c + f < b + g)
    (h1 : g = a + 2 * b)
    : c + f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_121
    {a b d e g : ℕ}
    (h0 : d + e < b + g)
    (h1 : g = a + 2 * b)
    : d + e < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_122
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : g = a + 2 * b)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_123
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 4 * d < 2 * b + 2 * g)
    (h2 : c + f < b + g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_124
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : g = a + 2 * b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_125
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : b + g = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_126
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : g = a + 2 * b)
    : 4 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_127
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : c + f < b + g)
    (h2 : g = a + 2 * b)
    : a + b + f < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_128
    {a b c d g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 4 * d < 2 * b + 2 * g)
    (h2 : g = a + 2 * b)
    : a + 2 * d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_129
    {a b c e g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 2 * b + e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_130
    {a b c d : ℕ}
    (h0 : d < a + b)
    : b + c + d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_131
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : c + f < b + g)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : d + f < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_132
    {a b c e g : ℕ}
    (h0 : 4 * e < a + 2 * b + 2 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : g = a + 2 * b)
    : 2 * e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_133
    {a b c d f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) ∧ g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_134
    {a b c d e f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_135
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : c + f < b + g)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a + b < (a + 2 * b + c) ∧ d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_136
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : g = a + 2 * b)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_137
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : g = a + 2 * b)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_138
    {a b c g : ℕ}
    (h0 : g = a + 2 * b)
    : c + g = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_139
    {a b d : ℕ}
    (h0 : d < a + b)
    : a + 3 * b + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_140
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : g = a + 2 * b)
    : 4 * b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_141
    {a b c f g : ℕ}
    (h0 : c + f < b + g)
    (h1 : g = a + 2 * b)
    : a + b + c + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_142
    {a b d e g : ℕ}
    (h0 : d + e < b + g)
    (h1 : g = a + 2 * b)
    : a + b + d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_143
    {a b c d g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 4 * d < 2 * b + 2 * g)
    (h2 : g = a + 2 * b)
    : a + c + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_144
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    : 3 * b + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_145
    {a b c e g : ℕ}
    (h0 : c + e < a + g)
    (h1 : g = a + 2 * b)
    : 2 * b + c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_146
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_147
    {a b c d : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : d < a + b)
    : b + 2 * c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_148
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : c + f < b + g)
    (h2 : g = a + 2 * b)
    : a + 2 * f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_149
    {a b d g : ℕ}
    (h0 : d < a + b)
    (h1 : g = a + 2 * b)
    : b + d + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_150
    {a b c e f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : c + e < a + g)
    (h2 : c + f < b + g)
    (h3 : g = a + 2 * b)
    : b + e + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_151
    {a b c d f g : ℕ}
    (h0 : c + f < b + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : c + d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_152
    {a b c e g : ℕ}
    (h0 : 4 * e < a + 2 * b + 2 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : g = a + 2 * b)
    : c + 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_153
    {a b d e g : ℕ}
    (h0 : d + e < b + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 2 * d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_154
    {a b c d e f g : ℕ}
    (h0 : 0 < a)
    (h1 : 4 * e < a + 2 * b + 2 * g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + 4 * d < 2 * b + 2 * g)
    (h4 : c + e < a + g)
    (h5 : c + f < b + g)
    (h6 : d + e < b + g)
    (h7 : d < a + b)
    (h8 : g = a + 2 * b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_155
    {a b c d e f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : c + f < b + g)
    (h4 : d + e < b + g)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_156
    {a b c d e f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : d + e < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_157
    {a b c d f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_158
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : g = a + 2 * b)
    : b + c < (2 * a + 4 * b) ∧ f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_159
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : a + 2 * b + 2 * c = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_160
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : a + 2 * b + g = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_161
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : 4 * c = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_162
    {a b c g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : g = a + 2 * b)
    : 2 * c + g = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_163
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : 2 * g = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_164
    {a b d g : ℕ}
    (h0 : 6 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_165
    {a b c e f g : ℕ}
    (h0 : 6 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_166
    {a b d : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_167
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 6 * a ≤ 2 * b + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_168
    {a b c e g : ℕ}
    (h0 : 6 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_169
    {a b d : ℕ}
    (h0 : 6 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_170
    {a b c d : ℕ}
    (h0 : 6 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_171
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 6 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_172
    {a b c d e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_173
    {a b d g : ℕ}
    (h0 : 5 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_174
    {a b c e f g : ℕ}
    (h0 : 5 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_175
    {a b d : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_176
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_177
    {a b c e g : ℕ}
    (h0 : 5 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_178
    {a b d : ℕ}
    (h0 : 5 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_179
    {a b c d : ℕ}
    (h0 : 5 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_180
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_181
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_182
    {a b d g : ℕ}
    (h0 : 4 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_183
    {a b c e f g : ℕ}
    (h0 : 4 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_184
    {a b d : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_185
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_186
    {a b c e g : ℕ}
    (h0 : 4 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_187
    {a b d : ℕ}
    (h0 : 4 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_188
    {a b c d : ℕ}
    (h0 : 4 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_189
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_190
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_191
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_192
    {a b g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_193
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
private theorem astra4wPowerNat107_194
    {a b d g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_195
    {a b c e f g : ℕ}
    (h0 : 3 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_196
    {a b d : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_197
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_198
    {a b c e g : ℕ}
    (h0 : 3 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_199
    {a b d : ℕ}
    (h0 : 3 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_200
    {a b c d : ℕ}
    (h0 : 3 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_201
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_202
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_203
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_204
    {a b g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a ≤ b)
    (h2 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_205
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_206
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_207
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_208
    {a b d g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_209
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_210
    {a b d : ℕ}
    (h0 : a ≤ 2 * b + d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_211
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 2 * b + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_212
    {a b c e g : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : c + e < a + g)
    (h2 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_213
    {a b d : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_214
    {a b c d : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_215
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_216
    {a b c e g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ b + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_217
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_218
    {a b : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 3 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_219
    {a b c f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_220
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_221
    {a b d g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_222
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_223
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_224
    {a b c d e g : ℕ}
    (h0 : 5 * a ≤ d + e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_225
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_226
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_227
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_228
    {a b c d e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_229
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_230
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_231
    {a b c d e g : ℕ}
    (h0 : 4 * a ≤ d + e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_232
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_233
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_234
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_235
    {a b c d e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_236
    {a b c g : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_237
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_238
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ d + e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_239
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_240
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_241
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_242
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_243
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_244
    {a b c d f g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_245
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_246
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_247
    {a b c d e g : ℕ}
    (h0 : 5 * a ≤ d + e)
    (h1 : c + e < a + g)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_248
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_249
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_250
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_251
    {a b c d e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_252
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_253
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_254
    {a b c d e g : ℕ}
    (h0 : 4 * a ≤ d + e)
    (h1 : c + e < a + g)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_255
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_256
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_257
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_258
    {a b c d e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_259
    {a b c g : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_260
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_261
    {a b c d e g : ℕ}
    (h0 : 3 * a ≤ d + e)
    (h1 : c + e < a + g)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_262
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_263
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_264
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_265
    {a b c f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_266
    {a b c g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_267
    {a b c d e f g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_268
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) ∧ g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_269
    {a b c e f g : ℕ}
    (h0 : 0 < a)
    (h1 : 4 * e < a + 2 * b + 2 * g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_270
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : c + f < b + g)
    (h2 : g = a + 2 * b)
    : a + b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_271
    {a b c e f g : ℕ}
    (h0 : 0 < a)
    (h1 : 4 * e < a + 2 * b + 2 * g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_272
    {a b c e f g : ℕ}
    (h0 : 0 < a)
    (h1 : 4 * e < a + 2 * b + 2 * g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_273
    {a b c e f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + e < a + g)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_274
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : g = a + 2 * b)
    : a + 2 * b < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_275
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 6 * a ≤ d + g)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_276
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_277
    {a b d g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 6 * a ≤ b + 2 * d)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_278
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 6 * a ≤ 2 * c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    (h4 : f < 2 * a + b)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_279
    {a b c e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_280
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ d + g)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_281
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_282
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ b + 2 * d)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_283
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    (h4 : f < 2 * a + b)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_284
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_285
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ d + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_286
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_287
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_288
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_289
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
private theorem astra4wPowerNat107_290
    {a b d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ d + g)
    (h2 : d = 0)
    (h3 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_291
    {a b d g : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d = 0)
    (h3 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_292
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_293
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_294
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    (h4 : f < 2 * a + b)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_295
    {a b d g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ d + g)
    (h2 : d = 0)
    (h3 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_296
    {a b d : ℕ}
    (h0 : 0 < a)
    (h1 : a ≤ 2 * b + d)
    (h2 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_297
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_298
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ 2 * c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_299
    {a b c d f g : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_300
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_301
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
private theorem astra4wPowerNat107_302
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    (h4 : f < 2 * a + b)
    (h5 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_303
    {a b c e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_304
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
private theorem astra4wPowerNat107_305
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    (h4 : f < 2 * a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_306
    {a b c e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_307
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ d + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : f < 2 * a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_308
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_309
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_310
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
private theorem astra4wPowerNat107_311
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    (h4 : f < 2 * a + b)
    (h5 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_312
    {a b c e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_313
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
private theorem astra4wPowerNat107_314
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d = 0)
    (h4 : f < 2 * a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_315
    {a b c e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_316
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ d + e)
    (h3 : a + 2 * b = 2 * c)
    (h4 : d = 0)
    (h5 : f < 2 * a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_317
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d = 0)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_318
    {a b c e f g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : c + f < b + g)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_319
    {a b c f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : g = a + 2 * b)
    : 2 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_320
    {a b c d f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : c + f < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_321
    {a b c d f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : c + f < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_322
    {a b c d f g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : c + f < b + g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_323
    {a b e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 6 * a ≤ e + f)
    (h2 : e < 3 * a)
    (h3 : e = 0)
    (h4 : f < 2 * a + b)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_324
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
private theorem astra4wPowerNat107_325
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_326
    {a b e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ e + f)
    (h2 : e < 3 * a)
    (h3 : e = 0)
    (h4 : f < 2 * a + b)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_327
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
private theorem astra4wPowerNat107_328
    {a b c d g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_329
    {a b d e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ e + f)
    (h2 : d < a + b)
    (h3 : e = 0)
    (h4 : f < 2 * a + b)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_330
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
private theorem astra4wPowerNat107_331
    {a b e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ b + e)
    (h2 : e < 3 * a)
    (h3 : e = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_332
    {a b c g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_333
    {a b c e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : e = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_334
    {a b c e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : e = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_335
    {a b d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : d < a + b)
    (h3 : e = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_336
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : e = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_337
    {a b c e : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : e = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_338
    {a b d e g : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d < a + b)
    (h3 : e = 0)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_339
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
private theorem astra4wPowerNat107_340
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_341
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
private theorem astra4wPowerNat107_342
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_343
    {a b c d e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : f < 2 * a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_344
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
private theorem astra4wPowerNat107_345
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_346
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
private theorem astra4wPowerNat107_347
    {a b c d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_348
    {a b c d e f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : f < 2 * a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_349
    {a b c d f g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + f < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_350
    {a b c d e g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : d + e < b + g)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : b + c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_351
    {a b d g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 4 * d < 2 * b + 2 * g)
    (h2 : g = a + 2 * b)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_352
    {a b d e g : ℕ}
    (h0 : d + e < b + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_353
    {a b c d e g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : d + e < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) ∧ g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_354
    {a b c d e g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d + e < b + g)
    (h3 : g = a + 2 * b)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_355
    {a b c d e g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : a + b < (a + 2 * b + c) ∧ d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_356
    {a b c d e g : ℕ}
    (h0 : d + e < b + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_357
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_358
    {a b c d e g : ℕ}
    (h0 : 0 < a)
    (h1 : 4 * e < a + 2 * b + 2 * g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + 4 * d < 2 * b + 2 * g)
    (h4 : c + e < a + g)
    (h5 : d + e < b + g)
    (h6 : d < a + b)
    (h7 : g = a + 2 * b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_359
    {a b c d e g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_360
    {a b c d e g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : d + e < b + g)
    (h4 : g = a + 2 * b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_361
    {a b c d e g : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 4 * d < 2 * b + 2 * g)
    (h3 : d + e < b + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_362
    {a b c : ℕ}
    (h0 : 0 < a)
    (h1 : a + 2 * b = 2 * c)
    : b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_363
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 6 * a ≤ e + f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_364
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 6 * a ≤ 2 * b + f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_365
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_366
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_367
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 5 * a ≤ 2 * b + f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_368
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 4 * a ≤ e + f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_369
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_370
    {a b d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : 3 * a ≤ e + f)
    (h3 : d < a + b)
    (h4 : f = 0)
    (h5 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_371
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_372
    {a b d f g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a ≤ f)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_373
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
private theorem astra4wPowerNat107_374
    {a b f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : f = 0)
    (h3 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_375
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * g < 5 * a + 2 * b)
    (h2 : d < a + b)
    (h3 : f = 0)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_376
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
private theorem astra4wPowerNat107_377
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_378
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
private theorem astra4wPowerNat107_379
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_380
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
private theorem astra4wPowerNat107_381
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
private theorem astra4wPowerNat107_382
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : d < a + b)
    : 2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_383
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
private theorem astra4wPowerNat107_384
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 4 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_385
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
private theorem astra4wPowerNat107_386
    {a b c d e g : ℕ}
    (h0 : 2 * g < 5 * a + 2 * b)
    (h1 : 3 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat107_387
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
private theorem astra4wPowerNat107_388
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
private theorem astra4wPowerNat107_389
    {a b c d e g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : c + e < a + g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEG` / `BG·CG·BBB·BBC·BCC·CCC` dies on power system `S08` (carriers κ, μ, π). -/
theorem quarticChamberBCDEG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG5810 A B C D E F G)
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
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_164 h hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_363 hcq9 hcq10 h hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_166 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_364 hcq10 h hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_168 h hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_169 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_170 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_171 hcq10 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_365 hcq10 h hcq0 hcq14 hcq7 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_173 h hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_366 hcq9 hcq10 h hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_175 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_367 hcq10 h hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_177 h hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_178 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_179 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_180 hcq10 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_181 hcq10 h hcq0 hcq14 hcq7 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_182 h hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_368 hcq9 hcq10 h hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_184 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_369 hcq10 h hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_186 h hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_187 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_188 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_189 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_190 hcq10 h hcq0 hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_191 hcq10 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_192 hcq10 h hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_193 hApos hcq10 h hcq0 hcq14 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_194 h hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_370 hcq9 hcq10 h hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_196 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_371 hcq10 h hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_198 h hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_199 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_200 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat107_201 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_202 hcq10 h hcq0 hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_203 hcq10 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_204 hcq10 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_372 hcq10 h hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_206 hcq10 h hcq0 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_207 hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_208 h hcq7 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_373 h hcq10 hcq0 hcq14 hFn hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_210 h hcq7)
    · exact Or.inr (by exact astra4wPowerNat107_374 h hcq10 hFn hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_212 h hcq14 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_213 h hcq7)
    · exact Or.inr (by exact astra4wPowerNat107_214 h hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat107_215 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat107_216 hApos h hcq0 hcq14 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_217 hApos h hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat107_218 hApos h)
    · exact Or.inr (by exact astra4wPowerNat107_375 h hcq10 hcq7 hFn hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_220 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat107_221 h hcq10 hcq7 hcq1)
  have hr0 : (kappaQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by exact astra4wPowerNat107_119 hcq7) (by exact astra4wPowerNat107_121 hcq6 hcq1) hz0l hz0beta (Or.inr (by exact astra4wPowerNat107_350 hcq0 hcq6 hcq7 hcq1)) hz0delta (Or.inr (by exact astra4wPowerNat107_351 hApos hcq5 hcq1)) hz0zeta (Or.inr (by exact astra4wPowerNat107_352 hcq6 hcq7 hcq1)) hz0theta
  have hct0 := kappaQuarticChamberFace9810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_002 hcq0) (by exact astra4wPowerNat107_125 hcq1)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_222 hcq10 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_376 hcq10 h hcq0 hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_224 h hcq0 hcq14 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_225 hcq10 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_226 hcq10 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_227 hcq10 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_377 hcq10 h hcq0 hcq14 hcq7 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_229 hcq10 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_378 hcq10 h hcq0 hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_231 h hcq0 hcq14 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_232 hcq10 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_233 hcq10 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_234 hcq10 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_379 hcq10 h hcq0 hcq14 hcq7 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_236 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_380 hcq10 h hcq0 hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_238 h hcq0 hcq14 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_239 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_240 hcq10 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_241 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_381 hcq10 h hcq0 hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_243 hcq10 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_382 hApos h hcq0 hcq7)
  have hr1 : (muQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest10810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by exact astra4wPowerNat107_126 hcq10 hcq0 hcq1) (by exact astra4wPowerNat107_128 hcq0 hcq5 hcq1) (by exact astra4wPowerNat107_129 hcq0 hcq14 hcq1) (by exact astra4wPowerNat107_130 hcq7) (by exact astra4wPowerNat107_132 hcq8 hcq0 hcq1) hz1l hz1beta (Or.inr (by exact astra4wPowerNat107_353 hApos hcq0 hcq5 hcq6 hcq7 hcq1)) hz1delta (Or.inr (by exact astra4wPowerNat107_354 hApos hcq0 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_355 hApos hcq0 hcq5 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_356 hcq6 hcq7 hcq1)) (Or.inr (by exact astra4wPowerNat107_357 hApos hcq0))
  have hct1 := muQuarticChamberFace10810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_012 hcq0) (by exact astra4wPowerNat107_138 hcq1)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_245 hcq10 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_383 hcq10 h hcq0 hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_247 h hcq14 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_248 hcq10 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_249 hcq10 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_250 hcq10 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_384 hcq10 h hcq0 hcq14 hcq7 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_252 hcq10 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_385 hcq10 h hcq0 hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_254 h hcq14 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_255 hcq10 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_256 hcq10 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_257 hcq10 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_386 hcq10 h hcq0 hcq14 hcq7 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_259 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_387 hcq10 h hcq0 hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_261 h hcq14 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_262 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_263 hcq10 h hcq0 hcq7 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_264 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_388 hcq10 h hcq0 hcq7 hFn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_266 hcq10 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_389 hApos h hcq0 hcq14 hcq7 hcq1)
  have hr2 : (piQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest8810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hFz (by exact astra4wPowerNat107_139 hcq7) (by exact astra4wPowerNat107_140 hcq10 hcq0 hcq1) (by exact astra4wPowerNat107_142 hcq6 hcq1) (by exact astra4wPowerNat107_143 hcq0 hcq5 hcq1) (by exact astra4wPowerNat107_145 hcq14 hcq1) (by exact astra4wPowerNat107_146 hcq7) (by exact astra4wPowerNat107_147 hcq0 hcq7) (by exact astra4wPowerNat107_149 hcq7 hcq1) (by exact astra4wPowerNat107_152 hcq8 hcq0 hcq1) (by exact astra4wPowerNat107_153 hcq6 hcq7 hcq1) hz2l hz2beta (Or.inr (by exact astra4wPowerNat107_358 hApos hcq8 hcq0 hcq5 hcq14 hcq6 hcq7 hcq1)) hz2delta (Or.inr (by exact astra4wPowerNat107_359 hApos hcq0 hcq5 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_360 hApos hcq0 hcq5 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_361 hApos hcq0 hcq5 hcq6 hcq7 hcq1)) (Or.inr (by exact astra4wPowerNat107_362 hApos hcq0))
  have hct2 := piQuarticChamberFace8810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_159 hcq0) (by exact astra4wPowerNat107_160 hcq1) (by exact astra4wPowerNat107_161 hcq0) (by exact astra4wPowerNat107_162 hcq0 hcq1) (by exact astra4wPowerNat107_163 hcq1)
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
/-- Chamber `BCDFG` / `BG·CG·BBB·BBC·BCC·CCC` dies on power system `S08` (carriers κ, μ, π). -/
theorem quarticChamberBCDFG29810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG29810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat107_164 h hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_323 hcq12 h hAE hEn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_166 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_167 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_324 hcq12 h hcq0 hcq9 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_169 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_170 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_171 hcq12 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_325 hcq12 h hcq0 hcq6 hcq9 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_173 h hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_326 hcq12 h hAE hEn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_175 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_176 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_327 hcq12 h hcq0 hcq9 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_178 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_179 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_180 hcq12 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_328 hcq12 h hcq0 hcq9 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_182 h hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_329 hcq12 h hcq9 hEn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_184 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_185 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_330 hcq12 h hcq0 hcq9 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_187 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_188 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_189 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_331 hcq12 h hAE hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_191 hcq12 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_192 hcq12 h hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_332 hApos hcq12 h hcq0 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_194 h hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_333 hcq12 h hcq0 hcq6 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_196 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_197 hApos h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_334 hcq12 h hcq0 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_199 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_200 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat107_201 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_335 hcq12 h hcq9 hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_203 hcq12 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_204 hcq12 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_205 hcq12 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_206 hcq12 h hcq0 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_207 hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_208 h hcq9 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_336 h hcq12 hcq0 hcq6 hEn)
    · exact Or.inr (by exact astra4wPowerNat107_210 h hcq9)
    · exact Or.inr (by exact astra4wPowerNat107_211 hApos h hcq0 hcq6 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_337 hApos h hcq0 hEn)
    · exact Or.inr (by exact astra4wPowerNat107_213 h hcq9)
    · exact Or.inr (by exact astra4wPowerNat107_214 h hcq0 hcq9)
    · exact Or.inr (by exact astra4wPowerNat107_215 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat107_338 h hcq12 hcq9 hEn hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_217 hApos h hcq0 hcq9)
    · exact Or.inr (by exact astra4wPowerNat107_218 hApos h)
    · exact Or.inr (by exact astra4wPowerNat107_219 h hcq12 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat107_220 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat107_221 h hcq12 hcq9 hcq1)
  have hr0 : (kappaQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by exact astra4wPowerNat107_119 hcq9) (by exact astra4wPowerNat107_120 hcq6 hcq1) hz0l hz0beta (Or.inr (by exact astra4wPowerNat107_122 hApos hcq0 hcq6 hcq1)) hz0delta (Or.inr (by exact astra4wPowerNat107_123 hcq0 hcq7 hcq6 hcq9 hcq1)) hz0zeta (Or.inr (by exact astra4wPowerNat107_124 hApos hcq0 hcq6 hcq1)) hz0theta
  have hct0 := kappaQuarticChamberFace9810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_002 hcq0) (by exact astra4wPowerNat107_125 hcq1)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_222 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_223 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_339 hcq12 h hcq0 hcq9 hAE hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_225 hcq12 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_226 hcq12 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_227 hcq12 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_340 hcq12 h hcq0 hcq6 hcq9 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_229 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_230 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_341 hcq12 h hcq0 hcq9 hAE hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_232 hcq12 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_233 hcq12 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_234 hcq12 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_342 hcq12 h hcq0 hcq6 hcq9 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_236 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_237 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_343 hcq12 h hcq0 hcq9 hEn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_239 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_240 hcq12 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_241 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_242 hcq12 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_243 hcq12 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_244 hApos h hcq0 hcq6 hcq9 hcq1)
  have hr1 : (muQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest10810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz (by exact astra4wPowerNat107_126 hcq12 hcq0 hcq1) (by exact astra4wPowerNat107_127 hcq0 hcq6 hcq1) (by exact astra4wPowerNat107_128 hcq0 hcq7 hcq1) (by exact astra4wPowerNat107_130 hcq9) (by exact astra4wPowerNat107_131 hcq0 hcq6 hcq9 hcq1) hz1l hz1beta (Or.inr (by exact astra4wPowerNat107_133 hApos hcq0 hcq6 hcq9 hcq1)) hz1delta (Or.inr (by exact astra4wPowerNat107_319 hApos hcq0 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_135 hcq0 hcq6 hcq9 hcq1)) (Or.inr (by exact astra4wPowerNat107_136 hApos hcq0 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_137 hApos hcq0 hcq6 hcq1))
  have hct1 := muQuarticChamberFace10810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_012 hcq0) (by exact astra4wPowerNat107_138 hcq1)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_245 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_246 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_344 hcq12 h hcq0 hcq9 hAE hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_248 hcq12 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_249 hcq12 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_250 hcq12 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_345 hcq12 h hcq0 hcq6 hcq9 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_252 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_253 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_346 hcq12 h hcq0 hcq9 hAE hEn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_255 hcq12 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_256 hcq12 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_257 hcq12 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_347 hcq12 h hcq0 hcq6 hcq9 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_259 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_260 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_348 hcq12 h hcq0 hcq9 hEn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_262 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_263 hcq12 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_264 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_265 hcq12 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_266 hcq12 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_349 hApos h hcq0 hcq6 hcq9 hcq1)
  have hr2 : (piQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest8810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hEz (by exact astra4wPowerNat107_139 hcq9) (by exact astra4wPowerNat107_140 hcq12 hcq0 hcq1) (by exact astra4wPowerNat107_141 hcq6 hcq1) (by exact astra4wPowerNat107_143 hcq0 hcq7 hcq1) (by exact astra4wPowerNat107_144 hcq12 hcq0 hcq6) (by exact astra4wPowerNat107_146 hcq9) (by exact astra4wPowerNat107_147 hcq0 hcq9) (by exact astra4wPowerNat107_148 hcq0 hcq6 hcq1) (by exact astra4wPowerNat107_149 hcq9 hcq1) (by exact astra4wPowerNat107_151 hcq6 hcq9 hcq1) hz2l hz2beta (Or.inr (by exact astra4wPowerNat107_320 hApos hcq0 hcq7 hcq6 hcq9 hcq1)) hz2delta (Or.inr (by exact astra4wPowerNat107_321 hApos hcq0 hcq7 hcq6 hcq9 hcq1)) (Or.inr (by exact astra4wPowerNat107_322 hApos hcq0 hcq6 hcq9 hcq1)) (Or.inr (by exact astra4wPowerNat107_157 hApos hcq0 hcq6 hcq9 hcq1)) (Or.inr (by exact astra4wPowerNat107_158 hApos hcq0 hcq6 hcq1))
  have hct2 := piQuarticChamberFace8810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_159 hcq0) (by exact astra4wPowerNat107_160 hcq1) (by exact astra4wPowerNat107_161 hcq0) (by exact astra4wPowerNat107_162 hcq0 hcq1) (by exact astra4wPowerNat107_163 hcq1)
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
/-- Chamber `BCEFG` / `BG·CG·BBB·BBC·BCC·CCC` dies on power system `S08` (carriers κ, μ, π). -/
theorem quarticChamberBCEFG29810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG29810 A B C D E F G)
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
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_275 hcq12 h hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_165 h hcq0 hcq14 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_276 hcq12 h hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_167 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_168 h hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_277 hAD hcq12 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_278 hcq12 h hcq0 hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_171 hcq12 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_279 hcq12 h hcq0 hcq14 hcq6 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_280 hcq12 h hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_174 h hcq0 hcq14 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_281 hcq12 h hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_176 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_177 h hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_282 hcq12 h hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_283 hcq12 h hcq0 hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_180 hcq12 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_284 hcq12 h hcq0 hcq14 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_285 hcq12 h hcq0 hcq6 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_183 h hcq0 hcq14 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_286 hcq12 h hcq0 hcq6 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_185 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_186 h hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_287 hcq12 h hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_288 hcq12 h hcq0 hcq6 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_189 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_190 hcq12 h hcq0 hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_289 hAD hcq12 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_192 hcq12 h hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_193 hApos hcq12 h hcq0 hcq14 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_290 hcq12 h hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_195 h hcq0 hcq14 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_291 h hcq12 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_197 hApos h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_198 h hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_292 hcq12 h hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_293 hcq12 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_201 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_202 hcq12 h hcq0 hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_294 hcq12 h hcq0 hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_204 hcq12 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_205 hcq12 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_206 hcq12 h hcq0 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_207 hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_295 hApos h hDn hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_209 h hcq0 hcq14 hcq6 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_296 hApos h hDn)
    · exact Or.inr (by exact astra4wPowerNat107_211 hApos h hcq0 hcq6 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_212 h hcq14 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_297 h hcq12 hDn hcq11 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_298 hApos h hcq0 hDn)
    · exact Or.inr (by exact astra4wPowerNat107_215 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat107_216 hApos h hcq0 hcq14 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_299 h hcq12 hcq0 hcq6 hDn hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_218 hApos h)
    · exact Or.inr (by exact astra4wPowerNat107_219 h hcq12 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat107_220 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat107_300 h hcq12 hDn hcq11 hcq1)
  have hr0 : (kappaQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by exact astra4wPowerNat107_120 hcq6 hcq1) hz0l hz0beta (Or.inr (by exact astra4wPowerNat107_122 hApos hcq0 hcq6 hcq1)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat107_124 hApos hcq0 hcq6 hcq1)) hz0theta
  have hct0 := kappaQuarticChamberFace9810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_002 hcq0) (by exact astra4wPowerNat107_125 hcq1)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_222 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_223 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_301 hAD hcq9 hcq12 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_225 hcq12 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_302 hcq12 h hcq0 hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_227 hcq12 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_303 hcq12 h hcq0 hcq14 hcq6 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_229 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_230 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_304 hAD hcq9 hcq12 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_232 hcq12 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_305 hcq12 h hcq0 hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_234 hcq12 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_306 hcq12 h hcq0 hcq14 hcq6 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_236 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_237 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_307 hcq9 hcq12 h hcq0 hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_239 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_308 hcq12 h hcq0 hcq6 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_241 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_242 hcq12 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_243 hcq12 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_309 hApos h hcq0 hcq6 hcq1)
  have hr1 : (muQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest10810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by exact astra4wPowerNat107_126 hcq12 hcq0 hcq1) (by exact astra4wPowerNat107_127 hcq0 hcq6 hcq1) (by exact astra4wPowerNat107_129 hcq0 hcq14 hcq1) (by exact astra4wPowerNat107_132 hcq7 hcq0 hcq1) hz1l hz1beta (Or.inr (by exact astra4wPowerNat107_268 hApos hcq0 hcq6 hcq1)) hz1delta (Or.inr (by exact astra4wPowerNat107_269 hApos hcq7 hcq0 hcq14 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_270 hcq0 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_136 hApos hcq0 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_137 hApos hcq0 hcq6 hcq1))
  have hct1 := muQuarticChamberFace10810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_012 hcq0) (by exact astra4wPowerNat107_138 hcq1)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_245 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_246 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_310 hAD hcq9 hcq12 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_248 hcq12 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_311 hcq12 h hcq0 hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_250 hcq12 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_312 hcq12 h hcq0 hcq14 hcq6 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_252 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_253 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_313 hAD hcq9 hcq12 h hcq0 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_255 hcq12 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_314 hcq12 h hcq0 hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_257 hcq12 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_315 hcq12 h hcq0 hcq14 hcq6 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_259 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_260 hcq12 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_316 hcq9 hcq12 h hcq0 hDn hcq11 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_262 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_317 hcq12 h hcq0 hcq6 hDn hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_264 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_265 hcq12 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_266 hcq12 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_318 hApos h hcq0 hcq14 hcq6 hcq1)
  have hr2 : (piQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest8810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz (by exact astra4wPowerNat107_140 hcq12 hcq0 hcq1) (by exact astra4wPowerNat107_141 hcq6 hcq1) (by exact astra4wPowerNat107_144 hcq12 hcq0 hcq6) (by exact astra4wPowerNat107_145 hcq14 hcq1) (by exact astra4wPowerNat107_148 hcq0 hcq6 hcq1) (by exact astra4wPowerNat107_150 hcq0 hcq14 hcq6 hcq1) (by exact astra4wPowerNat107_152 hcq7 hcq0 hcq1) hz2l hz2beta (Or.inr (by exact astra4wPowerNat107_271 hApos hcq7 hcq0 hcq14 hcq6 hcq1)) hz2delta (Or.inr (by exact astra4wPowerNat107_272 hApos hcq7 hcq0 hcq14 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_273 hApos hcq0 hcq14 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_274 hApos hcq0 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_158 hApos hcq0 hcq6 hcq1))
  have hct2 := piQuarticChamberFace8810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_159 hcq0) (by exact astra4wPowerNat107_160 hcq1) (by exact astra4wPowerNat107_161 hcq0) (by exact astra4wPowerNat107_162 hcq0 hcq1) (by exact astra4wPowerNat107_163 hcq1)
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
/-- Chamber `BCDEFG` / `BG·CG·BBB·BBC·BCC·CCC` dies on power system `S08` (carriers κ, μ, π). -/
theorem quarticChamberBCDEFG53810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG53810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat107_164 h hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_165 h hcq0 hcq20 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_166 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_167 hcq16 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_168 h hcq20 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_169 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_170 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_171 hcq16 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_172 hcq16 h hcq0 hcq20 hcq6 hcq10 hcq1)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_173 h hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_174 h hcq0 hcq20 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_175 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_176 hcq16 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_177 h hcq20 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_178 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_179 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_180 hcq16 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_181 hcq16 h hcq0 hcq20 hcq10 hcq1)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_182 h hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_183 h hcq0 hcq20 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_184 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_185 hcq16 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_186 h hcq20 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_187 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_188 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_189 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_190 hcq16 h hcq0 hcq20 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_191 hcq16 h hcq0 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_192 hcq16 h hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_193 hApos hcq16 h hcq0 hcq20 hcq1)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_194 h hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_195 h hcq0 hcq20 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_196 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_197 hApos h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_198 h hcq20 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_199 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_200 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat107_201 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_202 hcq16 h hcq0 hcq20 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_203 hcq16 h hcq0 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_204 hcq16 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_205 hcq16 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_206 hcq16 h hcq0 hcq1)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_207 hApos h hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_208 h hcq10 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_209 h hcq0 hcq20 hcq6 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_210 h hcq10)
    · exact Or.inr (by exact astra4wPowerNat107_211 hApos h hcq0 hcq6 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_212 h hcq20 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_213 h hcq10)
    · exact Or.inr (by exact astra4wPowerNat107_214 h hcq0 hcq10)
    · exact Or.inr (by exact astra4wPowerNat107_215 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat107_216 hApos h hcq0 hcq20 hcq1)
    · exact Or.inr (by exact astra4wPowerNat107_217 hApos h hcq0 hcq10)
    · exact Or.inr (by exact astra4wPowerNat107_218 hApos h)
    · exact Or.inr (by exact astra4wPowerNat107_219 h hcq16 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat107_220 hApos h hcq0)
    · exact Or.inr (by exact astra4wPowerNat107_221 h hcq16 hcq10 hcq1)
  have hr0 : (kappaQuarticChamberRest9810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest9810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat107_119 hcq10) (by exact astra4wPowerNat107_120 hcq6 hcq1) (by exact astra4wPowerNat107_121 hcq8 hcq1) hz0l hz0beta (Or.inr (by exact astra4wPowerNat107_122 hApos hcq0 hcq6 hcq1)) hz0delta (Or.inr (by exact astra4wPowerNat107_123 hcq0 hcq7 hcq6 hcq10 hcq1)) hz0zeta (Or.inr (by exact astra4wPowerNat107_124 hApos hcq0 hcq6 hcq1)) hz0theta
  have hct0 := kappaQuarticChamberFace9810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_002 hcq0) (by exact astra4wPowerNat107_125 hcq1)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_222 hcq16 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_223 hcq16 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_224 h hcq0 hcq20 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_225 hcq16 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_226 hcq16 h hcq0 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_227 hcq16 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_228 hcq16 h hcq0 hcq20 hcq6 hcq10 hcq1)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_229 hcq16 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_230 hcq16 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_231 h hcq0 hcq20 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_232 hcq16 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_233 hcq16 h hcq0 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_234 hcq16 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_235 hcq16 h hcq0 hcq20 hcq6 hcq10 hcq1)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_236 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_237 hcq16 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_238 h hcq0 hcq20 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_239 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_240 hcq16 h hcq0 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_241 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_242 hcq16 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_243 hcq16 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_244 hApos h hcq0 hcq6 hcq10 hcq1)
  have hr1 : (muQuarticChamberRest10810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest10810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat107_126 hcq16 hcq0 hcq1) (by exact astra4wPowerNat107_127 hcq0 hcq6 hcq1) (by exact astra4wPowerNat107_128 hcq0 hcq7 hcq1) (by exact astra4wPowerNat107_129 hcq0 hcq20 hcq1) (by exact astra4wPowerNat107_130 hcq10) (by exact astra4wPowerNat107_131 hcq0 hcq6 hcq10 hcq1) (by exact astra4wPowerNat107_132 hcq11 hcq0 hcq1) hz1l hz1beta (Or.inr (by exact astra4wPowerNat107_133 hApos hcq0 hcq6 hcq10 hcq1)) hz1delta (Or.inr (by exact astra4wPowerNat107_134 hApos hcq0 hcq6 hcq8 hcq1)) (Or.inr (by exact astra4wPowerNat107_135 hcq0 hcq6 hcq10 hcq1)) (Or.inr (by exact astra4wPowerNat107_136 hApos hcq0 hcq6 hcq1)) (Or.inr (by exact astra4wPowerNat107_137 hApos hcq0 hcq6 hcq1))
  have hct1 := muQuarticChamberFace10810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_012 hcq0) (by exact astra4wPowerNat107_138 hcq1)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_245 hcq16 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_246 hcq16 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_247 h hcq20 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_248 hcq16 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_249 hcq16 h hcq0 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_250 hcq16 h hcq0 hcq1)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_251 hcq16 h hcq0 hcq20 hcq6 hcq10 hcq1)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_252 hcq16 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_253 hcq16 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_254 h hcq20 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_255 hcq16 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_256 hcq16 h hcq0 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_257 hcq16 h hcq0 hcq1)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_258 hcq16 h hcq0 hcq20 hcq6 hcq10 hcq1)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_259 hApos h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_260 hcq16 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat107_261 h hcq20 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_262 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_263 hcq16 h hcq0 hcq10 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_264 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat107_265 hcq16 h hcq0 hcq6 hcq1)
      · exact Or.inr (by exact astra4wPowerNat107_266 hcq16 h hcq0 hcq1)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_267 hApos h hcq0 hcq20 hcq6 hcq10 hcq1)
  have hr2 : (piQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest8810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by exact astra4wPowerNat107_139 hcq10) (by exact astra4wPowerNat107_140 hcq16 hcq0 hcq1) (by exact astra4wPowerNat107_141 hcq6 hcq1) (by exact astra4wPowerNat107_142 hcq8 hcq1) (by exact astra4wPowerNat107_143 hcq0 hcq7 hcq1) (by exact astra4wPowerNat107_144 hcq16 hcq0 hcq6) (by exact astra4wPowerNat107_145 hcq20 hcq1) (by exact astra4wPowerNat107_146 hcq10) (by exact astra4wPowerNat107_147 hcq0 hcq10) (by exact astra4wPowerNat107_148 hcq0 hcq6 hcq1) (by exact astra4wPowerNat107_149 hcq10 hcq1) (by exact astra4wPowerNat107_150 hcq0 hcq20 hcq6 hcq1) (by exact astra4wPowerNat107_151 hcq6 hcq10 hcq1) (by exact astra4wPowerNat107_152 hcq11 hcq0 hcq1) (by exact astra4wPowerNat107_153 hcq8 hcq10 hcq1) hz2l hz2beta (Or.inr (by exact astra4wPowerNat107_154 hApos hcq11 hcq0 hcq7 hcq20 hcq6 hcq8 hcq10 hcq1)) hz2delta (Or.inr (by exact astra4wPowerNat107_155 hApos hcq0 hcq7 hcq6 hcq8 hcq10 hcq1)) (Or.inr (by exact astra4wPowerNat107_156 hApos hcq0 hcq6 hcq8 hcq10 hcq1)) (Or.inr (by exact astra4wPowerNat107_157 hApos hcq0 hcq6 hcq10 hcq1)) (Or.inr (by exact astra4wPowerNat107_158 hApos hcq0 hcq6 hcq1))
  have hct2 := piQuarticChamberFace8810_coeff_top_S08 hAne hBne hCne hGne (D := D) (E := E) (F := F) (by exact astra4wPowerNat107_159 hcq0) (by exact astra4wPowerNat107_160 hcq1) (by exact astra4wPowerNat107_161 hcq0) (by exact astra4wPowerNat107_162 hcq0 hcq1) (by exact astra4wPowerNat107_163 hcq1)
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
/-- Chamber `BCEF` / `BF·CF·EE·BBB·BBC·BCC·CCC` dies on power system `S10` (carriers κ, μ, ξ). -/
theorem quarticChamberBCEF7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEF7810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_024 hcq6 hcq2 h hcq1 hDn hAG)
      · exact Or.inr (by exact astra4wPowerNat107_025 hcq2 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_026 hAD hcq6 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_027 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_028 hcq2 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_029 hAD hcq6 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_030 hAD hcq6 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_031 hcq2 h hcq0 hcq1 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_032 hcq2 h hcq0 hcq1 hcq8)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_033 hcq6 hcq2 h hcq1 hDn hAG)
      · exact Or.inr (by exact astra4wPowerNat107_034 hcq2 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_035 hAD hcq6 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_036 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_037 hcq2 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_038 hcq6 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_039 hAD hcq6 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_040 hcq2 h hcq0 hcq1 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_041 hcq2 h hcq0 hcq1 hcq8)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_042 hcq6 hcq2 h hcq1 hDn hGn)
      · exact Or.inr (by exact astra4wPowerNat107_043 hcq2 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_044 hAD hcq6 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_045 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_046 hcq2 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_047 hcq6 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_048 hAD hcq6 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_049 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_050 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_051 hAD hcq2 h hcq0 hcq1 hcq8 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_052 hcq2 h hcq1 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_053 hcq2 h hcq0 hcq1 hcq8)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_054 hcq6 hcq2 h hcq1 hDn hGn)
      · exact Or.inr (by exact astra4wPowerNat107_055 hcq2 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_056 h hcq2 hcq1 hcq8 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_057 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_058 hcq2 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_059 hcq6 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_060 hcq2 h hcq0 hcq1 hcq8 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_061 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_062 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_063 hcq6 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_064 hcq2 hcq1 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_065 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_066 hcq2 h hcq0 hcq1 hcq8)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_067 h hcq2 hcq0 hcq1 hcq8)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_068 h hcq2 hcq1 hcq8 hDn hGn)
    · exact Or.inr (by exact astra4wPowerNat107_069 h hcq2 hcq8)
    · exact Or.inr (by exact astra4wPowerNat107_070 hcq2 hcq1 h hcq8 hDn)
    · exact Or.inr (by exact astra4wPowerNat107_071 h hcq2 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat107_072 h hcq2 hcq0 hcq8)
    · exact Or.inr (by exact astra4wPowerNat107_073 h hcq2 hcq1 hcq8 hDn)
    · exact Or.inr (by exact astra4wPowerNat107_074 h hcq2 hcq0 hcq1 hcq8 hDn)
    · exact Or.inr (by exact astra4wPowerNat107_075 h hcq2 hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat107_076 h hcq2 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat107_077 h hcq2 hcq0 hcq1 hcq8 hDn)
    · exact Or.inr (by exact astra4wPowerNat107_078 h hcq2 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat107_079 h hcq2 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat107_080 h hcq2 hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat107_081 h hcq2 hcq1 hcq8 hDn)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz hGz hz0l hz0beta (Or.inr (by exact astra4wPowerNat107_000 hcq2 hcq0 hcq1 hcq8)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat107_001 hcq2 hcq1 hcq8)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top_S10 hAne hBne hCne hFne (D := D) (E := E) (G := G) (by exact astra4wPowerNat107_002 hcq0) (by exact astra4wPowerNat107_003 hcq2 hcq0)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_082 hcq6 hcq2 h hcq0 hcq1 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat107_083 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_084 hAD hcq6 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_085 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_086 hAD hcq6 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_087 hcq2 h hcq0 hcq1 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_088 hcq2 h hcq0 hcq1 hcq8)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_089 hcq6 hcq2 h hcq0 hcq1 hGn)
      · exact Or.inr (by exact astra4wPowerNat107_090 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_091 hAD hcq6 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_092 hcq2 hcq0 hcq1 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_093 hAD hcq6 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_094 hcq2 h hcq0 hcq1 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_095 hcq2 h hcq0 hcq1 hcq8)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_096 hcq6 hcq2 h hcq0 hcq1 hGn)
      · exact Or.inr (by exact astra4wPowerNat107_097 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_098 hcq6 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_099 h hcq2 hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_100 hAD hcq6 hcq2 h hcq0 hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_101 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_102 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_103 hcq2 h hcq0 hcq1 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_104 h hcq2 hcq0 hcq1 hcq8)
  have hr1 : (muQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest15810_natDegree_lt_of_live_BCEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz hGz (by exact astra4wPowerNat107_004 hcq2 hcq0 hcq1 hcq8) (by exact astra4wPowerNat107_005 hcq2 hcq0 hcq8) hz1l hz1beta (Or.inr (by exact astra4wPowerNat107_006 hcq2 hcq0 hcq1 hcq8)) hz1delta (Or.inr (by exact astra4wPowerNat107_007 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat107_008 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat107_009 hcq2 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat107_010 hcq2 hcq0 hcq1 hcq8))
  have hct1 := muQuarticChamberFace15810_coeff_top_S10 hAne hBne hCne hEne hFne (D := D) (G := G) (by exact astra4wPowerNat107_011 hcq2 hcq0) (by exact astra4wPowerNat107_012 hcq0) (by exact astra4wPowerNat107_013 hcq2 hcq0 hcq1)
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
      · exact Or.inr (by exact astra4wPowerNat107_105 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_106 h hcq0 hcq1 hcq8)
      · exact absurd h (by exact astra4wPowerNat107_107 hcq2 hcq1 hcq8 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_108 h hcq2 hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_109 h hcq2 hcq0 hcq1 hcq8)
      · exact absurd h (by exact astra4wPowerNat107_110 hcq2 hcq1 hcq8 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_111 hcq2 h hcq0 hcq1 hcq8)
  have hz2beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat107_112 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_113 h hcq0 hcq1 hcq8)
      · exact absurd h (by exact astra4wPowerNat107_114 hcq2 hcq1 hcq8 hDn)
      · exact Or.inr (by exact astra4wPowerNat107_115 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat107_116 h hcq2 hcq0 hcq1 hcq8)
      · exact absurd h (by exact astra4wPowerNat107_117 hcq2 hcq1 hcq8 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat107_118 h hcq2 hcq0 hcq1 hcq8)
  have hr2 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz hGz (by exact astra4wPowerNat107_014 hcq1 hcq8) (by exact astra4wPowerNat107_015 hcq0 hcq1 hcq8) (by exact astra4wPowerNat107_016 hcq2 hcq0 hcq1 hcq8) (by exact astra4wPowerNat107_017 hcq2 hcq1 hcq8) hz2l hz2beta (Or.inr (by exact astra4wPowerNat107_018 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat107_019 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat107_020 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat107_021 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat107_022 hcq2 hcq1 hcq8))
  have hct2 := xiQuarticChamberFace5810_coeff_top_S10 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat107_023 hcq0)
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
