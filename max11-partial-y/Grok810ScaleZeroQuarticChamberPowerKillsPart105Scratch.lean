import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
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
private theorem astra4wPowerNat105_000
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_001
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    : d + e < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_002
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_003
    {a b d : ℕ}
    (h0 : d < a + b)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_004
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_005
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : b + 2 * c = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_006
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : c + f = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_007
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_008
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b + e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_009
    {a b c d : ℕ}
    (h0 : d < a + b)
    : b + c + d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_010
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : d + f < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_011
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    : 2 * e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_012
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_013
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_014
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b < (a + 2 * b + c) ∧ d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_015
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_016
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_017
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : a + b + f = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_018
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    : a + 2 * d = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_019
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : 3 * c = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_020
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 4 * b < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_021
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    : a + 2 * b + e < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_022
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * b + d < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_023
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b + 2 * c < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_024
    {a b c d f : ℕ}
    (h0 : b + f = 2 * d)
    (h1 : d < a + b)
    : b + c + f < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_025
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + d + e < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_026
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    : 2 * c + e < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_027
    {a b c d : ℕ}
    (h0 : d < a + b)
    : c + 2 * d < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_028
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * f < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_029
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + d < (a + b + c + d) ∧ 2 * b + c < (a + b + c + d) ∧ b + f < (a + b + c + d) ∧ c + e < (a + b + c + d) ∧ 2 * d < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_030
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 2 * b < (a + b + c + d) ∧ b + d < (a + b + c + d) ∧ 2 * c < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_031
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + d < (a + b + c + d) ∧ b + c < (a + b + c + d) ∧ f < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_032
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * b < (a + b + c + d) ∧ e < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_033
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : d < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_034
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : a + d + f = a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_035
    {a b d : ℕ}
    (h0 : d < a + b)
    : a + 3 * b + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_036
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_037
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    : a + b + d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_038
    {a b d f : ℕ}
    (h0 : b + f = 2 * d)
    (h1 : d < a + b)
    : 3 * b + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_039
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b + c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_040
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_041
    {a b c d : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : d < a + b)
    : b + 2 * c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_042
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + e + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_043
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : c + d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_044
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    : c + 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_045
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : d < a + b)
    : 2 * d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_046
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_047
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_048
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_049
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_050
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + c < (2 * a + 4 * b) ∧ f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_051
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : a + 2 * b + 2 * c = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_052
    {a b c f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    : a + b + c + f = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_053
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    : a + c + 2 * d = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_054
    {a b c : ℕ}
    (h0 : a + 2 * b = 2 * c)
    : 4 * c = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_055
    {a b f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    : a + 2 * f = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_056
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
private theorem astra4wPowerNat105_057
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ e + f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_058
    {a b d : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_059
    {a b d f : ℕ}
    (h0 : 6 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_060
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 6 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_061
    {a b d : ℕ}
    (h0 : 6 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_062
    {a b c d : ℕ}
    (h0 : 6 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_063
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_064
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_065
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
private theorem astra4wPowerNat105_066
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_067
    {a b d : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_068
    {a b d f : ℕ}
    (h0 : 5 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_069
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 5 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_070
    {a b d : ℕ}
    (h0 : 5 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_071
    {a b c d : ℕ}
    (h0 : 5 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_072
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_073
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a < a + 3 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_074
    {a b d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ d + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_075
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ e + f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_076
    {a b d : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_077
    {a b d f : ℕ}
    (h0 : 4 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_078
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_079
    {a b d : ℕ}
    (h0 : 4 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_080
    {a b c d : ℕ}
    (h0 : 4 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_081
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_082
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_083
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_084
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_085
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
private theorem astra4wPowerNat105_086
    {a b d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ d + g)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_087
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ e + f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_088
    {a b d : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_089
    {a b d f : ℕ}
    (h0 : 3 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_090
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_091
    {a b d : ℕ}
    (h0 : 3 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_092
    {a b c d : ℕ}
    (h0 : 3 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_093
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_094
    {a b d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + e)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_095
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_096
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a ≤ b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_097
    {a b d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_098
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_099
    {a b c d f : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_100
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_101
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_102
    {a b d : ℕ}
    (h0 : a ≤ 2 * b + d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_103
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_104
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_105
    {a b d : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_106
    {a b c d : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_107
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_108
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_109
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_110
    {a b d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_111
    {a b d f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_112
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_113
    {a b d f : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_114
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g < 4 * a)
    (h6 : g = 0)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_115
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_116
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_117
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_118
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_119
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_120
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a + b < a + 2 * b + c)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_121
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_122
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_123
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_124
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_125
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_126
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_127
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
private theorem astra4wPowerNat105_128
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_129
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_130
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_131
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_132
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_133
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_134
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_135
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_136
    {a b c d f : ℕ}
    (h0 : 2 * a + b < a + 2 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_137
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g < 4 * a)
    (h6 : g = 0)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_138
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_139
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_140
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_141
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_142
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_143
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a + d < a + b + c + d)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 3 * a + f < a + b + c + d ∧ 2 * a + b + e < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + c + f < a + b + c + d ∧ a + d + e < a + b + c + d ∧ 2 * b + f < a + b + c + d ∧ b + c + e < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d ∧ e + f < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_144
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_145
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_146
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_147
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_148
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_149
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_150
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
private theorem astra4wPowerNat105_151
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_152
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ c + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_153
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_154
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_155
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_156
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_157
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_158
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_159
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
private theorem astra4wPowerNat105_160
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g < 4 * a)
    (h6 : g = 0)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_161
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ c + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_162
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_163
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_164
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_165
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_166
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a + b + c < 2 * a + 4 * b)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_167
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_168
    {a b c d f : ℕ}
    (h0 : 4 * a ≤ c + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_169
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_170
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a ≤ b)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_171
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_172
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_173
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
private theorem astra4wPowerNat105_174
    {a b c d e f g : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * b = 2 * c)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    (h6 : g = 0)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_175
    {a b c d f : ℕ}
    (h0 : 3 * a ≤ c + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_176
    {a b c d e f : ℕ}
    (h0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_177
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_178
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_179
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_180
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_181
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_182
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
private theorem astra4wPowerNat105_183
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_184
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b + d < (a + b + c + d) ∧ 2 * b + c < (a + b + c + d) ∧ b + f < (a + b + c + d) ∧ 2 * d < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_185
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b < (a + b + c + d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_186
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_187
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_188
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_189
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
private theorem astra4wPowerNat105_190
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
private theorem astra4wPowerNat105_191
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_192
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ e + f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : e < 3 * a)
    (h5 : e = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_193
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e < 3 * a)
    (h6 : e = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_194
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_195
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ d + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_196
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ e + f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : e < 3 * a)
    (h5 : e = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_197
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e < 3 * a)
    (h6 : e = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_198
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
private theorem astra4wPowerNat105_199
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a < a + 3 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_200
    {a b d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + g)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_201
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : e = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_202
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
private theorem astra4wPowerNat105_203
    {a b d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : e = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_204
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    (h3 : e = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_205
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
private theorem astra4wPowerNat105_206
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    (h4 : e = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_207
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
private theorem astra4wPowerNat105_208
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_209
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_210
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
private theorem astra4wPowerNat105_211
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + b < a + 2 * b + c)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_212
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_213
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_214
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
private theorem astra4wPowerNat105_215
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + d < a + b + c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 3 * a + f < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + c + f < a + b + c + d ∧ 2 * b + f < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_216
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 3 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_217
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
private theorem astra4wPowerNat105_218
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + d < a + b + c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + b + c + d ∧ 2 * a + b + c < a + b + c + d ∧ a + 3 * b < a + b + c + d ∧ 2 * a + f < a + b + c + d ∧ a + c + d < a + b + c + d ∧ 2 * b + d < a + b + c + d ∧ b + 2 * c < a + b + c + d ∧ c + f < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_219
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_220
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e = 0)
    : 2 * a + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_221
    {a b c d f : ℕ}
    (h0 : 2 * a + d < a + b + c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + b + c + d ∧ a + b + c < a + b + c + d ∧ 3 * b < a + b + c + d ∧ a + f < a + b + c + d ∧ c + d < a + b + c + d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_222
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
private theorem astra4wPowerNat105_223
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_224
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_225
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
private theorem astra4wPowerNat105_226
    {a b c d f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + b + c < 2 * a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_227
    {a b c d f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : g = 0)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_228
    {a b c d e f : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    (h5 : e = 0)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_229
    {a b c d f : ℕ}
    (h0 : 2 * a + b + c < 2 * a + 4 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_230
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_231
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : c + g < a + 2 * d)
    : b + g < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_232
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    (h2 : b + f < 2 * d)
    : c + f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_233
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_234
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_235
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_236
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : b + 2 * c = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_237
    {a b d e : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : a + 2 * d = 2 * e)
    : d + e = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_238
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : a + 2 * d = 2 * e)
    : 4 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_239
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : b + f < 2 * d)
    : a + b + f < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_240
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    : 2 * b + e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_241
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : b + c + d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_242
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : c + g < a + 2 * d)
    : c + g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_243
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : d + f < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_244
    {a b c d e f g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    (h5 : c + g < a + 2 * d)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) ∧ g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_245
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_246
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + b < (a + 2 * b + c) ∧ d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_247
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_248
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_249
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    : a + 2 * d = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_250
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : 3 * c = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_251
    {a b c d e : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : a + 2 * d = 2 * e)
    : 2 * e = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_252
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : a + 2 * d = 2 * e)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_253
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_254
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_255
    {a b d e f : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : a + 2 * d = 2 * e)
    (h2 : b + f < 2 * d)
    : a + d + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_256
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : a + 2 * d = 2 * e)
    (h3 : c + g < a + 2 * d)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_257
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_258
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : b + d + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_259
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_260
    {a b c d e g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : c + g < a + 2 * d)
    : e + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_261
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_262
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_263
    {a b c d e f g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    (h5 : c + g < a + 2 * d)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_264
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_265
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_266
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_267
    {a b c d e : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : a + b + c + d = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_268
    {a b c d e : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : 2 * c + e = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_269
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : a + 3 * b + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_270
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 4 * b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_271
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : c + g < a + 2 * d)
    : a + 2 * b + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_272
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    (h2 : b + f < 2 * d)
    : a + b + c + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_273
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : 3 * b + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_274
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    : 2 * b + c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_275
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : 2 * b + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_276
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : b + 2 * c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_277
    {a b d f : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : b + f < 2 * d)
    : a + 2 * f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_278
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : b + d + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_279
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : b + f < 2 * d)
    : b + e + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_280
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    (h2 : c + g < a + 2 * d)
    : 2 * c + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_281
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : c + d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_282
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    : 2 * d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_283
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : c + g < a + 2 * d)
    : 2 * g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_284
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_285
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_286
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_287
    {a b c d e f g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    (h5 : c + g < a + 2 * d)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_288
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : b + c < (2 * a + 4 * b) ∧ f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_289
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : a + 2 * b + 2 * c = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_290
    {a b d e : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : a + 2 * d = 2 * e)
    : a + b + d + e = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_291
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : a + c + 2 * d = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_292
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : 4 * c = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_293
    {a b c d e : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : c + 2 * e = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_294
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 6 * a ≤ d + g)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_295
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 6 * a ≤ e + f)
    (h3 : b + f < 2 * d)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_296
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * d = 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_297
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 6 * a ≤ 2 * b + f)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_298
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 6 * a ≤ b + c + e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_299
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 6 * a ≤ b + 2 * d)
    (h3 : a + 2 * d = 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_300
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 6 * a ≤ 2 * c + d)
    (h4 : a + 2 * d = 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_301
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 6 * a ≤ 3 * b + c)
    (h4 : a + 2 * d = 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_302
    {a b c d e f g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    (h6 : c + g < a + 2 * d)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_303
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ d + g)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_304
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : b + f < 2 * d)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_305
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_306
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + f)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_307
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + c + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_308
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_309
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ 2 * c + d)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_310
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ 3 * b + c)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_311
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a < a + 3 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_312
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ d + g)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_313
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ e + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : b + f < 2 * d)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_314
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_315
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_316
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + c + e)
    (h3 : 4 * d = a + 6 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_317
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_318
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_319
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 3 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_320
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ b + e)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_321
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ c + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_322
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_323
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a < a + 3 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_324
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ d + g)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_325
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ e + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : b + f < 2 * d)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_326
    {a b d e : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_327
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_328
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + c + e)
    (h3 : 4 * d = a + 6 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_329
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_330
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ 2 * c + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_331
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ 3 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_332
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ b + e)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_333
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ c + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_334
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : a ≤ b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_335
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_336
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_337
    {a b c d e : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_338
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_339
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : b + f < 2 * d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_340
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : a ≤ 2 * b + d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_341
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_342
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_343
    {a b d e : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_344
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_345
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_346
    {a b d e : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_347
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_348
    {a b d e : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_349
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_350
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_351
    {a b d e : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_352
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_353
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ c + f)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_354
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ d + e)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_355
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 3 * b)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_356
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_357
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + 2 * c)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_358
    {a b c d e f g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + b < a + 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    (h6 : c + g < a + 2 * d)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_359
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_360
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ c + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_361
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ d + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_362
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : a + 2 * d = 2 * e)
    (h3 : a ≤ b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_363
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_364
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_365
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a + b < a + 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_366
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_367
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ c + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_368
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ d + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_369
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_370
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_371
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_372
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ f)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_373
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_374
    {a b c d e f : ℕ}
    (h0 : 2 * a + b < a + 2 * b + c)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_375
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + g)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_376
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ c + f)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_377
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ d + e)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_378
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_379
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_380
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + 2 * c)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_381
    {a b c d e f g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + d < a + 2 * b + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    (h6 : c + g < a + 2 * d)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_382
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + g)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_383
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ c + f)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_384
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ d + e)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_385
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : a ≤ b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_386
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_387
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_388
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a + d < a + 2 * b + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_389
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + g)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_390
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ c + f)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_391
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ d + e)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_392
    {a b d e : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_393
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_394
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_395
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_396
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_397
    {a b c d e f : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_398
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_399
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ c + f)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_400
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ d + e)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_401
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 3 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_402
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_403
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + 2 * c)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_404
    {a b c d e f g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + b + c < 2 * a + 4 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    (h6 : c + g < a + 2 * d)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_405
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ b + g)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_406
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ c + f)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_407
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ d + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_408
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : a ≤ b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_409
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_410
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_411
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a + b + c < 2 * a + 4 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_412
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ b + g)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_413
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ c + f)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_414
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ d + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_415
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_416
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_417
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_418
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ f)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_419
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat105_420
    {a b c d e f : ℕ}
    (h0 : 2 * a + b + c < 2 * a + 4 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `DD·DE·EE·BBB·BBC·BCC·CCC` dies on power system `S06` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEFG120810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG120810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat105_294 hcq18 hcq3 hcq2 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_295 hcq18 hcq2 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_296 hcq18 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_297 hcq18 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_298 hcq18 hcq3 hcq2 h)
      · exact Or.inr (by exact astra4wPowerNat105_299 hcq18 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_300 hcq18 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_301 hcq18 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_302 hcq18 hcq3 hcq2 h hcq0 hcq6 hcq9)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_303 hcq18 hcq3 hcq2 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_304 hcq18 hcq2 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_305 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_306 hcq18 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_307 hcq18 hcq3 hcq2 h)
      · exact Or.inr (by exact astra4wPowerNat105_308 hcq18 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_309 hcq18 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_310 hcq18 hcq3 hcq2 h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_311 hcq18 hcq3 h hcq2 hcq0 hcq9)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_312 hcq18 hcq3 h hcq2 hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_313 hcq18 h hcq2 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_314 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_315 hcq18 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_316 hcq18 hcq3 h hcq2)
      · exact Or.inr (by exact astra4wPowerNat105_317 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_318 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_319 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_320 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_321 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_322 hcq18 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_323 hcq18 hcq3 h hcq2 hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_324 hcq18 hcq3 h hcq2 hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_325 hcq18 h hcq2 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_326 h hcq18 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_327 hcq18 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_328 hcq18 hcq3 h hcq2)
      · exact Or.inr (by exact astra4wPowerNat105_329 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_330 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_331 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_332 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_333 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_334 hcq18 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat105_335 hcq18 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_336 hcq18 hcq3 h hcq2 hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_337 h hcq18 hcq3 hcq2 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_338 h hcq18 hcq3 hcq2 hcq0 hcq9)
    · exact Or.inr (by exact astra4wPowerNat105_339 h hcq18 hcq2 hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_340 hcq18 hcq2 hcq0 h)
    · exact Or.inr (by exact astra4wPowerNat105_341 h hcq18 hcq2 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_342 h hcq18 hcq3 hcq2)
    · exact Or.inr (by exact astra4wPowerNat105_343 h hcq18 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat105_344 h hcq18 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat105_345 h hcq18 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat105_346 h hcq18 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat105_347 h hcq18 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat105_348 h hcq18 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat105_349 h hcq18 hcq2 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_350 h hcq18 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat105_351 h hcq18 hcq2 hcq0)
  have hr0 : (kappaQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest8810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat105_230 hcq18 hcq2 hcq0) (by exact astra4wPowerNat105_231 hcq3 hcq9) (by exact astra4wPowerNat105_232 hcq3 hcq2 hcq6) hz0l hz0beta (Or.inr (by exact astra4wPowerNat105_233 hcq18 hcq3 hcq2 hcq0 hcq6)) hz0delta (Or.inr (by exact astra4wPowerNat105_234 hcq18 hcq2 hcq0 hcq6)) hz0zeta (Or.inr (by exact astra4wPowerNat105_235 hcq18 hcq2 hcq0 hcq6)) hz0theta
  have hct0 := kappaQuarticChamberFace8810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat105_236 hcq3 hcq2) (by exact astra4wPowerNat105_237 hcq2 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face8_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + C.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_352 hcq18 hcq3 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_353 hcq18 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_354 hcq18 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_355 hcq18 hcq3 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_356 hcq18 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_357 hcq18 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_358 hcq18 hcq3 h hcq2 hcq0 hcq6 hcq9)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_359 hcq18 hcq3 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_360 hcq18 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_361 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_362 hcq18 hcq3 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat105_363 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_364 hcq18 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_365 hcq18 hcq3 h hcq2 hcq0 hcq6)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_366 hcq18 hcq3 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_367 hcq18 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_368 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_369 h hcq18 hcq3 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_370 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_371 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_372 hcq18 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_373 hcq18 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_374 h hcq18 hcq3 hcq2 hcq0 hcq6)
  have hr1 : (muQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest13810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat105_238 hcq18 hcq3 hcq0) (by exact astra4wPowerNat105_239 hcq3 hcq6) (by exact astra4wPowerNat105_240 hcq18 hcq3) (by exact astra4wPowerNat105_241 hcq18 hcq2 hcq0) (by exact astra4wPowerNat105_242 hcq3 hcq9) (by exact astra4wPowerNat105_243 hcq18 hcq3 hcq2 hcq0 hcq6) hz1l hz1beta (Or.inr (by exact astra4wPowerNat105_244 hcq18 hcq3 hcq2 hcq0 hcq6 hcq9)) hz1delta (Or.inr (by exact astra4wPowerNat105_245 hcq18 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat105_246 hcq18 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat105_247 hcq18 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat105_248 hcq18 hcq3 hcq2 hcq0 hcq6))
  have hct1 := muQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat105_249 hcq3) (by exact astra4wPowerNat105_250 hcq3 hcq2) (by exact astra4wPowerNat105_251 hcq3 hcq0)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_375 hcq18 hcq3 hcq2 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_376 hcq18 hcq3 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_377 hcq18 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_378 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_379 hcq18 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_380 hcq18 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_381 hcq18 hcq3 h hcq2 hcq0 hcq6 hcq9)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_382 hcq18 hcq3 h hcq2 hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_383 hcq18 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_384 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_385 hcq18 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat105_386 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_387 hcq18 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_388 hcq18 hcq3 h hcq2 hcq0 hcq6)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_389 hcq18 hcq3 h hcq2 hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_390 hcq18 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_391 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_392 h hcq18 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_393 hcq18 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_394 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_395 hcq18 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_396 hcq18 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_397 h hcq18 hcq3 hcq2 hcq0 hcq6)
  have hr2 : (xiQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest13810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by exact astra4wPowerNat105_252 hcq18 hcq0) (by exact astra4wPowerNat105_253 hcq18 hcq2 hcq0) (by exact astra4wPowerNat105_254 hcq18 hcq3 hcq2 hcq0) (by exact astra4wPowerNat105_255 hcq2 hcq0 hcq6) (by exact astra4wPowerNat105_256 hcq18 hcq3 hcq0 hcq9) (by exact astra4wPowerNat105_257 hcq18 hcq3 hcq2 hcq0 hcq6) (by exact astra4wPowerNat105_258 hcq18 hcq2 hcq0) (by exact astra4wPowerNat105_259 hcq18 hcq3 hcq2 hcq0) (by exact astra4wPowerNat105_260 hcq3 hcq9) (by exact astra4wPowerNat105_261 hcq18 hcq2 hcq0 hcq6) hz2l hz2beta (Or.inr (by exact astra4wPowerNat105_262 hcq18 hcq3 hcq2 hcq0 hcq6)) hz2delta (Or.inr (by exact astra4wPowerNat105_263 hcq18 hcq3 hcq2 hcq0 hcq6 hcq9)) (Or.inr (by exact astra4wPowerNat105_264 hcq18 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat105_265 hcq18 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat105_266 hcq18 hcq2 hcq0 hcq6))
  have hct2 := xiQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat105_267 hcq3 hcq2 hcq0) (by exact astra4wPowerNat105_268 hcq3 hcq2)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_398 hcq18 hcq2 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_399 hcq18 hcq3 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_400 hcq18 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_401 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_402 hcq18 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_403 hcq18 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_404 hcq18 hcq3 h hcq2 hcq0 hcq6 hcq9)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_405 hcq18 h hcq2 hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_406 hcq18 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_407 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_408 hcq18 hcq3 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat105_409 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_410 hcq18 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_411 hcq18 hcq3 h hcq2 hcq0 hcq6)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_412 hcq18 h hcq2 hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat105_413 hcq18 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_414 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_415 h hcq18 hcq3 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_416 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_417 hcq18 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat105_418 hcq18 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_419 hcq18 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_420 h hcq18 hcq3 hcq2 hcq0 hcq6)
  have hr3 : (piQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 (by exact astra4wPowerNat105_269 hcq18 hcq2 hcq0) (by exact astra4wPowerNat105_270 hcq18 hcq3 hcq2 hcq0) (by exact astra4wPowerNat105_271 hcq3 hcq9) (by exact astra4wPowerNat105_272 hcq3 hcq2 hcq6) (by exact astra4wPowerNat105_273 hcq18 hcq2 hcq0 hcq6) (by exact astra4wPowerNat105_274 hcq18 hcq3 hcq2) (by exact astra4wPowerNat105_275 hcq18 hcq2 hcq0) (by exact astra4wPowerNat105_276 hcq18 hcq3 hcq2 hcq0) (by exact astra4wPowerNat105_277 hcq2 hcq6) (by exact astra4wPowerNat105_278 hcq18 hcq3 hcq2 hcq0 hcq9) (by exact astra4wPowerNat105_279 hcq18 hcq2 hcq6) (by exact astra4wPowerNat105_280 hcq3 hcq2 hcq9) (by exact astra4wPowerNat105_281 hcq18 hcq3 hcq2 hcq0 hcq6) (by exact astra4wPowerNat105_282 hcq18 hcq2) (by exact astra4wPowerNat105_283 hcq3 hcq9) hz3l hz3beta (Or.inr (by exact astra4wPowerNat105_284 hcq18 hcq3 hcq2 hcq0 hcq6)) hz3delta (Or.inr (by exact astra4wPowerNat105_285 hcq18 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat105_286 hcq18 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat105_287 hcq18 hcq3 hcq2 hcq0 hcq6 hcq9)) (Or.inr (by exact astra4wPowerNat105_288 hcq18 hcq3 hcq2 hcq0 hcq6))
  have hct3 := piQuarticChamberFace6810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat105_289 hcq3 hcq2) (by exact astra4wPowerNat105_290 hcq2 hcq0) (by exact astra4wPowerNat105_291 hcq3 hcq2) (by exact astra4wPowerNat105_292 hcq3 hcq2) (by exact astra4wPowerNat105_293 hcq3 hcq2 hcq0)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face6_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : piQuarticPowerInnerS06810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS06810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hEc


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
/-- Chamber `BCDF` / `BF·CF·DD·BBB·BBC·BCC·CCC` dies on power system `S07` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDF7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF7810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_056 hcq2 h hcq1 hcq6 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat105_189 hcq2 h hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_058 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_059 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_190 hcq2 h hcq0 hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_061 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_062 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_063 hcq2 h hcq0 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_191 hcq2 h hcq0 hcq1 hcq6)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_065 hcq2 h hcq1 hcq6 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat105_192 hcq2 h hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_067 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_068 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_193 hcq2 h hcq0 hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_070 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_071 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_072 hcq2 h hcq0 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_194 hcq2 h hcq0 hcq1 hcq6)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_195 hcq2 h hcq1 hcq6 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_196 hcq2 h hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_076 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_077 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_197 hcq2 h hcq0 hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_079 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_080 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_081 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_198 hcq2 h hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_083 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_084 hcq2 h hcq1 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_199 hcq2 h hcq0 hcq1 hcq6)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_200 hcq2 h hcq1 hcq6 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_201 hcq2 h hcq1 hcq6 hEn)
      · exact Or.inr (by exact astra4wPowerNat105_088 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_089 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_202 hcq2 h hcq0 hcq1 hcq6 hEn)
      · exact Or.inr (by exact astra4wPowerNat105_091 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_092 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_093 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_203 hcq2 h hcq1 hcq6 hEn)
      · exact Or.inr (by exact astra4wPowerNat105_095 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_096 hcq2 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_097 hcq2 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_098 hcq2 h hcq0 hcq1 hcq6)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_099 h hcq2 hcq0 hcq1 hcq6)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_100 h hcq2 hcq1 hcq6 hGn)
    · exact Or.inr (by exact astra4wPowerNat105_204 h hcq1 hcq6 hEn)
    · exact Or.inr (by exact astra4wPowerNat105_102 h hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_103 h hcq1 hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_205 h hcq2 hcq0 hcq1 hcq6 hEn)
    · exact Or.inr (by exact astra4wPowerNat105_105 h hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_106 h hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_107 h hcq2 hcq0 hcq1 hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_206 h hcq2 hcq1 hcq6 hEn)
    · exact Or.inr (by exact astra4wPowerNat105_109 h hcq2 hcq0 hcq1 hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_110 h hcq2 hcq1 hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_111 h hcq1 hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_112 h hcq2 hcq0 hcq1 hcq6)
    · exact Or.inr (by exact astra4wPowerNat105_113 h hcq2 hcq1 hcq6)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz hGz (by exact astra4wPowerNat105_000 hcq6) hz0l hz0beta (Or.inr (by exact astra4wPowerNat105_002 hcq2 hcq0 hcq1 hcq6)) hz0delta (Or.inr (by exact astra4wPowerNat105_003 hcq6)) hz0zeta (Or.inr (by exact astra4wPowerNat105_004 hcq2 hcq1 hcq6)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top_S07 hAne hBne hCne hFne (D := D) (E := E) (G := G) (by exact astra4wPowerNat105_005 hcq0) (by exact astra4wPowerNat105_006 hcq2 hcq0)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_114 hcq2 h hcq0 hcq1 hcq6 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat105_115 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_207 hcq2 h hcq0 hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_117 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_118 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_119 hcq2 h hcq0 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_208 hcq2 h hcq0 hcq1 hcq6)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_209 hcq2 h hcq0 hcq1 hcq6 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_122 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_210 hcq2 h hcq0 hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_124 hcq2 hcq0 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_125 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_126 hcq2 h hcq0 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_211 hcq2 h hcq0 hcq1 hcq6)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_212 hcq2 h hcq0 hcq1 hcq6 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_129 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_213 hcq2 h hcq0 hcq1 hcq6 hEn)
      · exact Or.inr (by exact astra4wPowerNat105_131 h hcq2 hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_132 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_133 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_134 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_135 hcq2 h hcq0 hcq1 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_136 h hcq2 hcq0 hcq1 hcq6)
  have hr1 : (muQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest14810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz hGz (by exact astra4wPowerNat105_007 hcq2 hcq0 hcq1 hcq6) (by exact astra4wPowerNat105_009 hcq6) (by exact astra4wPowerNat105_010 hcq2 hcq0 hcq6) hz1l hz1beta (Or.inr (by exact astra4wPowerNat105_012 hcq2 hcq0 hcq1 hcq6)) hz1delta (Or.inr (by exact astra4wPowerNat105_183 hcq2 hcq0 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat105_014 hcq2 hcq0 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat105_015 hcq2 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat105_016 hcq2 hcq0 hcq1 hcq6))
  have hct1 := muQuarticChamberFace14810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat105_017 hcq2 hcq0) (by exact astra4wPowerNat105_018 hcq2 hcq0 hcq1) (by exact astra4wPowerNat105_019 hcq0)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_137 hcq2 h hcq0 hcq1 hcq6 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat105_138 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_214 hcq2 h hcq0 hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_140 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_141 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_142 hcq2 h hcq0 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_215 hcq2 h hcq0 hcq1 hcq6)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_216 hcq2 h hcq0 hcq1 hcq6 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_145 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_217 hcq2 h hcq0 hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_147 hcq2 hcq0 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_148 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_149 hcq2 h hcq0 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_218 hcq2 h hcq0 hcq1 hcq6)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_219 hcq2 h hcq0 hcq1 hcq6 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_152 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_220 hcq2 h hcq0 hcq1 hcq6 hEn)
      · exact Or.inr (by exact astra4wPowerNat105_154 h hcq2 hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_155 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_156 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_157 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_158 hcq2 h hcq0 hcq1 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_221 h hcq2 hcq0 hcq1 hcq6)
  have hr2 : (xiQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest14810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hEz hGz (by exact astra4wPowerNat105_020 hcq2 hcq0 hcq1 hcq6) (by exact astra4wPowerNat105_022 hcq2 hcq0 hcq1 hcq6) (by exact astra4wPowerNat105_023 hcq2 hcq0 hcq1 hcq6) (by exact astra4wPowerNat105_024 hcq1 hcq6) (by exact astra4wPowerNat105_027 hcq6) (by exact astra4wPowerNat105_028 hcq2 hcq0 hcq1 hcq6) hz2l hz2beta (Or.inr (by exact astra4wPowerNat105_184 hcq2 hcq0 hcq1 hcq6)) hz2delta (Or.inr (by exact astra4wPowerNat105_030 hcq2 hcq0 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat105_031 hcq2 hcq0 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat105_185 hcq2 hcq0 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat105_033 hcq2 hcq0 hcq1 hcq6))
  have hct2 := xiQuarticChamberFace14810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat105_034 hcq2 hcq0)
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_160 hcq2 h hcq0 hcq1 hcq6 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat105_161 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_222 hcq2 h hcq0 hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_163 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_164 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_165 hcq2 h hcq0 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_223 hcq2 h hcq0 hcq1 hcq6)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_224 hcq2 h hcq0 hcq1 hcq6 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_168 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_225 hcq2 h hcq0 hcq1 hcq6 hAE hEn)
      · exact Or.inr (by exact astra4wPowerNat105_170 hcq2 hcq0 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_171 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_172 hcq2 h hcq0 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_226 hcq2 h hcq0 hcq1 hcq6)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_227 hcq2 h hcq0 hcq1 hcq6 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_175 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_228 hcq2 h hcq0 hcq1 hcq6 hEn)
      · exact Or.inr (by exact astra4wPowerNat105_177 h hcq2 hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_178 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_179 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_180 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat105_181 hcq2 h hcq0 hcq1 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_229 h hcq2 hcq0 hcq1 hcq6)
  have hr3 : (piQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest7810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hEz hGz (by exact astra4wPowerNat105_035 hcq6) (by exact astra4wPowerNat105_036 hcq2 hcq0 hcq1 hcq6) (by exact astra4wPowerNat105_038 hcq1 hcq6) (by exact astra4wPowerNat105_040 hcq6) (by exact astra4wPowerNat105_041 hcq0 hcq6) (by exact astra4wPowerNat105_043 hcq2 hcq0 hcq6) hz3l hz3beta (Or.inr (by exact astra4wPowerNat105_186 hcq2 hcq0 hcq1 hcq6)) hz3delta (Or.inr (by exact astra4wPowerNat105_187 hcq2 hcq0 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat105_188 hcq2 hcq0 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat105_049 hcq2 hcq0 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat105_050 hcq2 hcq0 hcq1 hcq6))
  have hct3 := piQuarticChamberFace7810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat105_051 hcq0) (by exact astra4wPowerNat105_052 hcq2 hcq0) (by exact astra4wPowerNat105_053 hcq2 hcq0 hcq1) (by exact astra4wPowerNat105_054 hcq0) (by exact astra4wPowerNat105_055 hcq2)
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
/-- Chamber `BCDEF` / `BF·CF·DD·BBB·BBC·BCC·CCC` dies on power system `S07` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEF7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF7810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat105_056 hcq2 h hcq1 hcq7 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat105_057 hcq6 hcq2 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_058 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_059 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_060 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_061 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_062 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_063 hcq2 h hcq0 hcq1 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_064 hcq6 hcq2 h hcq0 hcq1 hcq7)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_065 hcq2 h hcq1 hcq7 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat105_066 hcq6 hcq2 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_067 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_068 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_069 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_070 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_071 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_072 hcq2 h hcq0 hcq1 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_073 hcq6 hcq2 h hcq0 hcq1 hcq7)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_074 hcq6 hcq2 h hcq1 hcq7 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_075 hcq6 hcq2 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_076 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_077 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_078 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_079 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_080 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_081 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_082 hcq6 hcq2 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_083 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_084 hcq2 h hcq1 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_085 hcq6 hcq2 h hcq0 hcq1 hcq7)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_086 hcq6 hcq2 h hcq1 hcq7 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_087 hcq6 hcq2 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_088 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_089 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_090 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_091 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_092 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_093 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_094 hcq6 hcq2 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_095 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_096 hcq2 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_097 hcq2 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_098 hcq2 h hcq0 hcq1 hcq7)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_099 h hcq2 hcq0 hcq1 hcq7)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_100 h hcq2 hcq1 hcq7 hGn)
    · exact Or.inr (by exact astra4wPowerNat105_101 h hcq6 hcq2 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_102 h hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_103 h hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_104 h hcq6 hcq0 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_105 h hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_106 h hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_107 h hcq2 hcq0 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_108 h hcq6 hcq2 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_109 h hcq2 hcq0 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_110 h hcq2 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_111 h hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_112 h hcq2 hcq0 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat105_113 h hcq2 hcq1 hcq7)
  have hr0 : (kappaQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hGz (by exact astra4wPowerNat105_000 hcq7) (by exact astra4wPowerNat105_001 hcq6 hcq2) hz0l hz0beta (Or.inr (by exact astra4wPowerNat105_002 hcq2 hcq0 hcq1 hcq7)) hz0delta (Or.inr (by exact astra4wPowerNat105_003 hcq7)) hz0zeta (Or.inr (by exact astra4wPowerNat105_004 hcq2 hcq1 hcq7)) hz0theta
  have hct0 := kappaQuarticChamberFace6810_coeff_top_S07 hAne hBne hCne hFne (D := D) (E := E) (G := G) (by exact astra4wPowerNat105_005 hcq0) (by exact astra4wPowerNat105_006 hcq2 hcq0)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_114 hcq2 h hcq0 hcq1 hcq7 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat105_115 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_116 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_117 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_118 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_119 hcq2 h hcq0 hcq1 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_120 hcq6 hcq2 h hcq0 hcq1 hcq7)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_121 hcq6 hcq2 h hcq0 hcq1 hcq7 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_122 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_123 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_124 hcq2 hcq0 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_125 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_126 hcq2 h hcq0 hcq1 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_127 hcq6 hcq2 h hcq0 hcq1 hcq7)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_128 hcq6 hcq2 h hcq0 hcq1 hcq7 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_129 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_130 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_131 h hcq2 hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_132 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_133 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_134 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_135 hcq2 h hcq0 hcq1 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_136 h hcq2 hcq0 hcq1 hcq7)
  have hr1 : (muQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest14810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hGz (by exact astra4wPowerNat105_007 hcq2 hcq0 hcq1 hcq7) (by exact astra4wPowerNat105_008 hcq6 hcq0 hcq1 hcq7) (by exact astra4wPowerNat105_009 hcq7) (by exact astra4wPowerNat105_010 hcq2 hcq0 hcq7) (by exact astra4wPowerNat105_011 hcq6 hcq2 hcq0 hcq1) hz1l hz1beta (Or.inr (by exact astra4wPowerNat105_012 hcq2 hcq0 hcq1 hcq7)) hz1delta (Or.inr (by exact astra4wPowerNat105_013 hcq6 hcq2 hcq0 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat105_014 hcq2 hcq0 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat105_015 hcq2 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat105_016 hcq2 hcq0 hcq1 hcq7))
  have hct1 := muQuarticChamberFace14810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat105_017 hcq2 hcq0) (by exact astra4wPowerNat105_018 hcq2 hcq0 hcq1) (by exact astra4wPowerNat105_019 hcq0)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_137 hcq2 h hcq0 hcq1 hcq7 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat105_138 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_139 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_140 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_141 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_142 hcq2 h hcq0 hcq1 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_143 hcq6 hcq2 h hcq0 hcq1 hcq7)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_144 hcq6 hcq2 h hcq0 hcq1 hcq7 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_145 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_146 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_147 hcq2 hcq0 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_148 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_149 hcq2 h hcq0 hcq1 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_150 hcq6 hcq2 h hcq0 hcq1 hcq7)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_151 hcq6 hcq2 h hcq0 hcq1 hcq7 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_152 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_153 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_154 h hcq2 hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_155 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_156 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_157 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_158 hcq2 h hcq0 hcq1 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_159 h hcq6 hcq2 hcq0 hcq1 hcq7)
  have hr2 : (xiQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest14810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hGz (by exact astra4wPowerNat105_020 hcq2 hcq0 hcq1 hcq7) (by exact astra4wPowerNat105_021 hcq6 hcq0 hcq1) (by exact astra4wPowerNat105_022 hcq2 hcq0 hcq1 hcq7) (by exact astra4wPowerNat105_023 hcq2 hcq0 hcq1 hcq7) (by exact astra4wPowerNat105_024 hcq1 hcq7) (by exact astra4wPowerNat105_025 hcq6 hcq0 hcq1 hcq7) (by exact astra4wPowerNat105_026 hcq6 hcq0 hcq1) (by exact astra4wPowerNat105_027 hcq7) (by exact astra4wPowerNat105_028 hcq2 hcq0 hcq1 hcq7) hz2l hz2beta (Or.inr (by exact astra4wPowerNat105_029 hcq6 hcq2 hcq0 hcq1 hcq7)) hz2delta (Or.inr (by exact astra4wPowerNat105_030 hcq2 hcq0 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat105_031 hcq2 hcq0 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat105_032 hcq6 hcq2 hcq0 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat105_033 hcq2 hcq0 hcq1 hcq7))
  have hct2 := xiQuarticChamberFace14810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat105_034 hcq2 hcq0)
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_160 hcq2 h hcq0 hcq1 hcq7 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat105_161 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_162 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_163 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_164 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_165 hcq2 h hcq0 hcq1 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_166 hcq6 hcq2 h hcq0 hcq1 hcq7)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_167 hcq6 hcq2 h hcq0 hcq1 hcq7 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_168 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_169 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_170 hcq2 hcq0 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_171 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_172 hcq2 h hcq0 hcq1 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_173 hcq6 hcq2 h hcq0 hcq1 hcq7)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat105_174 hcq6 hcq2 h hcq0 hcq1 hcq7 hGn)
      · exact Or.inr (by exact astra4wPowerNat105_175 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_176 hcq6 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_177 h hcq2 hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_178 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_179 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_180 hcq2 h hcq0 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat105_181 hcq2 h hcq0 hcq1 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat105_182 h hcq6 hcq2 hcq0 hcq1 hcq7)
  have hr3 : (piQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest7810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hGz (by exact astra4wPowerNat105_035 hcq7) (by exact astra4wPowerNat105_036 hcq2 hcq0 hcq1 hcq7) (by exact astra4wPowerNat105_037 hcq6 hcq2) (by exact astra4wPowerNat105_038 hcq1 hcq7) (by exact astra4wPowerNat105_039 hcq6 hcq0 hcq1 hcq7) (by exact astra4wPowerNat105_040 hcq7) (by exact astra4wPowerNat105_041 hcq0 hcq7) (by exact astra4wPowerNat105_042 hcq6 hcq2 hcq1 hcq7) (by exact astra4wPowerNat105_043 hcq2 hcq0 hcq7) (by exact astra4wPowerNat105_044 hcq6 hcq2 hcq0 hcq1) (by exact astra4wPowerNat105_045 hcq6 hcq2 hcq7) hz3l hz3beta (Or.inr (by exact astra4wPowerNat105_046 hcq6 hcq2 hcq0 hcq1 hcq7)) hz3delta (Or.inr (by exact astra4wPowerNat105_047 hcq6 hcq2 hcq0 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat105_048 hcq6 hcq2 hcq0 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat105_049 hcq2 hcq0 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat105_050 hcq2 hcq0 hcq1 hcq7))
  have hct3 := piQuarticChamberFace7810_coeff_top_S07 hAne hBne hCne hDne hFne (E := E) (G := G) (by exact astra4wPowerNat105_051 hcq0) (by exact astra4wPowerNat105_052 hcq2 hcq0) (by exact astra4wPowerNat105_053 hcq2 hcq0 hcq1) (by exact astra4wPowerNat105_054 hcq0) (by exact astra4wPowerNat105_055 hcq2)
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
