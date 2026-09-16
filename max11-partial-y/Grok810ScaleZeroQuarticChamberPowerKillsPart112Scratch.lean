import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
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
private theorem astra4wPowerNat112_000
    {a b c f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    : a + 3 * b < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_001
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * b + d < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_002
    {b c f : ℕ}
    (h0 : b + c < f)
    : b + 2 * c < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_003
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : b + c < (c + f) ∧ f < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_004
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : d < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_005
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : b < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_006
    {a b c f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    : a < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_007
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : a + 2 * b + c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_008
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 4 * b < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_009
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : a + b + f < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_010
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : e < a + c)
    : 2 * b + e < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_011
    {a b c d e f : ℕ}
    (h0 : b + c < f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : b + c + d < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_012
    {a c d e f : ℕ}
    (h0 : c + f = d + e)
    (h1 : e < a + c)
    : d + f < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_013
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + 2 * b < (a + 2 * d) ∧ b + d < (a + 2 * d) ∧ 2 * c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_014
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * b < (a + 2 * d) ∧ e < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_015
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + b < (a + 2 * d) ∧ d < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_016
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_017
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : b < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_018
    {a c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    : 3 * c = a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_019
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : c + f = d + e)
    : 2 * e = a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_020
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + 4 * b < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_021
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    : a + 2 * b + e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_022
    {a b c d f : ℕ}
    (h0 : b + c < f)
    : a + b + c + d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_023
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * b + d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_024
    {a b c d e f : ℕ}
    (h0 : b + c < f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 2 * b + 2 * c < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_025
    {a b c d e f : ℕ}
    (h0 : b + c < f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : b + c + f < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_026
    {a b c d e f : ℕ}
    (h0 : b + c < f)
    (h1 : e < a + c)
    : b + d + e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_027
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : c + 2 * d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_028
    {a c d e f : ℕ}
    (h0 : c + f = d + e)
    (h1 : e < a + c)
    : 2 * f < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_029
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + b + d < (a + d + f) ∧ 2 * b + c < (a + d + f) ∧ b + f < (a + d + f) ∧ c + e < (a + d + f) ∧ 2 * d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_030
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + 2 * b < (a + d + f) ∧ b + d < (a + d + f) ∧ 2 * c < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_031
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + d < (a + d + f) ∧ b + c < (a + d + f) ∧ f < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_032
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * b < (a + d + f) ∧ e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_033
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_034
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    : 2 * c + e = a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_035
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : 2 * a + 4 * b < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_036
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + 3 * b + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_037
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : a + 2 * b + 2 * c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_038
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 4 * b + c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_039
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : a + b + c + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_040
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    : a + b + d + e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_041
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 3 * b + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_042
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : e < a + c)
    : 2 * b + c + e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_043
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * b + 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_044
    {a b c d e f : ℕ}
    (h0 : b + c < f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : b + 2 * c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_045
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : e < a + c)
    : b + e + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_046
    {a c d e f : ℕ}
    (h0 : c + f = d + e)
    (h1 : e < a + c)
    : c + d + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_047
    {a c d e : ℕ}
    (h0 : e < a + c)
    : 2 * d + e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_048
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + 2 * b + c < (a + c + 2 * d) ∧ 4 * b < (a + c + 2 * d) ∧ a + 2 * d < (a + c + 2 * d) ∧ 2 * b + e < (a + c + 2 * d) ∧ b + c + d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ d + f < (a + c + 2 * d) ∧ 2 * e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_049
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + b + d < (a + c + 2 * d) ∧ 2 * b + c < (a + c + 2 * d) ∧ b + f < (a + c + 2 * d) ∧ c + e < (a + c + 2 * d) ∧ 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_050
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + b + c < (a + c + 2 * d) ∧ 3 * b < (a + c + 2 * d) ∧ a + f < (a + c + 2 * d) ∧ b + e < (a + c + 2 * d) ∧ c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_051
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + 2 * b < (a + c + 2 * d) ∧ b + d < (a + c + 2 * d) ∧ 2 * c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_052
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : b + c < (a + c + 2 * d) ∧ f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_053
    {a c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    : 4 * c = a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_054
    {a c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    : a + 2 * f = a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_055
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : c + f = d + e)
    : c + 2 * e = a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_056
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 6 * a ≤ d + g)
    (h3 : a + 2 * b < 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : g = 0)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_057
    {a c e f : ℕ}
    (h0 : 6 * a ≤ e + f)
    (h1 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_058
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_059
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 6 * a ≤ 2 * b + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_060
    {a b c e f : ℕ}
    (h0 : 6 * a ≤ b + c + e)
    (h1 : b + c < f)
    (h2 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_061
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 6 * a ≤ b + 2 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_062
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 6 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_063
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 6 * a ≤ 3 * b + c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_064
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a < c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 5 * a < c + f ∧ 3 * a + c < c + f ∧ 2 * a + 2 * b < c + f ∧ 2 * a + e < c + f ∧ a + b + d < c + f ∧ a + 2 * c < c + f ∧ 2 * b + c < c + f ∧ b + f < c + f ∧ c + e < c + f ∧ 2 * d < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_065
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 5 * a ≤ d + g)
    (h3 : a + 2 * b < 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : g = 0)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_066
    {a c e f : ℕ}
    (h0 : 5 * a ≤ e + f)
    (h1 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_067
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_068
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 2 * b + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_069
    {a b c e f : ℕ}
    (h0 : 5 * a ≤ b + c + e)
    (h1 : b + c < f)
    (h2 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_070
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ b + 2 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_071
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_072
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 3 * b + c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_073
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a < c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a < c + f ∧ 2 * a + c < c + f ∧ a + 2 * b < c + f ∧ a + e < c + f ∧ b + d < c + f ∧ 2 * c < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_074
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 4 * a ≤ d + g)
    (h3 : a + 2 * b < 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : g = 0)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_075
    {a c e f : ℕ}
    (h0 : 4 * a ≤ e + f)
    (h1 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_076
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_077
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_078
    {a b c e f : ℕ}
    (h0 : 4 * a ≤ b + c + e)
    (h1 : b + c < f)
    (h2 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_079
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_080
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_081
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_082
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ b + e)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_083
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_084
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_085
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a < c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a < c + f ∧ a + c < c + f ∧ 2 * b < c + f ∧ e < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_086
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 3 * a ≤ d + g)
    (h3 : a + 2 * b < 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : g = 0)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_087
    {a c e f : ℕ}
    (h0 : 3 * a ≤ e + f)
    (h1 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_088
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_089
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_090
    {a b c e f : ℕ}
    (h0 : 3 * a ≤ b + c + e)
    (h1 : b + c < f)
    (h2 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_091
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_092
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_093
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_094
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + e)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_095
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_096
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : a ≤ b)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_097
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_098
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_099
    {a b c d e f : ℕ}
    (h0 : 2 * a < c + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f ∧ c < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_100
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 4 * b)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_101
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 7 * a ≤ 4 * c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_102
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_103
    {a b c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_104
    {a b c d e f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_105
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    (h4 : g = 0)
    : ¬ (15 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_106
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_107
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 4 * b)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_108
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 4 * c)
    (h2 : b + c < f)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_109
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_110
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 9 * a ≤ 4 * e)
    (h2 : b + c < f)
    (h3 : e < a + c)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_111
    {a b c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_112
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    (h4 : g = 0)
    : ¬ (13 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_113
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a + b < a + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_114
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : a ≤ 4 * b)
    (h3 : b + c < f)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_115
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 4 * c)
    (h2 : b + c < f)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_116
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_117
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 7 * a ≤ 4 * e)
    (h2 : b + c < f)
    (h3 : e < a + c)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_118
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 9 * a ≤ 4 * f)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_119
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    (h4 : g = 0)
    : ¬ (11 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_120
    {a b c d e f : ℕ}
    (h0 : 2 * a + b < a + 2 * d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_121
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * b < 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : g < 4 * a)
    (h6 : g = 0)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_122
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_123
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_124
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_125
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_126
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_127
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a + d < a + d + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + c + e < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ e + f < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_128
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * b < 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : g = 0)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_129
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_130
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_131
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : a ≤ b)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_132
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_133
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_134
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a + d < a + d + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + d < a + d + f ∧ 2 * a + b + c < a + d + f ∧ a + 3 * b < a + d + f ∧ 2 * a + f < a + d + f ∧ a + b + e < a + d + f ∧ a + c + d < a + d + f ∧ 2 * b + d < a + d + f ∧ b + 2 * c < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_135
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * b < 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : g = 0)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_136
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_137
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_138
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_139
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_140
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_141
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_142
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_143
    {a b c d e f : ℕ}
    (h0 : 2 * a + d < a + d + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + d < a + d + f ∧ a + b + c < a + d + f ∧ 3 * b < a + d + f ∧ a + f < a + d + f ∧ b + e < a + d + f ∧ c + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_144
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * b < 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : g < 4 * a)
    (h6 : g = 0)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_145
    {a c d e f : ℕ}
    (h0 : 5 * a ≤ c + f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_146
    {a c d e f : ℕ}
    (h0 : 5 * a ≤ d + e)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_147
    {a b c d e f : ℕ}
    (h0 : 4 * a ≤ 3 * b)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_148
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_149
    {a b c d e f : ℕ}
    (h0 : 5 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_150
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a + f < a + c + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d ∧ 3 * a + b + e < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * b + f < a + c + 2 * d ∧ a + b + c + e < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 3 * b + e < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ b + d + f < a + c + 2 * d ∧ b + 2 * e < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_151
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * b < 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : g = 0)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_152
    {a c d e f : ℕ}
    (h0 : 4 * a ≤ c + f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_153
    {a c d e f : ℕ}
    (h0 : 4 * a ≤ d + e)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_154
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : a ≤ b)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_155
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_156
    {a b c d e f : ℕ}
    (h0 : 4 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_157
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a + f < a + c + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + b + c < a + c + 2 * d ∧ 2 * a + 3 * b < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d ∧ 2 * a + b + e < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + 2 * b + d < a + c + 2 * d ∧ a + b + 2 * c < a + c + 2 * d ∧ 3 * b + c < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ 2 * b + f < a + c + 2 * d ∧ b + c + e < a + c + 2 * d ∧ b + 2 * d < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d ∧ e + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_158
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * b < 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : g = 0)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_159
    {a c d e f : ℕ}
    (h0 : 3 * a ≤ c + f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_160
    {a c d e f : ℕ}
    (h0 : 3 * a ≤ d + e)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_161
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_162
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_163
    {a b c d e f : ℕ}
    (h0 : 3 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_164
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_165
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_166
    {a b c d e f : ℕ}
    (h0 : 2 * a + f < a + c + 2 * d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + b + c < a + c + 2 * d ∧ a + 3 * b < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d ∧ a + b + e < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ 2 * b + d < a + c + 2 * d ∧ b + 2 * c < a + c + 2 * d ∧ c + f < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_167
    {a c d e f : ℕ}
    (h0 : 0 < c + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : f < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_168
    {a c d e f : ℕ}
    (h0 : 0 < c + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : d < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_169
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 2 * c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_170
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : e < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_171
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : d < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_172
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_173
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : c + e < (a + d + f) ∧ 2 * d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_174
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 2 * c < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_175
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + d < (a + d + f) ∧ f < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_176
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_177
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_178
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + 2 * d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ d + f < (a + c + 2 * d) ∧ 2 * e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_179
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : c + e < (a + c + 2 * d) ∧ 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_180
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + f < (a + c + 2 * d) ∧ c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_181
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 2 * c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_182
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_183
    {a c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 6 * a ≤ d + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_184
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_185
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 6 * a ≤ 2 * b + f)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_186
    {a b c d e f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 6 * a ≤ b + c + e)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    (h6 : c + f = d + e)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_187
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 6 * a ≤ b + 2 * d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_188
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 6 * a ≤ 3 * b + c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_189
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a < c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 5 * a < c + f ∧ 3 * a + c < c + f ∧ 2 * a + e < c + f ∧ a + 2 * c < c + f ∧ c + e < c + f ∧ 2 * d < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_190
    {a c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 5 * a ≤ d + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_191
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 4 * a ≤ 2 * b + d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_192
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 5 * a ≤ 2 * b + f)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_193
    {a b c d e f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 5 * a ≤ b + c + e)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    (h6 : c + f = d + e)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_194
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 5 * a ≤ b + 2 * d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_195
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 5 * a ≤ 3 * b + c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_196
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a < c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a < c + f ∧ 2 * a + c < c + f ∧ a + e < c + f ∧ 2 * c < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_197
    {a c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 4 * a ≤ d + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : g = 0)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_198
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_199
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 4 * a ≤ 2 * b + f)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_200
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_201
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_202
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 4 * a ≤ 3 * b + c)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_203
    {a b c d e f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 4 * a ≤ b + e)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_204
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 4 * a ≤ 3 * b)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_205
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a < c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a < c + f ∧ a + c < c + f ∧ e < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_206
    {a c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 3 * a ≤ d + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : g = 0)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_207
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_208
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_209
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_210
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_211
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 3 * a ≤ 3 * b + c)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_212
    {a b c d e f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 3 * a ≤ b + e)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_213
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : a ≤ b)
    (h4 : b = 0)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_214
    {a b c d e f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 3 * a ≤ b + c)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_215
    {a c d e f : ℕ}
    (h0 : 2 * a < c + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f ∧ c < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_216
    {a c d e f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    (h5 : g = 0)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_217
    {a c e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_218
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : a ≤ 2 * b + d)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_219
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_220
    {a b c e f : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b = 0)
    (h3 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_221
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_222
    {a c d e f : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_223
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_224
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_225
    {a c d e f : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_226
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_227
    {a c d e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_228
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * b < 3 * a)
    (h2 : 2 * c + 2 * f = a + 4 * d)
    (h3 : 2 * d < a + 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_229
    {a c d e f : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_230
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b = 0)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : ¬ (5 * a ≤ 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_231
    {a c d e f : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_232
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_233
    {a c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_234
    {a c d e f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_235
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    (h4 : g = 0)
    : ¬ (15 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_236
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a + d < a + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_237
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b = 0)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : ¬ (3 * a ≤ 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_238
    {a c d e f : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_239
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_240
    {a c d e f : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_241
    {a c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_242
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    (h4 : g = 0)
    : ¬ (13 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_243
    {a c d e f : ℕ}
    (h0 : 2 * a + d < a + 2 * d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_244
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b = 0)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : ¬ (a ≤ 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_245
    {a c d e f : ℕ}
    (h0 : 3 * a ≤ 4 * c)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_246
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_247
    {a c d e f : ℕ}
    (h0 : 7 * a ≤ 4 * e)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_248
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 9 * a ≤ 4 * f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_249
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    (h4 : g = 0)
    : ¬ (11 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_250
    {a c d e f : ℕ}
    (h0 : a + d < a + 2 * d)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : a + d < a + 2 * d ∧ f < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_251
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : g < 4 * a)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_252
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 4 * a ≤ 3 * b)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_253
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_254
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 5 * a ≤ b + 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_255
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a + d < a + d + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a + d < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * c + d < a + d + f ∧ e + f < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_256
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : g = 0)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_257
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : a ≤ b)
    (h4 : b = 0)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_258
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 4 * a ≤ 2 * b + d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_259
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 4 * a ≤ b + 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_260
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a + d < a + d + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + d + f ∧ 2 * a + f < a + d + f ∧ a + c + d < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_261
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : g = 0)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_262
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_263
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_264
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_265
    {a b c d e f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 3 * a ≤ b + c)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_266
    {a c d e f : ℕ}
    (h0 : 2 * a + d < a + d + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + d + f ∧ a + f < a + d + f ∧ c + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_267
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : g < 4 * a)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_268
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 4 * a ≤ 3 * b)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_269
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_270
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 5 * a ≤ b + 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_271
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a + f < a + c + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a + f < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_272
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : g = 0)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_273
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : a ≤ b)
    (h4 : b = 0)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_274
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 4 * a ≤ 2 * b + d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_275
    {a b c d f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 4 * a ≤ b + 2 * c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_276
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a + f < a + c + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d ∧ e + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_277
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : g = 0)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_278
    {a b c d f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_279
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_280
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b = 0)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_281
    {a b c d e f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 3 * a ≤ b + c)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_282
    {a c d e f : ℕ}
    (h0 : 2 * a + f < a + c + 2 * d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + f < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ c + f < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_283
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_284
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : b + 2 * c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_285
    {a b c f g : ℕ}
    (h0 : c + f < b + g)
    (h1 : g = a + 2 * b)
    : c + f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_286
    {a b c d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_287
    {a b d : ℕ}
    (h0 : d < a + b)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_288
    {a b d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_289
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : b + g = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_290
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : g = a + 2 * b)
    : d + e = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_291
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_292
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    : a + b + c + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_293
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_294
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_295
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : b + g = d + e)
    (h3 : g = a + 2 * b)
    : a + d + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_296
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_297
    {a b c d e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * f < 2 * g)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_298
    {a b d e : ℕ}
    (h0 : d < a + b)
    : b + d + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_299
    {a b c e : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : 2 * c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_300
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_301
    {a b d e f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_302
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_303
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_304
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_305
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_306
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_307
    {a b e g : ℕ}
    (h0 : g = a + 2 * b)
    : e + g = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_308
    {a b d : ℕ}
    (h0 : d < a + b)
    : a + 3 * b + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_309
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : a + 2 * b + 2 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_310
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 4 * b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_311
    {a b c f g : ℕ}
    (h0 : c + f < b + g)
    (h1 : g = a + 2 * b)
    : a + b + c + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_312
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : g = a + 2 * b)
    : a + c + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_313
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : d < a + b)
    : 3 * b + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_314
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    : 2 * b + c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_315
    {a b d : ℕ}
    (h0 : d < a + b)
    : 2 * b + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_316
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : d < a + b)
    : b + 2 * c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_317
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : 4 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_318
    {a b f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : g = a + 2 * b)
    : a + 2 * f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_319
    {a b d g : ℕ}
    (h0 : d < a + b)
    (h1 : g = a + 2 * b)
    : b + d + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_320
    {a b d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : b + e + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_321
    {a b c g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : g = a + 2 * b)
    : 2 * c + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_322
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * f < 2 * g)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : c + d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_323
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : b + g = d + e)
    (h3 : g = a + 2 * b)
    : c + 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_324
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 2 * d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_325
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_326
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_327
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_328
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_329
    {a b c d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : b + c < (2 * a + 4 * b) ∧ f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_330
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : a + 2 * b + g = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_331
    {a b d e g : ℕ}
    (h0 : b + g = d + e)
    (h1 : g = a + 2 * b)
    : a + b + d + e = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_332
    {a b g : ℕ}
    (h0 : g = a + 2 * b)
    : 2 * g = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_333
    {a b d g : ℕ}
    (h0 : 6 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_334
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
private theorem astra4wPowerNat112_335
    {a b d : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_336
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 6 * a ≤ 2 * b + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_337
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 6 * a ≤ b + c + e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_338
    {a b d : ℕ}
    (h0 : 6 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_339
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 6 * a ≤ 2 * c + d)
    (h2 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_340
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 6 * a ≤ 3 * b + c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_341
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a < a + 3 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_342
    {a b d g : ℕ}
    (h0 : 5 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_343
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
private theorem astra4wPowerNat112_344
    {a b d : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_345
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 5 * a ≤ 2 * b + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_346
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a ≤ b + c + e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_347
    {a b d : ℕ}
    (h0 : 5 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_348
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_349
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a ≤ 3 * b + c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_350
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
private theorem astra4wPowerNat112_351
    {a b d g : ℕ}
    (h0 : 4 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_352
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
private theorem astra4wPowerNat112_353
    {a b d : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_354
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_355
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a ≤ b + c + e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_356
    {a b d : ℕ}
    (h0 : 4 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_357
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_358
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a ≤ 3 * b + c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_359
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ b + e)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_360
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a ≤ c + d)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_361
    {a b d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_362
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
private theorem astra4wPowerNat112_363
    {a b d g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_364
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
private theorem astra4wPowerNat112_365
    {a b d : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_366
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_367
    {a b c d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ b + c + e)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_368
    {a b d : ℕ}
    (h0 : 3 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_369
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_370
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ 3 * b + c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_371
    {a b d e g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ b + e)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_372
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ c + d)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_373
    {a b d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : a ≤ b)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_374
    {a b d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_375
    {a b c d g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ b + c)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_376
    {a b c d g : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_377
    {a b d g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : d < a + b)
    (h2 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_378
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
private theorem astra4wPowerNat112_379
    {a b d : ℕ}
    (h0 : a ≤ 2 * b + d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_380
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_381
    {a b c d e g : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_382
    {a b d : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_383
    {a b c d : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_384
    {a b c d g : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_385
    {a b d e g : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_386
    {a b c d g : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_387
    {a b d g : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_388
    {a b d f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_389
    {a b c d g : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_390
    {a b d g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_391
    {a b d e g : ℕ}
    (h0 : 5 * a ≤ b + g)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_392
    {a b c d e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_393
    {a b d e : ℕ}
    (h0 : 5 * a ≤ d + e)
    (h1 : d < a + b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_394
    {a b d e g : ℕ}
    (h0 : 4 * a ≤ 3 * b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_395
    {a b d e g : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_396
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a ≤ b + 2 * c)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_397
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 4 * a + d < a + 2 * b + e)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_398
    {a b d e g : ℕ}
    (h0 : 4 * a ≤ b + g)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_399
    {a b c d e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_400
    {a b d e : ℕ}
    (h0 : 4 * a ≤ d + e)
    (h1 : d < a + b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_401
    {a b d e g : ℕ}
    (h0 : a ≤ b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_402
    {a b d e g : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_403
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 4 * a ≤ b + 2 * c)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_404
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a + d < a + 2 * b + e)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : c + f < b + g)
    (h6 : d < a + b)
    (h7 : g = a + 2 * b)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_405
    {a b d e g : ℕ}
    (h0 : 3 * a ≤ b + g)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_406
    {a b c d e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : b + g = d + e)
    (h4 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_407
    {a b d e : ℕ}
    (h0 : 3 * a ≤ d + e)
    (h1 : d < a + b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_408
    {a b d e g : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_409
    {a b d e g : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : b + g = d + e)
    (h2 : d < a + b)
    (h3 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_410
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a ≤ b + 2 * c)
    (h2 : b + g = d + e)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_411
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
private theorem astra4wPowerNat112_412
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
private theorem astra4wPowerNat112_413
    {a b c d e f g : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_414
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a ≤ 4 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_415
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 7 * a ≤ 4 * c)
    (h3 : b + g = d + e)
    (h4 : c + f < b + g)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_416
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 9 * a ≤ 4 * d)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_417
    {a b c d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_418
    {a b c d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_419
    {a b c d e f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_420
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a + b + e < 2 * a + 4 * b ∧ 4 * a + b + c < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : c + f < b + g)
    (h6 : d < a + b)
    (h7 : g = a + 2 * b)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_421
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a ≤ 4 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_422
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 5 * a ≤ 4 * c)
    (h3 : b + g = d + e)
    (h4 : c + f < b + g)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_423
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 7 * a ≤ 4 * d)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_424
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 9 * a ≤ 4 * e)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_425
    {a b c d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_426
    {a b c d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_427
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_428
    {a b c f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a ≤ 4 * b)
    (h3 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_429
    {a b c f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a ≤ 4 * c)
    (h2 : c + f < b + g)
    (h3 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_430
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : a + 2 * f < 2 * g)
    (h3 : d < a + b)
    (h4 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_431
    {a b c d e f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 7 * a ≤ 4 * e)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_432
    {a b c d f g : ℕ}
    (h0 : 2 * b + 2 * g = a + 4 * d)
    (h1 : 2 * c < a + 2 * b)
    (h2 : 9 * a ≤ 4 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_433
    {a b c d f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : d < a + b)
    (h5 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat112_434
    {a b c d e f g : ℕ}
    (h0 : 2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b)
    (h1 : 2 * b + 2 * g = a + 4 * d)
    (h2 : 2 * c < a + 2 * b)
    (h3 : a + 2 * f < 2 * g)
    (h4 : b + g = d + e)
    (h5 : d < a + b)
    (h6 : g = a + 2 * b)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BG·DD·DE·EE·BBB` dies on power system `S14` (carriers κ, ξ, π). -/
theorem quarticChamberBCDEFG68810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG68810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat112_333 h hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_334 hcq0 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_335 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_336 hcq0 h hcq4 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_337 hcq0 hcq6 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_338 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_339 hcq6 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_340 hcq0 hcq6 h hcq8 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_341 hcq0 hcq6 h hcq4 hcq1 hcq8 hcq3)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_342 h hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_343 hcq0 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_344 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_345 hcq0 h hcq4 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_346 hcq0 hcq6 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_347 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_348 hcq6 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_349 hcq0 hcq6 h hcq8 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_350 hcq0 hcq6 h hcq1 hcq8 hcq3)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_351 h hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_352 hcq0 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_353 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_354 hcq0 h hcq4 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_355 hcq0 hcq6 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_356 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_357 hcq6 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_358 hcq0 hcq6 h hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_359 hcq0 h hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_360 hcq0 hcq6 h hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_361 hcq0 h hcq8 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_362 hcq0 hcq6 h hcq1 hcq8 hcq3)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_363 h hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_364 hcq0 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_365 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_366 hcq0 h hcq4 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_367 hcq0 hcq6 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_368 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_369 hcq6 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_370 hcq0 hcq6 h hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_371 hcq0 h hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_372 hcq0 hcq6 h hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_373 hcq0 h hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_374 hcq0 h hcq4 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_375 hcq0 hcq6 h hcq8 hcq3)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_376 h hcq0 hcq6 hcq8 hcq3)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_377 h hcq8 hcq3)
    · exact Or.inr (by exact astra4wPowerNat112_378 h hcq0 hcq4 hcq1 hcq8 hcq3)
    · exact Or.inr (by exact astra4wPowerNat112_379 h hcq8)
    · exact Or.inr (by exact astra4wPowerNat112_380 h hcq0 hcq4 hcq8)
    · exact Or.inr (by exact astra4wPowerNat112_381 h hcq0 hcq6 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat112_382 h hcq8)
    · exact Or.inr (by exact astra4wPowerNat112_383 h hcq6 hcq8)
    · exact Or.inr (by exact astra4wPowerNat112_384 h hcq0 hcq6 hcq8 hcq3)
    · exact Or.inr (by exact astra4wPowerNat112_385 h hcq0 hcq1 hcq8 hcq3)
    · exact Or.inr (by exact astra4wPowerNat112_386 h hcq0 hcq6 hcq8 hcq3)
    · exact Or.inr (by exact astra4wPowerNat112_387 h hcq0 hcq8 hcq3)
    · exact Or.inr (by exact astra4wPowerNat112_388 h hcq0 hcq4 hcq8)
    · exact Or.inr (by exact astra4wPowerNat112_389 h hcq0 hcq6 hcq8 hcq3)
    · exact Or.inr (by exact astra4wPowerNat112_390 h hcq0 hcq8 hcq3)
  have hr0 : (kappaQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest13810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat112_283 hcq8) (by exact astra4wPowerNat112_284 hcq6) (by exact astra4wPowerNat112_285 hcq5 hcq3) hz0l hz0beta (Or.inr (by exact astra4wPowerNat112_286 hcq0 hcq6 hcq4 hcq8 hcq3)) hz0delta (Or.inr (by exact astra4wPowerNat112_287 hcq8)) hz0zeta (Or.inr (by exact astra4wPowerNat112_288 hcq0 hcq8 hcq3)) hz0theta
  have hct0 := kappaQuarticChamberFace13810_coeff_top_S14 hAne hBne hDne hEne hGne (C := C) (F := F) (by exact astra4wPowerNat112_289 hcq3) (by exact astra4wPowerNat112_290 hcq1 hcq3)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_391 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_392 hcq6 h hcq4 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_393 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_394 h hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_395 h hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_396 hcq6 h hcq1 hcq8 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_397 hcq0 hcq6 h hcq4 hcq1 hcq8 hcq3)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_398 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_399 hcq6 h hcq4 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_400 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_401 h hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_402 h hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_403 hcq6 h hcq1 hcq8 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_404 hcq0 hcq6 h hcq4 hcq1 hcq5 hcq8 hcq3)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_405 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_406 hcq6 h hcq4 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_407 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat112_408 h hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_409 h hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_410 hcq6 h hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_411 hcq0 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_412 hcq0 hcq6 h hcq1 hcq8 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_413 h hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)
  have hr1 : (xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest19810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat112_291 hcq1 hcq8 hcq3) (by exact astra4wPowerNat112_292 hcq0 hcq6 hcq1) (by exact astra4wPowerNat112_293 hcq1 hcq8 hcq3) (by exact astra4wPowerNat112_294 hcq6 hcq1 hcq8 hcq3) (by exact astra4wPowerNat112_295 hcq0 hcq4 hcq1 hcq3) (by exact astra4wPowerNat112_296 hcq1 hcq8) (by exact astra4wPowerNat112_297 hcq6 hcq4 hcq1 hcq8) (by exact astra4wPowerNat112_298 hcq8) (by exact astra4wPowerNat112_299 hcq6) (by exact astra4wPowerNat112_300 hcq0 hcq6 hcq1 hcq8) (by exact astra4wPowerNat112_301 hcq4 hcq1 hcq8 hcq3) hz1l hz1beta (Or.inr (by exact astra4wPowerNat112_302 hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)) hz1delta (Or.inr (by exact astra4wPowerNat112_303 hcq6 hcq1 hcq8 hcq3)) (Or.inr (by exact astra4wPowerNat112_304 hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)) (Or.inr (by exact astra4wPowerNat112_305 hcq0 hcq1 hcq8 hcq3)) (Or.inr (by exact astra4wPowerNat112_306 hcq1 hcq8 hcq3))
  have hct1 := xiQuarticChamberFace19810_coeff_top_S14 hAne hBne hEne hGne (C := C) (D := D) (F := F) (by exact astra4wPowerNat112_307 hcq3)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_414 hcq0 hcq6 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_415 hcq0 hcq6 h hcq1 hcq5 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_416 hcq0 hcq6 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_417 h hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_418 h hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_419 h hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_420 hcq0 hcq6 h hcq4 hcq1 hcq5 hcq8 hcq3)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_421 hcq0 hcq6 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_422 hcq0 hcq6 h hcq1 hcq5 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_423 hcq0 hcq6 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_424 hcq0 hcq6 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_425 h hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_426 h hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_427 hcq0 hcq6 h hcq4 hcq1 hcq8 hcq3)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_428 hcq6 hcq4 h hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_429 hcq6 h hcq5 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_430 hcq6 h hcq4 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_431 hcq0 hcq6 h hcq4 hcq1 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_432 hcq0 hcq6 h hcq4 hcq8 hcq3)
      · exact Or.inr (by exact astra4wPowerNat112_433 h hcq0 hcq6 hcq4 hcq8 hcq3)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_434 h hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)
  have hr2 : (piQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest11810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by exact astra4wPowerNat112_308 hcq8) (by exact astra4wPowerNat112_309 hcq6) (by exact astra4wPowerNat112_310 hcq0 hcq6 hcq8 hcq3) (by exact astra4wPowerNat112_311 hcq5 hcq3) (by exact astra4wPowerNat112_312 hcq0 hcq6 hcq3) (by exact astra4wPowerNat112_313 hcq0 hcq4 hcq8) (by exact astra4wPowerNat112_314 hcq0 hcq6 hcq1 hcq8) (by exact astra4wPowerNat112_315 hcq8) (by exact astra4wPowerNat112_316 hcq6 hcq8) (by exact astra4wPowerNat112_317 hcq6) (by exact astra4wPowerNat112_318 hcq4 hcq3) (by exact astra4wPowerNat112_319 hcq8 hcq3) (by exact astra4wPowerNat112_320 hcq0 hcq4 hcq1 hcq8 hcq3) (by exact astra4wPowerNat112_321 hcq6 hcq3) (by exact astra4wPowerNat112_322 hcq6 hcq4 hcq8 hcq3) (by exact astra4wPowerNat112_323 hcq0 hcq6 hcq1 hcq3) (by exact astra4wPowerNat112_324 hcq1 hcq8 hcq3) hz2l hz2beta (Or.inr (by exact astra4wPowerNat112_325 hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)) hz2delta (Or.inr (by exact astra4wPowerNat112_326 hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)) (Or.inr (by exact astra4wPowerNat112_327 hcq0 hcq6 hcq4 hcq1 hcq8 hcq3)) (Or.inr (by exact astra4wPowerNat112_328 hcq0 hcq6 hcq8 hcq3)) (Or.inr (by exact astra4wPowerNat112_329 hcq0 hcq6 hcq4 hcq8 hcq3))
  have hct2 := piQuarticChamberFace11810_coeff_top_S14 hAne hBne hDne hEne hGne (C := C) (F := F) (by exact astra4wPowerNat112_330 hcq3) (by exact astra4wPowerNat112_331 hcq1 hcq3) (by exact astra4wPowerNat112_332 hcq3)
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
/-- Chamber `CDEF` / `CF·DD·DE·EE·CCC` dies on power system `S15` (carriers κ, μ, ξ, π). -/
theorem quarticChamberCDEF7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF7810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
  have hdp0 : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hGn hcq0 hcq1 hcq3 hcq4 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_183 hcq0 hcq4 h hcq3 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat112_057 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_184 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_185 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_186 hAB hcq0 hcq4 h hcq3 hBn hcq1)
      · exact Or.inr (by exact astra4wPowerNat112_187 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_062 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_188 hAB hcq0 hcq4 h hcq3 hBn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_189 hcq0 h hcq3 hcq1 hcq5)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_190 hcq0 hcq4 h hcq3 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat112_066 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_191 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_192 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_193 hAB hcq0 hcq4 h hcq3 hBn hcq1)
      · exact Or.inr (by exact astra4wPowerNat112_194 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_071 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_195 hAB hcq0 hcq4 h hcq3 hBn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_196 hcq0 h hcq3 hcq1 hcq5)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_197 hcq0 hcq4 h hcq3 hGn)
      · exact Or.inr (by exact astra4wPowerNat112_075 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_198 hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_199 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_200 hcq0 h hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_201 hcq0 h hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_080 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_202 hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_203 hAB hcq0 h hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_083 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_204 hcq0 hcq4 h hcq3 hBn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_205 hcq0 h hcq3 hcq1 hcq5)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_206 hcq0 hcq4 h hcq3 hGn)
      · exact Or.inr (by exact astra4wPowerNat112_087 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_207 h hcq0 hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_208 hcq0 h hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_209 hcq0 h hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_210 hcq0 h hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_092 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_211 hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_212 hAB hcq0 h hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_095 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_213 hcq0 hcq4 hcq3 h hBn)
      · exact Or.inr (by exact astra4wPowerNat112_097 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_214 hAB hcq0 h hcq3 hBn hcq1 hcq5)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_215 h hcq0 hcq3 hcq1 hcq5)
  have hz0theta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_216 h hcq0 hcq3 hcq1 hcq5 hGn)
    · exact Or.inr (by exact astra4wPowerNat112_217 h hcq5)
    · exact Or.inr (by exact astra4wPowerNat112_218 hcq0 hcq3 h hBn hcq1 hcq5)
    · exact Or.inr (by exact astra4wPowerNat112_219 h hcq0 hcq3 hBn hcq1 hcq5)
    · exact Or.inr (by exact astra4wPowerNat112_220 h hcq3 hBn hcq5)
    · exact Or.inr (by exact astra4wPowerNat112_221 h hcq0 hcq3 hBn hcq1 hcq5)
    · exact Or.inr (by exact astra4wPowerNat112_222 h hcq0 hcq3 hcq1 hcq5)
    · exact Or.inr (by exact astra4wPowerNat112_223 h hcq0 hcq4 hcq3 hBn)
    · exact Or.inr (by exact astra4wPowerNat112_224 h hcq0 hcq3 hBn hcq1 hcq5)
    · exact Or.inr (by exact astra4wPowerNat112_225 h hcq0 hcq3 hcq1 hcq5)
    · exact Or.inr (by exact astra4wPowerNat112_226 h hcq0 hcq4 hcq3 hBn)
    · exact Or.inr (by exact astra4wPowerNat112_227 h hcq0 hcq3 hcq1 hcq5)
    · exact Or.inr (by exact astra4wPowerNat112_228 h hAB hcq0 hcq4 hcq3 hBn)
    · exact Or.inr (by exact astra4wPowerNat112_229 h hcq0 hcq3 hcq1 hcq5)
  have hr0 : (kappaQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest14810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hBz hGz hz0l hz0beta (Or.inr (by exact astra4wPowerNat112_167 hdp0 hcq0 hcq3 hcq1 hcq5)) hz0delta (Or.inr (by exact astra4wPowerNat112_168 hdp0 hcq0 hcq3 hcq1 hcq5)) hz0zeta hz0theta
  have hct0 := kappaQuarticChamberFace14810_coeff_top_S15 hCne hDne hEne hFne (A := A) (B := B) (G := G) (by exact hcq1.symm)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (C.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat112_230 hcq0 hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_231 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_232 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_233 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_234 h hcq0 hcq3 hcq1 hcq5)
      · exact absurd h (by exact astra4wPowerNat112_235 hcq0 hcq3 hcq1 hcq5 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_236 hcq0 h hcq3 hcq1 hcq5)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat112_237 hcq0 hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_238 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_239 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_240 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_241 h hcq0 hcq3 hcq1 hcq5)
      · exact absurd h (by exact astra4wPowerNat112_242 hcq0 hcq3 hcq1 hcq5 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_243 h hcq0 hcq3 hcq1 hcq5)
  have hz1delta : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat112_244 hcq0 hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_245 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_246 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_247 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_248 hcq0 h hcq3 hcq1 hcq5)
      · exact absurd h (by exact astra4wPowerNat112_249 hcq0 hcq3 hcq1 hcq5 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_250 h hcq1 hcq5)
  have hr1 : (muQuarticChamberRest18810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest18810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hBz hGz (by exact astra4wPowerNat112_012 hcq1 hcq5) hz1l hz1beta (Or.inr (by exact astra4wPowerNat112_169 hcq0 hcq3 hcq1 hcq5)) hz1delta (Or.inr (by exact astra4wPowerNat112_170 hcq0 hcq3 hcq1 hcq5)) (Or.inr (by exact astra4wPowerNat112_171 hcq0 hcq3 hcq1 hcq5)) (Or.inr (by exact astra4wPowerNat112_172 hcq0 hcq3 hcq1 hcq5))
  have hct1 := muQuarticChamberFace18810_coeff_top_S15 hAne hCne hDne hEne (B := B) (F := F) (G := G) (by exact astra4wPowerNat112_018 hcq0 hcq3) (by exact astra4wPowerNat112_019 hcq0 hcq1)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face18_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_251 hcq0 hcq4 h hcq3 hBn hAG)
      · exact Or.inr (by exact astra4wPowerNat112_122 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_123 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_252 hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_253 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_254 hAB hcq0 hcq4 h hcq3 hBn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_255 hcq0 h hcq3 hcq1 hcq5)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_256 hcq0 hcq4 h hcq3 hBn hGn)
      · exact Or.inr (by exact astra4wPowerNat112_129 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_130 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_257 hcq0 hcq4 hcq3 h hBn)
      · exact Or.inr (by exact astra4wPowerNat112_258 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_259 hAB hcq0 hcq4 h hcq3 hBn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_260 hcq0 h hcq3 hcq1 hcq5)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_261 hcq0 hcq4 h hcq3 hBn hGn)
      · exact Or.inr (by exact astra4wPowerNat112_136 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_137 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_262 h hcq0 hcq4 hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_263 hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_264 hcq0 h hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_141 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_265 hAB hcq0 h hcq3 hBn hcq1 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_266 h hcq0 hcq3 hcq1 hcq5)
  have hr2 : (xiQuarticChamberRest20810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest20810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hBz hGz (by exact astra4wPowerNat112_027 hcq0 hcq3 hcq1 hcq5) (by exact astra4wPowerNat112_028 hcq1 hcq5) hz2l hz2beta (Or.inr (by exact astra4wPowerNat112_173 hcq0 hcq3 hcq1 hcq5)) hz2delta (Or.inr (by exact astra4wPowerNat112_174 hcq0 hcq3 hcq1 hcq5)) (Or.inr (by exact astra4wPowerNat112_175 hcq0 hcq3 hcq1 hcq5)) (Or.inr (by exact astra4wPowerNat112_176 hcq0 hcq3 hcq1 hcq5)) (Or.inr (by exact astra4wPowerNat112_177 hcq0 hcq3 hcq1 hcq5))
  have hct2 := xiQuarticChamberFace20810_coeff_top_S15 hAne hCne hDne hEne hFne (B := B) (G := G) (by exact astra4wPowerNat112_034 hcq0 hcq3 hcq1)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face20_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_267 hcq0 hcq4 h hcq3 hBn hAG)
      · exact Or.inr (by exact astra4wPowerNat112_145 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_146 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_268 hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_269 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_270 hAB hcq0 hcq4 h hcq3 hBn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_271 hcq0 h hcq3 hcq1 hcq5)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_272 hcq0 hcq4 h hcq3 hBn hGn)
      · exact Or.inr (by exact astra4wPowerNat112_152 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_153 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_273 hcq0 hcq4 hcq3 h hBn)
      · exact Or.inr (by exact astra4wPowerNat112_274 hAB hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_275 hAB hcq0 hcq4 h hcq3 hBn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_276 hcq0 h hcq3 hcq1 hcq5)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_277 hcq0 hcq4 h hcq3 hBn hGn)
      · exact Or.inr (by exact astra4wPowerNat112_159 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_160 h hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_278 h hcq0 hcq4 hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_279 hcq0 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat112_280 hcq0 h hcq3 hBn hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_164 hcq0 h hcq3 hcq1 hcq5)
      · exact Or.inr (by exact astra4wPowerNat112_281 hAB hcq0 h hcq3 hBn hcq1 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_282 h hcq0 hcq3 hcq1 hcq5)
  have hr3 : (piQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest12810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hBz hGz (by exact astra4wPowerNat112_046 hcq1 hcq5) (by exact astra4wPowerNat112_047 hcq5) hz3l hz3beta (Or.inr (by exact astra4wPowerNat112_178 hcq0 hcq3 hcq1 hcq5)) hz3delta (Or.inr (by exact astra4wPowerNat112_179 hcq0 hcq3 hcq1 hcq5)) (Or.inr (by exact astra4wPowerNat112_180 hcq0 hcq3 hcq1 hcq5)) (Or.inr (by exact astra4wPowerNat112_181 hcq0 hcq3 hcq1 hcq5)) (Or.inr (by exact astra4wPowerNat112_182 hcq0 hcq3 hcq1 hcq5))
  have hct3 := piQuarticChamberFace12810_coeff_top_S15 hAne hCne hDne hEne hFne (B := B) (G := G) (by exact astra4wPowerNat112_053 hcq0 hcq3) (by exact astra4wPowerNat112_054 hcq0 hcq3) (by exact astra4wPowerNat112_055 hcq0 hcq1)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : piQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS15810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hEc


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
/-- Chamber `BCDEF` / `CF·DD·DE·EE·CCC` dies on power system `S15` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEF33810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF33810 A B C D E F G)
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hGn hcq0 hcq1 hcq3 hcq4 hcq5 hApos hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_056 hcq0 hcq5 h hcq4 hcq3 hGn)
      · exact Or.inr (by exact astra4wPowerNat112_057 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_058 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_059 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_060 h hcq12 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_061 hcq0 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_062 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_063 hcq0 h hcq3 hcq12 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_064 hcq0 h hcq3 hcq12 hcq1 hcq6)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_065 hcq0 hcq5 h hcq4 hcq3 hGn)
      · exact Or.inr (by exact astra4wPowerNat112_066 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_067 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_068 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_069 h hcq12 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_070 hcq0 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_071 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_072 hcq0 h hcq3 hcq12 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_073 hcq0 h hcq3 hcq12 hcq1 hcq6)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_074 hcq0 hcq5 h hcq4 hcq3 hGn)
      · exact Or.inr (by exact astra4wPowerNat112_075 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_076 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_077 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_078 h hcq12 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_079 hcq0 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_080 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_081 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_082 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_083 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_084 hcq0 h hcq3 hcq12 hcq1 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_085 hcq0 h hcq3 hcq12 hcq1 hcq6)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_086 hcq0 hcq5 h hcq4 hcq3 hGn)
      · exact Or.inr (by exact astra4wPowerNat112_087 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_088 h hcq0 hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_089 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_090 h hcq12 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_091 hcq0 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_092 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_093 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_094 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_095 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_096 hcq0 hcq3 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_097 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_098 hcq0 h hcq3 hcq12 hcq1 hcq6)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_099 h hcq0 hcq3 hcq12 hcq1 hcq6)
  have hr0 : (kappaQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest14810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hGz (by exact astra4wPowerNat112_000 hcq3 hcq12) (by exact astra4wPowerNat112_001 hcq0 hcq3 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_002 hcq12) hz0l hz0beta (Or.inr (by exact astra4wPowerNat112_003 hcq0 hcq3 hcq12 hcq1 hcq6)) hz0delta (Or.inr (by exact astra4wPowerNat112_004 hcq0 hcq3 hcq12 hcq1 hcq6)) hz0zeta (Or.inr (by exact astra4wPowerNat112_005 hcq0 hcq3 hcq12 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat112_006 hcq3 hcq12))
  have hct0 := kappaQuarticChamberFace14810_coeff_top_S15 hCne hDne hEne hFne (A := A) (B := B) (G := G) (by exact hcq1.symm)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (C.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_100 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_101 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_102 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_103 h hcq0 hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_104 h hcq0 hcq3 hcq12 hcq1 hcq6)
      · exact absurd h (by exact astra4wPowerNat112_105 hcq0 hcq12 hcq1 hcq6 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_106 hcq0 h hcq3 hcq12 hcq1 hcq6)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_107 hcq0 h hcq3 hcq12)
      · exact Or.inr (by exact astra4wPowerNat112_108 hcq0 h hcq12)
      · exact Or.inr (by exact astra4wPowerNat112_109 hcq0 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_110 hcq0 h hcq12 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_111 h hcq0 hcq12 hcq1 hcq6)
      · exact absurd h (by exact astra4wPowerNat112_112 hcq0 hcq12 hcq1 hcq6 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_113 hcq0 h hcq3 hcq12 hcq1 hcq6)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_114 hcq0 hcq3 h hcq12)
      · exact Or.inr (by exact astra4wPowerNat112_115 hcq0 h hcq12)
      · exact Or.inr (by exact astra4wPowerNat112_116 hcq0 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_117 hcq0 h hcq12 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_118 hcq0 h hcq12 hcq1 hcq6)
      · exact absurd h (by exact astra4wPowerNat112_119 hcq0 hcq12 hcq1 hcq6 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_120 h hcq0 hcq3 hcq12 hcq1 hcq6)
  have hr1 : (muQuarticChamberRest18810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest18810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hGz (by exact astra4wPowerNat112_007 hcq0 hcq3 hcq12) (by exact astra4wPowerNat112_008 hcq3 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_009 hcq0 hcq3 hcq12) (by exact astra4wPowerNat112_010 hcq0 hcq3 hcq12 hcq6) (by exact astra4wPowerNat112_011 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_012 hcq1 hcq6) hz1l hz1beta (Or.inr (by exact astra4wPowerNat112_013 hcq0 hcq3 hcq12 hcq1 hcq6)) hz1delta (Or.inr (by exact astra4wPowerNat112_014 hcq0 hcq3 hcq12 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat112_015 hcq0 hcq3 hcq12 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat112_016 hcq0 hcq3 hcq12 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat112_017 hcq3 hcq12 hcq1 hcq6))
  have hct1 := muQuarticChamberFace18810_coeff_top_S15 hAne hCne hDne hEne (B := B) (F := F) (G := G) (by exact astra4wPowerNat112_018 hcq0 hcq3) (by exact astra4wPowerNat112_019 hcq0 hcq1)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face18_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_121 hcq0 hcq5 h hcq4 hcq3 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat112_122 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_123 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_124 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_125 hcq0 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_126 hcq0 h hcq3 hcq12 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_127 hcq0 h hcq3 hcq12 hcq1 hcq6)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_128 hcq0 hcq5 h hcq4 hcq3 hGn)
      · exact Or.inr (by exact astra4wPowerNat112_129 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_130 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_131 hcq0 hcq3 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_132 hcq0 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_133 hcq0 h hcq3 hcq12 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_134 hcq0 h hcq3 hcq12 hcq1 hcq6)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_135 hcq0 hcq5 h hcq4 hcq3 hGn)
      · exact Or.inr (by exact astra4wPowerNat112_136 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_137 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_138 h hcq0 hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_139 hcq0 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_140 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_141 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_142 hcq0 h hcq3 hcq12 hcq1 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_143 h hcq0 hcq3 hcq12 hcq1 hcq6)
  have hr2 : (xiQuarticChamberRest20810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest20810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hGz (by exact astra4wPowerNat112_020 hcq3 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_021 hcq0 hcq3 hcq12 hcq1) (by exact astra4wPowerNat112_022 hcq12) (by exact astra4wPowerNat112_023 hcq0 hcq3 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_024 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_025 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_026 hcq12 hcq6) (by exact astra4wPowerNat112_027 hcq0 hcq3 hcq1 hcq6) (by exact astra4wPowerNat112_028 hcq1 hcq6) hz2l hz2beta (Or.inr (by exact astra4wPowerNat112_029 hcq0 hcq3 hcq12 hcq1 hcq6)) hz2delta (Or.inr (by exact astra4wPowerNat112_030 hcq0 hcq3 hcq12 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat112_031 hcq0 hcq3 hcq12 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat112_032 hcq0 hcq3 hcq12 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat112_033 hcq0 hcq3 hcq12 hcq1 hcq6))
  have hct2 := xiQuarticChamberFace20810_coeff_top_S15 hAne hCne hDne hEne hFne (B := B) (G := G) (by exact astra4wPowerNat112_034 hcq0 hcq3 hcq1)
  have hq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp2
  rw [degreeZeroXiQuartic810_eq_face20_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : xiQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_144 hcq0 hcq5 h hcq4 hcq3 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat112_145 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_146 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_147 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_148 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_149 h hcq12 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_150 hcq0 h hcq3 hcq12 hcq1 hcq6)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_151 hcq0 hcq5 h hcq4 hcq3 hGn)
      · exact Or.inr (by exact astra4wPowerNat112_152 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_153 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_154 hcq3 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_155 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_156 h hcq12 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_157 hcq0 h hcq3 hcq12 hcq1 hcq6)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat112_158 hcq0 hcq5 h hcq4 hcq3 hGn)
      · exact Or.inr (by exact astra4wPowerNat112_159 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_160 h hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_161 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_162 hcq0 h hcq3 hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_163 h hcq12 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_164 hcq0 h hcq3 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat112_165 hcq0 h hcq3 hcq12 hcq1 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat112_166 h hcq0 hcq3 hcq12 hcq1 hcq6)
  have hr3 : (piQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest12810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hGz (by exact astra4wPowerNat112_035 hcq0 hcq3 hcq12) (by exact astra4wPowerNat112_036 hcq3 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_037 hcq0 hcq3 hcq12) (by exact astra4wPowerNat112_038 hcq3 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_039 hcq0 hcq3 hcq12) (by exact astra4wPowerNat112_040 hcq0 hcq3 hcq12 hcq1) (by exact astra4wPowerNat112_041 hcq3 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_042 hcq0 hcq3 hcq12 hcq6) (by exact astra4wPowerNat112_043 hcq0 hcq3 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_044 hcq12 hcq1 hcq6) (by exact astra4wPowerNat112_045 hcq0 hcq3 hcq12 hcq6) (by exact astra4wPowerNat112_046 hcq1 hcq6) (by exact astra4wPowerNat112_047 hcq6) hz3l hz3beta (Or.inr (by exact astra4wPowerNat112_048 hcq0 hcq3 hcq12 hcq1 hcq6)) hz3delta (Or.inr (by exact astra4wPowerNat112_049 hcq0 hcq3 hcq12 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat112_050 hcq0 hcq3 hcq12 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat112_051 hcq0 hcq3 hcq12 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat112_052 hcq3 hcq12 hcq1 hcq6))
  have hct3 := piQuarticChamberFace12810_coeff_top_S15 hAne hCne hDne hEne hFne (B := B) (G := G) (by exact astra4wPowerNat112_053 hcq0 hcq3) (by exact astra4wPowerNat112_054 hcq0 hcq3) (by exact astra4wPowerNat112_055 hcq0 hcq1)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp3
  rw [degreeZeroPiQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : piQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact quarticPowerInnerS15810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hEc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
