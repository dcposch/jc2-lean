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
private theorem astra4wPowerNat104_000
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_001
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : c + g < a + 2 * d)
    : b + g < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_002
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : b + c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_003
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_004
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_005
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : b + 2 * c = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_006
    {a b d e : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : a + 2 * d = 2 * e)
    : d + e = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_007
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : a + 2 * d = 2 * e)
    : 4 * b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_008
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    : 2 * b + e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_009
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : b + c + d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_010
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : c + g < a + 2 * d)
    : c + g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_011
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) ∧ g < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_012
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : a + 2 * d = 2 * e)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_013
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a + b < (a + 2 * b + c) ∧ d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_014
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_015
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : a + 2 * d = 2 * e)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_016
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    : a + 2 * d = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_017
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : 3 * c = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_018
    {a b c d e : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : a + 2 * d = 2 * e)
    : 2 * e = a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_019
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : a + 2 * d = 2 * e)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_020
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_021
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_022
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : a + 2 * d = 2 * e)
    (h3 : c + g < a + 2 * d)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_023
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : b + d + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_024
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_025
    {a b c d e g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : c + g < a + 2 * d)
    : e + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_026
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_027
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_028
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_029
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_030
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_031
    {a b c d e : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : a + b + c + d = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_032
    {a b c d e : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : 2 * c + e = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_033
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : a + 3 * b + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_034
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 4 * b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_035
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : c + g < a + 2 * d)
    : a + 2 * b + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_036
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    : 2 * b + c + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_037
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : 2 * b + 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_038
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : b + 2 * c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_039
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : b + d + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_040
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    (h2 : c + g < a + 2 * d)
    : 2 * c + g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_041
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    : 2 * d + e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_042
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : c + g < a + 2 * d)
    : 2 * g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_043
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_044
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_045
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_046
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) ∧ g < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_047
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : b + c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_048
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : a + 2 * b + 2 * c = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_049
    {a b d e : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : a + 2 * d = 2 * e)
    : a + b + d + e = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_050
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : a + c + 2 * d = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_051
    {a b c d : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    : 4 * c = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_052
    {a b c d e : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    : c + 2 * e = 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_053
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
private theorem astra4wPowerNat104_054
    {a b d e f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 6 * a ≤ e + f)
    (h4 : a + 2 * d = 2 * e)
    (h5 : f = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_055
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * d = 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_056
    {a b d e f g : ℕ}
    (h0 : 4 * b < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 6 * a ≤ 2 * b + f)
    (h3 : a + 2 * d = 2 * e)
    (h4 : e + g < 2 * a + 2 * d)
    (h5 : f = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_057
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 6 * a ≤ b + c + e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_058
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 6 * a ≤ b + 2 * d)
    (h3 : a + 2 * d = 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_059
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 6 * a ≤ 2 * c + d)
    (h4 : a + 2 * d = 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_060
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 6 * a ≤ 3 * b + c)
    (h4 : a + 2 * d = 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_061
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_062
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
private theorem astra4wPowerNat104_063
    {a b d e f g : ℕ}
    (h0 : 4 * b < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : a + 2 * d = 2 * e)
    (h4 : e + g < 2 * a + 2 * d)
    (h5 : f = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_064
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_065
    {a b d e f g : ℕ}
    (h0 : 4 * b < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + f)
    (h3 : a + 2 * d = 2 * e)
    (h4 : e + g < 2 * a + 2 * d)
    (h5 : f = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_066
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + c + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_067
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_068
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ 2 * c + d)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_069
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ 3 * b + c)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_070
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
private theorem astra4wPowerNat104_071
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
private theorem astra4wPowerNat104_072
    {a b d e f g : ℕ}
    (h0 : 4 * a ≤ e + f)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : e + g < 2 * a + 2 * d)
    (h5 : f = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_073
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_074
    {a b d e f g : ℕ}
    (h0 : 4 * a ≤ 2 * b + f)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : e + g < 2 * a + 2 * d)
    (h5 : f = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_075
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + c + e)
    (h3 : 4 * d = a + 6 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_076
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_077
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_078
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 3 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_079
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ b + e)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_080
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ c + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_081
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_082
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a < a + 3 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_083
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
private theorem astra4wPowerNat104_084
    {a b c d e f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ e + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    (h6 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_085
    {a b d e : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_086
    {a b c d f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : c + g < a + 2 * d)
    (h5 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_087
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + c + e)
    (h3 : 4 * d = a + 6 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_088
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_089
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ 2 * c + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_090
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ 3 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_091
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ b + e)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_092
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ c + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_093
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : a ≤ b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_094
    {a b d e f g : ℕ}
    (h0 : 3 * a ≤ f)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : e + g < 2 * a + 2 * d)
    (h5 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_095
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_096
    {a b c d e : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_097
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
private theorem astra4wPowerNat104_098
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : f = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_099
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : a ≤ 2 * b + d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_100
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : f = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_101
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_102
    {a b d e : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_103
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_104
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_105
    {a b d e : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_106
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_107
    {a b d e : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_108
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : f = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_109
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_110
    {a b d e : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_111
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_112
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : 5 * a ≤ c + f)
    (h5 : f = 0)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_113
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ d + e)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_114
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 3 * b)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_115
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_116
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + 2 * c)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_117
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + b < a + 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_118
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + g)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_119
    {a b c d e f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : e + g < 2 * a + 2 * d)
    (h6 : f = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_120
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ d + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_121
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : a + 2 * d = 2 * e)
    (h3 : a ≤ b)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_122
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_123
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_124
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a + b < a + 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_125
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_126
    {a b c d e f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : e + g < 2 * a + 2 * d)
    (h6 : f = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_127
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ d + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_128
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_129
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_130
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_131
    {a b c d e f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : e + g < 2 * a + 2 * d)
    (h6 : f = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_132
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_133
    {a b c d e : ℕ}
    (h0 : 2 * a + b < a + 2 * b + c)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_134
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
private theorem astra4wPowerNat104_135
    {a b c d e f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : 5 * a ≤ c + f)
    (h5 : a + 2 * d = 2 * e)
    (h6 : f = 0)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_136
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ d + e)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_137
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_138
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * d = 2 * e)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_139
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + 2 * c)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_140
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + d < a + 2 * b + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_141
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
private theorem astra4wPowerNat104_142
    {a b c d e f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : e + g < 2 * a + 2 * d)
    (h6 : f = 0)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_143
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ d + e)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_144
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : a ≤ b)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_145
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_146
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_147
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a + d < a + 2 * b + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_148
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
private theorem astra4wPowerNat104_149
    {a b c d e f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : e + g < 2 * a + 2 * d)
    (h6 : f = 0)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_150
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ d + e)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_151
    {a b d e : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_152
    {a b d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_153
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_154
    {a b d e f g : ℕ}
    (h0 : 3 * a ≤ f)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : e + g < 2 * a + 2 * d)
    (h5 : f = 0)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_155
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_156
    {a b c d e : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_157
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_158
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 2 * f < 7 * a)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : 5 * a ≤ c + f)
    (h5 : f = 0)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_159
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ d + e)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_160
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 3 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_161
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_162
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + 2 * c)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_163
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + b + c < 2 * a + 4 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : c + g < a + 2 * d)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_164
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ b + g)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_165
    {a b c d e f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : e + g < 2 * a + 2 * d)
    (h6 : f = 0)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_166
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ d + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_167
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : a ≤ b)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_168
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_169
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_170
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a + b + c < 2 * a + 4 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_171
    {a b c d e g : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ b + g)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : c + g < a + 2 * d)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_172
    {a b c d e f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : e + g < 2 * a + 2 * d)
    (h6 : f = 0)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_173
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ d + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_174
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_175
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_176
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + 2 * c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_177
    {a b c d e f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : e + g < 2 * a + 2 * d)
    (h6 : f = 0)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_178
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 3 * a ≤ b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_179
    {a b c d e : ℕ}
    (h0 : 2 * a + b + c < 2 * a + 4 * b)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 2 * d = 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_180
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    (h2 : b + f < 2 * d)
    : c + f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_181
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_182
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_183
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_184
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : b + f < 2 * d)
    : a + b + f < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_185
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : d + f < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_186
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_187
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 2 * b < (a + 2 * b + c) ∧ e < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_188
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + b < (a + 2 * b + c) ∧ d < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_189
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_190
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : b < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_191
    {a b d e f : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : a + 2 * d = 2 * e)
    (h2 : b + f < 2 * d)
    : a + d + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_192
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_193
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_194
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_195
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_196
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_197
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_198
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_199
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * d = a + 6 * b)
    (h2 : b + f < 2 * d)
    : a + b + c + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_200
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * d = 2 * e)
    (h3 : b + f < 2 * d)
    : 3 * b + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_201
    {a b d f : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : b + f < 2 * d)
    : a + 2 * f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_202
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : b + f < 2 * d)
    : b + e + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_203
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : c + d + f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_204
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + 2 * b + c < (2 * a + 4 * b) ∧ 4 * b < (2 * a + 4 * b) ∧ a + 2 * d < (2 * a + 4 * b) ∧ 2 * b + e < (2 * a + 4 * b) ∧ b + c + d < (2 * a + 4 * b) ∧ 3 * c < (2 * a + 4 * b) ∧ d + f < (2 * a + 4 * b) ∧ 2 * e < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_205
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + b + d < (2 * a + 4 * b) ∧ 2 * b + c < (2 * a + 4 * b) ∧ b + f < (2 * a + 4 * b) ∧ c + e < (2 * a + 4 * b) ∧ 2 * d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_206
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + b + c < (2 * a + 4 * b) ∧ 3 * b < (2 * a + 4 * b) ∧ a + f < (2 * a + 4 * b) ∧ b + e < (2 * a + 4 * b) ∧ c + d < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_207
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_208
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : b + c < (2 * a + 4 * b) ∧ f < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_209
    {a b d f g : ℕ}
    (h0 : 4 * b < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : f < a + d)
    (h4 : g = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_210
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 6 * a ≤ e + f)
    (h3 : b + f < 2 * d)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_211
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 6 * a ≤ 2 * b + f)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_212
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_213
    {a b d f g : ℕ}
    (h0 : 4 * b < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : f < a + d)
    (h4 : g = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_214
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : b + f < 2 * d)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_215
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + f)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_216
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a < a + 3 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_217
    {a b d f g : ℕ}
    (h0 : 4 * a ≤ d + g)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : f < a + d)
    (h4 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_218
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ e + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : b + f < 2 * d)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_219
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_220
    {a b d f g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : f < a + d)
    (h4 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_221
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ e + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : b + f < 2 * d)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_222
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_223
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_224
    {a b d e g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : g = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_225
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : b + f < 2 * d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_226
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_227
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b + e < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_228
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + g)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_229
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ c + f)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 4 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_230
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + b < a + 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_231
    {a b c d f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * a ≤ b + g)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f < a + d)
    (h5 : g = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_232
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 4 * a ≤ c + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_233
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
private theorem astra4wPowerNat104_234
    {a b c d f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ b + g)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f < a + d)
    (h5 : g = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_235
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ c + f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_236
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
private theorem astra4wPowerNat104_237
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
private theorem astra4wPowerNat104_238
    {a b d e g : ℕ}
    (h0 : 4 * b < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ b + g)
    (h3 : a + 2 * d = 2 * e)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_239
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
private theorem astra4wPowerNat104_240
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + d < a + 2 * b + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_241
    {a b d e f g : ℕ}
    (h0 : 4 * a ≤ b + g)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : f < a + d)
    (h5 : g = 0)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_242
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
private theorem astra4wPowerNat104_243
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
private theorem astra4wPowerNat104_244
    {a b d e f g : ℕ}
    (h0 : 3 * a ≤ b + g)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : f < a + d)
    (h5 : g = 0)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_245
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
private theorem astra4wPowerNat104_246
    {a b d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : b + f < 2 * d)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_247
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
private theorem astra4wPowerNat104_248
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ b + g)
    (h4 : g < 4 * a)
    (h5 : g = 0)
    : 4 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_249
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
private theorem astra4wPowerNat104_250
    {a b c d e f : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + b + c < 2 * a + 4 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : b + f < 2 * d)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_251
    {a b c d f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * a ≤ b + g)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f < a + d)
    (h5 : g = 0)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_252
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
private theorem astra4wPowerNat104_253
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
private theorem astra4wPowerNat104_254
    {a b c d f g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ b + g)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f < a + d)
    (h5 : g = 0)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_255
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
private theorem astra4wPowerNat104_256
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
private theorem astra4wPowerNat104_257
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
private theorem astra4wPowerNat104_258
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a + 2 * b < (a + 2 * b + c) ∧ b + d < (a + 2 * b + c) ∧ 2 * c < (a + 2 * b + c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_259
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_260
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    : a + 2 * b < (2 * a + 4 * b) ∧ b + d < (2 * a + 4 * b) ∧ 2 * c < (2 * a + 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_261
    {a b d g : ℕ}
    (h0 : 4 * b < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : g < 4 * a)
    (h4 : g = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_262
    {a b d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 6 * a ≤ 2 * b + f)
    (h4 : f = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_263
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : a + 2 * d = 2 * e)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_264
    {a b d g : ℕ}
    (h0 : 4 * b < a + 2 * d)
    (h1 : 4 * d = a + 6 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : g < 4 * a)
    (h4 : g = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_265
    {a b d e f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ e + f)
    (h4 : a + 2 * d = 2 * e)
    (h5 : f = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_266
    {a b d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : 5 * a ≤ 2 * b + f)
    (h4 : f = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_267
    {a b d g : ℕ}
    (h0 : 4 * a ≤ d + g)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : g = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_268
    {a b d e f : ℕ}
    (h0 : 4 * a ≤ e + f)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : f = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_269
    {a b d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_270
    {a b d g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : g = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_271
    {a b d e f : ℕ}
    (h0 : 3 * a ≤ e + f)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_272
    {a b d f : ℕ}
    (h0 : 3 * a ≤ 2 * b + f)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_273
    {a b d f : ℕ}
    (h0 : 3 * a ≤ f)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : f = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_274
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + b < a + 2 * b + c)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_275
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * a ≤ b + g)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : g = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_276
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f = 0)
    : 3 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_277
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ b + g)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : g = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_278
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_279
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f = 0)
    : 2 * a + b < a + 2 * b + c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_280
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + d < a + 2 * b + e)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_281
    {a b d e g : ℕ}
    (h0 : 4 * a ≤ b + g)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : g = 0)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_282
    {a b c d e f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : f = 0)
    : 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_283
    {a b d e g : ℕ}
    (h0 : 3 * a ≤ b + g)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : g = 0)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_284
    {a b c d e f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    (h5 : f = 0)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_285
    {a b d e f : ℕ}
    (h0 : 3 * a ≤ f)
    (h1 : 4 * b < a + 2 * d)
    (h2 : 4 * d = a + 6 * b)
    (h3 : a + 2 * d = 2 * e)
    (h4 : f = 0)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_286
    {a b c d e : ℕ}
    (h0 : 2 * b + e < a + 2 * d)
    (h1 : 2 * d = 2 * b + c)
    (h2 : 4 * a + b + c < 2 * a + 4 * b)
    (h3 : 4 * d = a + 6 * b)
    (h4 : a + 2 * d = 2 * e)
    : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_287
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * a ≤ b + g)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : g = 0)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_288
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 4 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f = 0)
    : 3 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_289
    {a b c d g : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ b + g)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : g = 0)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_290
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ c + f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f = 0)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat104_291
    {a b c d f : ℕ}
    (h0 : 2 * d = 2 * b + c)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * b < a + 2 * d)
    (h3 : 4 * d = a + 6 * b)
    (h4 : f = 0)
    : 2 * a + b + c < 2 * a + 4 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDE` / `DD·DE·EE·BBB·BBC·BCC·CCC` dies on power system `S06` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDE9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE9810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_261 hcq6 hcq2 h hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat104_054 hAF hcq6 hcq2 h hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_055 hcq7 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_262 hAF hcq6 hcq2 h hFn)
      · exact Or.inr (by exact astra4wPowerNat104_057 hcq7 hcq3 hcq2 h)
      · exact Or.inr (by exact astra4wPowerNat104_058 hcq7 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_059 hcq7 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_060 hcq7 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_263 hcq7 hcq3 hcq2 h hcq0)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_264 hcq6 hcq2 h hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat104_265 hAF hcq6 hcq2 h hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_064 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_266 hAF hcq6 hcq2 h hFn)
      · exact Or.inr (by exact astra4wPowerNat104_066 hcq7 hcq3 hcq2 h)
      · exact Or.inr (by exact astra4wPowerNat104_067 hcq7 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_068 hcq7 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_069 hcq7 hcq3 hcq2 h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_216 hcq7 hcq3 h hcq2 hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_267 h hcq6 hcq2 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_268 h hcq6 hcq2 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_073 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_269 hAF h hcq6 hcq2 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_075 hcq7 hcq3 h hcq2)
      · exact Or.inr (by exact astra4wPowerNat104_076 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_077 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_078 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_079 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_080 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_081 hcq7 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_082 hcq7 hcq3 h hcq2 hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_270 h hcq6 hcq2 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_271 h hcq6 hcq2 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_085 h hcq7 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_272 h hcq6 hcq2 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_087 hcq7 hcq3 h hcq2)
      · exact Or.inr (by exact astra4wPowerNat104_088 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_089 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_090 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_091 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_092 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_093 hcq7 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_273 h hcq6 hcq2 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_095 hcq7 hcq3 h hcq2 hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_096 h hcq7 hcq3 hcq2 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_224 h hcq7 hcq2 hcq0 hGn)
    · exact Or.inr (by exact astra4wPowerNat104_098 h hcq7 hcq2 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat104_099 hcq7 hcq2 hcq0 h)
    · exact Or.inr (by exact astra4wPowerNat104_100 h hcq7 hcq2 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat104_101 h hcq7 hcq3 hcq2)
    · exact Or.inr (by exact astra4wPowerNat104_102 h hcq7 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_103 h hcq7 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_104 h hcq7 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_105 h hcq7 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_106 h hcq7 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_107 h hcq7 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_108 h hcq7 hcq2 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat104_109 h hcq7 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_110 h hcq7 hcq2 hcq0)
  have hr0 : (kappaQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest8810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz hGz (by exact astra4wPowerNat104_000 hcq7 hcq2 hcq0) hz0l hz0beta (Or.inr (by exact astra4wPowerNat104_002 hcq7 hcq3 hcq2 hcq0)) hz0delta (Or.inr (by exact astra4wPowerNat104_003 hcq7 hcq2 hcq0)) hz0zeta (Or.inr (by exact astra4wPowerNat104_004 hcq7 hcq2 hcq0)) hz0theta
  have hct0 := kappaQuarticChamberFace8810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_005 hcq3 hcq2) (by exact astra4wPowerNat104_006 hcq2 hcq0)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_228 hcq3 hcq6 hcq2 h hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat104_112 hcq3 hAF hcq6 hcq2 h hFn)
      · exact Or.inr (by exact astra4wPowerNat104_113 hcq7 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_114 hcq7 hcq3 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_115 hcq7 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_116 hcq7 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_274 hcq7 hcq3 h hcq2 hcq0)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_275 hcq3 h hcq6 hcq2 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_276 hcq3 h hcq6 hcq2 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_120 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_121 hcq7 hcq3 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_122 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_123 hcq7 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_124 hcq7 hcq3 h hcq2 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_277 hcq3 h hcq6 hcq2 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_278 hcq3 h hcq6 hcq2 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_127 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_128 h hcq7 hcq3 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_129 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_130 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_279 hcq3 h hcq6 hcq2 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_132 hcq7 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_133 h hcq7 hcq3 hcq2 hcq0)
  have hr1 : (muQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest13810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz hGz (by exact astra4wPowerNat104_007 hcq7 hcq3 hcq0) (by exact astra4wPowerNat104_008 hcq7 hcq3) (by exact astra4wPowerNat104_009 hcq7 hcq2 hcq0) hz1l hz1beta (Or.inr (by exact astra4wPowerNat104_258 hcq7 hcq3 hcq2 hcq0)) hz1delta (Or.inr (by exact astra4wPowerNat104_012 hcq7 hcq3 hcq0)) (Or.inr (by exact astra4wPowerNat104_013 hcq7 hcq3 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_014 hcq7 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_015 hcq7 hcq3 hcq0))
  have hct1 := muQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_016 hcq3) (by exact astra4wPowerNat104_017 hcq3 hcq2) (by exact astra4wPowerNat104_018 hcq3 hcq0)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_238 hcq6 hcq2 h hcq0 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat104_135 hcq3 hAF hcq6 hcq2 h hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_136 hcq7 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_137 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_138 hcq7 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_139 hcq7 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_280 hcq7 hcq3 h hcq2 hcq0)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_281 h hcq6 hcq2 hcq0 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_282 hcq3 h hcq6 hcq2 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_143 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_144 hcq7 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_145 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_146 hcq7 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_147 hcq7 hcq3 h hcq2 hcq0)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_283 h hcq6 hcq2 hcq0 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_284 hcq3 h hcq6 hcq2 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_150 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_151 h hcq7 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_152 hcq7 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_153 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_285 h hcq6 hcq2 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_155 hcq7 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_156 h hcq7 hcq3 hcq2 hcq0)
  have hr2 : (xiQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest13810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hFz hGz (by exact astra4wPowerNat104_019 hcq7 hcq0) (by exact astra4wPowerNat104_020 hcq7 hcq2 hcq0) (by exact astra4wPowerNat104_021 hcq7 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_023 hcq7 hcq2 hcq0) (by exact astra4wPowerNat104_024 hcq7 hcq3 hcq2 hcq0) hz2l hz2beta (Or.inr (by exact astra4wPowerNat104_026 hcq7 hcq3 hcq2 hcq0)) hz2delta (Or.inr (by exact astra4wPowerNat104_259 hcq7 hcq3 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_028 hcq7 hcq3 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_029 hcq7 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_030 hcq7 hcq2 hcq0))
  have hct2 := xiQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_031 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_032 hcq3 hcq2)
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_248 hcq3 hcq6 hcq2 h hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat104_158 hcq3 hAF hcq6 hcq2 h hFn)
      · exact Or.inr (by exact astra4wPowerNat104_159 hcq7 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_160 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_161 hcq7 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_162 hcq7 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_286 hcq7 hcq3 h hcq2 hcq0)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_287 hcq3 h hcq6 hcq2 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_288 hcq3 h hcq6 hcq2 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_166 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_167 hcq7 hcq3 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_168 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_169 hcq7 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_170 hcq7 hcq3 h hcq2 hcq0)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_289 hcq3 h hcq6 hcq2 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_290 hcq3 h hcq6 hcq2 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_173 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_174 h hcq7 hcq3 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_175 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_176 hcq7 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_291 hcq3 h hcq6 hcq2 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_178 hcq7 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_179 h hcq7 hcq3 hcq2 hcq0)
  have hr3 : (piQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hFz hGz (by exact astra4wPowerNat104_033 hcq7 hcq2 hcq0) (by exact astra4wPowerNat104_034 hcq7 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_036 hcq7 hcq3 hcq2) (by exact astra4wPowerNat104_037 hcq7 hcq2 hcq0) (by exact astra4wPowerNat104_038 hcq7 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_041 hcq7 hcq2) hz3l hz3beta (Or.inr (by exact astra4wPowerNat104_043 hcq7 hcq3 hcq2 hcq0)) hz3delta (Or.inr (by exact astra4wPowerNat104_044 hcq7 hcq3 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_045 hcq7 hcq3 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_260 hcq7 hcq3 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_047 hcq7 hcq3 hcq2 hcq0))
  have hct3 := piQuarticChamberFace6810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_048 hcq3 hcq2) (by exact astra4wPowerNat104_049 hcq2 hcq0) (by exact astra4wPowerNat104_050 hcq3 hcq2) (by exact astra4wPowerNat104_051 hcq3 hcq2) (by exact astra4wPowerNat104_052 hcq3 hcq2 hcq0)
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
/-- Chamber `BCDEF` / `DD·DE·EE·BBB·BBC·BCC·CCC` dies on power system `S06` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEF46810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF46810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat104_209 hcq11 hcq2 h hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_210 hcq12 hcq2 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_055 hcq12 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_211 hcq12 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_057 hcq12 hcq3 hcq2 h)
      · exact Or.inr (by exact astra4wPowerNat104_058 hcq12 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_059 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_060 hcq12 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_212 hcq12 hcq3 hcq2 h hcq0 hcq6)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_213 hcq11 hcq2 h hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_214 hcq12 hcq2 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_064 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_215 hcq12 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_066 hcq12 hcq3 hcq2 h)
      · exact Or.inr (by exact astra4wPowerNat104_067 hcq12 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_068 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_069 hcq12 hcq3 hcq2 h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_216 hcq12 hcq3 h hcq2 hcq0)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_217 h hcq11 hcq2 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_218 hcq12 h hcq2 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_073 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_219 hcq12 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_075 hcq12 hcq3 h hcq2)
      · exact Or.inr (by exact astra4wPowerNat104_076 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_077 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_078 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_079 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_080 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_081 hcq12 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_082 hcq12 hcq3 h hcq2 hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_220 h hcq11 hcq2 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_221 hcq12 h hcq2 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_085 h hcq12 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_222 hcq12 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_087 hcq12 hcq3 h hcq2)
      · exact Or.inr (by exact astra4wPowerNat104_088 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_089 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_090 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_091 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_092 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_093 hcq12 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_223 hcq12 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_095 hcq12 hcq3 h hcq2 hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_096 h hcq12 hcq3 hcq2 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_224 h hcq12 hcq2 hcq0 hGn)
    · exact Or.inr (by exact astra4wPowerNat104_225 h hcq12 hcq2 hcq6)
    · exact Or.inr (by exact astra4wPowerNat104_099 hcq12 hcq2 hcq0 h)
    · exact Or.inr (by exact astra4wPowerNat104_226 h hcq12 hcq2 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat104_101 h hcq12 hcq3 hcq2)
    · exact Or.inr (by exact astra4wPowerNat104_102 h hcq12 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_103 h hcq12 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_104 h hcq12 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_105 h hcq12 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_106 h hcq12 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_107 h hcq12 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_227 h hcq12 hcq2 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat104_109 h hcq12 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_110 h hcq12 hcq2 hcq0)
  have hr0 : (kappaQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest8810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hGz (by exact astra4wPowerNat104_000 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_180 hcq3 hcq2 hcq6) hz0l hz0beta (Or.inr (by exact astra4wPowerNat104_181 hcq12 hcq3 hcq2 hcq0 hcq6)) hz0delta (Or.inr (by exact astra4wPowerNat104_182 hcq12 hcq2 hcq0 hcq6)) hz0zeta (Or.inr (by exact astra4wPowerNat104_183 hcq12 hcq2 hcq0 hcq6)) hz0theta
  have hct0 := kappaQuarticChamberFace8810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_005 hcq3 hcq2) (by exact astra4wPowerNat104_006 hcq2 hcq0)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_228 hcq3 hcq11 hcq2 h hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat104_229 hcq12 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_113 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_114 hcq12 hcq3 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_115 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_116 hcq12 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_230 hcq12 hcq3 h hcq2 hcq0 hcq6)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_231 hcq3 h hcq11 hcq2 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_232 hcq12 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_120 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_121 hcq12 hcq3 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_122 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_123 hcq12 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_233 hcq12 hcq3 h hcq2 hcq0 hcq6)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ F.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_234 hcq3 h hcq11 hcq2 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_235 hcq12 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_127 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_128 h hcq12 hcq3 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_129 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_130 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_236 hcq12 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_132 hcq12 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_237 h hcq12 hcq3 hcq2 hcq0 hcq6)
  have hr1 : (muQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest13810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hGz (by exact astra4wPowerNat104_007 hcq12 hcq3 hcq0) (by exact astra4wPowerNat104_184 hcq3 hcq6) (by exact astra4wPowerNat104_008 hcq12 hcq3) (by exact astra4wPowerNat104_009 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_185 hcq12 hcq3 hcq2 hcq0 hcq6) hz1l hz1beta (Or.inr (by exact astra4wPowerNat104_186 hcq12 hcq3 hcq2 hcq0 hcq6)) hz1delta (Or.inr (by exact astra4wPowerNat104_187 hcq12 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat104_188 hcq12 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat104_189 hcq12 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat104_190 hcq12 hcq3 hcq2 hcq0 hcq6))
  have hct1 := muQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_016 hcq3) (by exact astra4wPowerNat104_017 hcq3 hcq2) (by exact astra4wPowerNat104_018 hcq3 hcq0)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_238 hcq11 hcq2 h hcq0 hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat104_239 hcq12 hcq3 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_136 hcq12 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_137 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_138 hcq12 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_139 hcq12 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_240 hcq12 hcq3 h hcq2 hcq0 hcq6)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_241 h hcq11 hcq2 hcq0 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_242 hcq12 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_143 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_144 hcq12 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_145 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_146 hcq12 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_243 hcq12 hcq3 h hcq2 hcq0 hcq6)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_244 h hcq11 hcq2 hcq0 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_245 hcq12 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_150 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_151 h hcq12 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_152 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_153 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_246 hcq12 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_155 hcq12 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_247 h hcq12 hcq3 hcq2 hcq0 hcq6)
  have hr2 : (xiQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest13810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hGz (by exact astra4wPowerNat104_019 hcq12 hcq0) (by exact astra4wPowerNat104_020 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_021 hcq12 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_191 hcq2 hcq0 hcq6) (by exact astra4wPowerNat104_192 hcq12 hcq3 hcq2 hcq0 hcq6) (by exact astra4wPowerNat104_023 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_024 hcq12 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_193 hcq12 hcq2 hcq0 hcq6) hz2l hz2beta (Or.inr (by exact astra4wPowerNat104_194 hcq12 hcq3 hcq2 hcq0 hcq6)) hz2delta (Or.inr (by exact astra4wPowerNat104_195 hcq12 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat104_196 hcq12 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat104_197 hcq12 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat104_198 hcq12 hcq2 hcq0 hcq6))
  have hct2 := xiQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_031 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_032 hcq3 hcq2)
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_248 hcq3 hcq11 hcq2 h hAG hGn)
      · exact Or.inr (by exact astra4wPowerNat104_249 hcq12 hcq3 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_159 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_160 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_161 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_162 hcq12 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_250 hcq12 hcq3 h hcq2 hcq0 hcq6)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ E.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_251 hcq3 h hcq11 hcq2 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_252 hcq12 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_166 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_167 hcq12 hcq3 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_168 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_169 hcq12 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_253 hcq12 hcq3 h hcq2 hcq0 hcq6)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_254 hcq3 h hcq11 hcq2 hcq8 hGn)
      · exact Or.inr (by exact astra4wPowerNat104_255 hcq12 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_173 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_174 h hcq12 hcq3 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_175 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_176 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_256 hcq12 hcq3 h hcq2 hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat104_178 hcq12 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_257 h hcq12 hcq3 hcq2 hcq0 hcq6)
  have hr3 : (piQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hGz (by exact astra4wPowerNat104_033 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_034 hcq12 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_199 hcq3 hcq2 hcq6) (by exact astra4wPowerNat104_200 hcq12 hcq2 hcq0 hcq6) (by exact astra4wPowerNat104_036 hcq12 hcq3 hcq2) (by exact astra4wPowerNat104_037 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_038 hcq12 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_201 hcq2 hcq6) (by exact astra4wPowerNat104_202 hcq12 hcq2 hcq6) (by exact astra4wPowerNat104_203 hcq12 hcq3 hcq2 hcq0 hcq6) (by exact astra4wPowerNat104_041 hcq12 hcq2) hz3l hz3beta (Or.inr (by exact astra4wPowerNat104_204 hcq12 hcq3 hcq2 hcq0 hcq6)) hz3delta (Or.inr (by exact astra4wPowerNat104_205 hcq12 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat104_206 hcq12 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat104_207 hcq12 hcq3 hcq2 hcq0 hcq6)) (Or.inr (by exact astra4wPowerNat104_208 hcq12 hcq3 hcq2 hcq0 hcq6))
  have hct3 := piQuarticChamberFace6810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_048 hcq3 hcq2) (by exact astra4wPowerNat104_049 hcq2 hcq0) (by exact astra4wPowerNat104_050 hcq3 hcq2) (by exact astra4wPowerNat104_051 hcq3 hcq2) (by exact astra4wPowerNat104_052 hcq3 hcq2 hcq0)
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
/-- Chamber `BCDEG` / `DD·DE·EE·BBB·BBC·BCC·CCC` dies on power system `S06` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEG46810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG46810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat104_053 hcq12 hcq3 hcq2 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_054 hAF hcq11 hcq2 h hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_055 hcq12 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_056 hcq11 hcq2 h hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_057 hcq12 hcq3 hcq2 h)
      · exact Or.inr (by exact astra4wPowerNat104_058 hcq12 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_059 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_060 hcq12 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_061 hcq12 hcq3 hcq2 h hcq0 hcq7)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_062 hcq12 hcq3 hcq2 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_063 hcq11 hcq2 h hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_064 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_065 hcq11 hcq2 h hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_066 hcq12 hcq3 hcq2 h)
      · exact Or.inr (by exact astra4wPowerNat104_067 hcq12 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_068 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_069 hcq12 hcq3 hcq2 h hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_070 hcq12 hcq3 h hcq2 hcq0 hcq7)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_071 hcq12 hcq3 h hcq2 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_072 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_073 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_074 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_075 hcq12 hcq3 h hcq2)
      · exact Or.inr (by exact astra4wPowerNat104_076 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_077 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_078 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_079 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_080 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_081 hcq12 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_082 hcq12 hcq3 h hcq2 hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_083 hcq12 hcq3 h hcq2 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_084 hcq3 h hcq11 hcq2 hcq0 hcq7 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_085 h hcq12 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_086 hcq3 h hcq11 hcq2 hcq7 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_087 hcq12 hcq3 h hcq2)
      · exact Or.inr (by exact astra4wPowerNat104_088 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_089 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_090 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_091 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_092 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_093 hcq12 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_094 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_095 hcq12 hcq3 h hcq2 hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_096 h hcq12 hcq3 hcq2 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_097 h hcq12 hcq3 hcq2 hcq0 hcq7)
    · exact Or.inr (by exact astra4wPowerNat104_098 h hcq12 hcq2 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat104_099 hcq12 hcq2 hcq0 h)
    · exact Or.inr (by exact astra4wPowerNat104_100 h hcq12 hcq2 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat104_101 h hcq12 hcq3 hcq2)
    · exact Or.inr (by exact astra4wPowerNat104_102 h hcq12 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_103 h hcq12 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_104 h hcq12 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_105 h hcq12 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_106 h hcq12 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_107 h hcq12 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_108 h hcq12 hcq2 hcq0 hFn)
    · exact Or.inr (by exact astra4wPowerNat104_109 h hcq12 hcq3 hcq2 hcq0)
    · exact Or.inr (by exact astra4wPowerNat104_110 h hcq12 hcq2 hcq0)
  have hr0 : (kappaQuarticChamberRest8810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest8810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by exact astra4wPowerNat104_000 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_001 hcq3 hcq7) hz0l hz0beta (Or.inr (by exact astra4wPowerNat104_002 hcq12 hcq3 hcq2 hcq0)) hz0delta (Or.inr (by exact astra4wPowerNat104_003 hcq12 hcq2 hcq0)) hz0zeta (Or.inr (by exact astra4wPowerNat104_004 hcq12 hcq2 hcq0)) hz0theta
  have hct0 := kappaQuarticChamberFace8810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_005 hcq3 hcq2) (by exact astra4wPowerNat104_006 hcq2 hcq0)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_111 hcq12 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_112 hcq3 hAF hcq11 hcq2 h hFn)
      · exact Or.inr (by exact astra4wPowerNat104_113 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_114 hcq12 hcq3 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_115 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_116 hcq12 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_117 hcq12 hcq3 h hcq2 hcq0 hcq7)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_118 hcq12 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_119 hcq3 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_120 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_121 hcq12 hcq3 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_122 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_123 hcq12 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_124 hcq12 hcq3 h hcq2 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * B.natDegree + C.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_125 hcq12 hcq3 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_126 hcq3 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_127 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_128 h hcq12 hcq3 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_129 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_130 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_131 hcq3 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_132 hcq12 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_133 h hcq12 hcq3 hcq2 hcq0)
  have hr1 : (muQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + C.natDegree :=
    muQuarticChamberRest13810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by exact astra4wPowerNat104_007 hcq12 hcq3 hcq0) (by exact astra4wPowerNat104_008 hcq12 hcq3) (by exact astra4wPowerNat104_009 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_010 hcq3 hcq7) hz1l hz1beta (Or.inr (by exact astra4wPowerNat104_011 hcq12 hcq3 hcq2 hcq0 hcq7)) hz1delta (Or.inr (by exact astra4wPowerNat104_012 hcq12 hcq3 hcq0)) (Or.inr (by exact astra4wPowerNat104_013 hcq12 hcq3 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_014 hcq12 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_015 hcq12 hcq3 hcq0))
  have hct1 := muQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_016 hcq3) (by exact astra4wPowerNat104_017 hcq3 hcq2) (by exact astra4wPowerNat104_018 hcq3 hcq0)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_134 hcq12 hcq3 hcq2 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_135 hcq3 hAF hcq11 hcq2 h hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_136 hcq12 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_137 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_138 hcq12 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_139 hcq12 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_140 hcq12 hcq3 h hcq2 hcq0 hcq7)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_141 hcq12 hcq3 h hcq2 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_142 hcq3 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_143 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_144 hcq12 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_145 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_146 hcq12 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_147 hcq12 hcq3 h hcq2 hcq0)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_148 hcq12 hcq3 h hcq2 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_149 hcq3 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_150 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_151 h hcq12 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_152 hcq12 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_153 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_154 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_155 hcq12 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_156 h hcq12 hcq3 hcq2 hcq0)
  have hr2 : (xiQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest13810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hFz (by exact astra4wPowerNat104_019 hcq12 hcq0) (by exact astra4wPowerNat104_020 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_021 hcq12 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_022 hcq12 hcq3 hcq0 hcq7) (by exact astra4wPowerNat104_023 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_024 hcq12 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_025 hcq3 hcq7) hz2l hz2beta (Or.inr (by exact astra4wPowerNat104_026 hcq12 hcq3 hcq2 hcq0)) hz2delta (Or.inr (by exact astra4wPowerNat104_027 hcq12 hcq3 hcq2 hcq0 hcq7)) (Or.inr (by exact astra4wPowerNat104_028 hcq12 hcq3 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_029 hcq12 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_030 hcq12 hcq2 hcq0))
  have hct2 := xiQuarticChamberFace13810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_031 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_032 hcq3 hcq2)
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_157 hcq12 hcq2 h hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_158 hcq3 hAF hcq11 hcq2 h hFn)
      · exact Or.inr (by exact astra4wPowerNat104_159 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_160 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_161 hcq12 hcq3 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_162 hcq12 hcq3 hcq2 h hcq0)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_163 hcq12 hcq3 h hcq2 hcq0 hcq7)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_164 hcq12 h hcq2 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_165 hcq3 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_166 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_167 hcq12 hcq3 hcq2 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat104_168 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_169 hcq12 hcq3 h hcq2 hcq0)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_170 hcq12 hcq3 h hcq2 hcq0)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ D.natDegree + E.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat104_171 hcq12 h hcq2 hcq0 hcq7)
      · exact Or.inr (by exact astra4wPowerNat104_172 hcq3 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_173 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_174 h hcq12 hcq3 hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_175 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_176 hcq12 hcq3 h hcq2 hcq0)
      · exact Or.inr (by exact astra4wPowerNat104_177 hcq3 h hcq11 hcq2 hcq0 hcq9 hFn)
      · exact Or.inr (by exact astra4wPowerNat104_178 hcq12 hcq3 h hcq2 hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat104_179 h hcq12 hcq3 hcq2 hcq0)
  have hr3 : (piQuarticChamberRest6810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hFz (by exact astra4wPowerNat104_033 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_034 hcq12 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_035 hcq3 hcq7) (by exact astra4wPowerNat104_036 hcq12 hcq3 hcq2) (by exact astra4wPowerNat104_037 hcq12 hcq2 hcq0) (by exact astra4wPowerNat104_038 hcq12 hcq3 hcq2 hcq0) (by exact astra4wPowerNat104_039 hcq12 hcq3 hcq2 hcq0 hcq7) (by exact astra4wPowerNat104_040 hcq3 hcq2 hcq7) (by exact astra4wPowerNat104_041 hcq12 hcq2) (by exact astra4wPowerNat104_042 hcq3 hcq7) hz3l hz3beta (Or.inr (by exact astra4wPowerNat104_043 hcq12 hcq3 hcq2 hcq0)) hz3delta (Or.inr (by exact astra4wPowerNat104_044 hcq12 hcq3 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_045 hcq12 hcq3 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat104_046 hcq12 hcq3 hcq2 hcq0 hcq7)) (Or.inr (by exact astra4wPowerNat104_047 hcq12 hcq3 hcq2 hcq0))
  have hct3 := piQuarticChamberFace6810_coeff_top_S06 hAne hBne hCne hDne hEne (F := F) (G := G) (by exact astra4wPowerNat104_048 hcq3 hcq2) (by exact astra4wPowerNat104_049 hcq2 hcq0) (by exact astra4wPowerNat104_050 hcq3 hcq2) (by exact astra4wPowerNat104_051 hcq3 hcq2) (by exact astra4wPowerNat104_052 hcq3 hcq2 hcq0)
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
