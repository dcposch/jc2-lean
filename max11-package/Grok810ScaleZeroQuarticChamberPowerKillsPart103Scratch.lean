import Grok810ScaleZeroQuarticChamberDefs3Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberDefs2Scratch
import Grok810ScaleZeroQuarticChamberRestsScratch

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
private theorem astra4wPowerNat103_000
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    : a + 2 * b + c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_001
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : a + 2 * d = 3 * c)
    (h2 : b + c < a + d)
    : 4 * b < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_002
    {a b d f : ℕ}
    (h0 : b + f < 2 * d)
    : a + b + f < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_003
    {a b c d e : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * e < a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 2 * b + e < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_004
    {a b c d : ℕ}
    (h0 : b + c < a + d)
    : b + c + d < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_005
    {a c d g : ℕ}
    (h0 : c + g < a + 2 * d)
    : c + g < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_006
    {a d f : ℕ}
    (h0 : f < a + d)
    : d + f < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_007
    {a d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    : 2 * e < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_008
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    : a + 2 * b < (a + 2 * d) ∧ b + d < (a + 2 * d) ∧ 2 * c < (a + 2 * d) ∧ g < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_009
    {a b c d e : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : 2 * e < a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    : 2 * b < (a + 2 * d) ∧ e < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_010
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : a + b < (a + 2 * d) ∧ d < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_011
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    : c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_012
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    : b < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_013
    {a c d : ℕ}
    (h0 : a + 2 * d = 3 * c)
    : 3 * c = a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_014
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : a + 2 * d = 3 * c)
    : 2 * a + 4 * b < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_015
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : a + 2 * d = 3 * c)
    (h2 : b + c < a + d)
    : a + 3 * b + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_016
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    : a + 2 * b + 2 * c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_017
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : a + 2 * d = 3 * c)
    (h2 : b + c < a + d)
    : 4 * b + c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_018
    {a b c d g : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : a + 2 * d = 3 * c)
    (h2 : c + g < a + 2 * d)
    : a + 2 * b + g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_019
    {a b c d f : ℕ}
    (h0 : b + f < 2 * d)
    : a + b + c + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_020
    {a b c d e : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * e < a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    : a + b + d + e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_021
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : a + 2 * d = 3 * c)
    (h2 : b + c < a + d)
    (h3 : f < a + d)
    : 3 * b + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_022
    {a b c d e : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * e < a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 2 * b + c + e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_023
    {a b c d : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : b + c < a + d)
    : 2 * b + 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_024
    {a b c d : ℕ}
    (h0 : b + c < a + d)
    : b + 2 * c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_025
    {a c d f : ℕ}
    (h0 : 2 * c + 2 * f < a + 4 * d)
    (h1 : a + 2 * d = 3 * c)
    : a + 2 * f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_026
    {a b c d g : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : b + c < a + d)
    (h2 : c + g < a + 2 * d)
    : b + d + g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_027
    {a b c d e f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * e < a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : b + e + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_028
    {a c d g : ℕ}
    (h0 : c + g < a + 2 * d)
    : 2 * c + g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_029
    {a c d f : ℕ}
    (h0 : f < a + d)
    : c + d + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_030
    {a c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    : c + 2 * e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_031
    {a c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    : 2 * d + e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_032
    {a c d g : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : c + g < a + 2 * d)
    : 2 * g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_033
    {a b c d e f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : 2 * c + 2 * f < a + 4 * d)
    (h3 : 2 * e < a + 2 * d)
    (h4 : a + 2 * d = 3 * c)
    (h5 : b + c < a + d)
    (h6 : b + f < 2 * d)
    : a + 2 * b + c < (a + c + 2 * d) ∧ 4 * b < (a + c + 2 * d) ∧ a + 2 * d < (a + c + 2 * d) ∧ 2 * b + e < (a + c + 2 * d) ∧ b + c + d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ d + f < (a + c + 2 * d) ∧ 2 * e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_034
    {a b c d e f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : 2 * e < a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + f < 2 * d)
    : a + b + d < (a + c + 2 * d) ∧ 2 * b + c < (a + c + 2 * d) ∧ b + f < (a + c + 2 * d) ∧ c + e < (a + c + 2 * d) ∧ 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_035
    {a b c d e f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : 2 * e < a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : b + f < 2 * d)
    (h6 : f < a + d)
    : a + b + c < (a + c + 2 * d) ∧ 3 * b < (a + c + 2 * d) ∧ a + f < (a + c + 2 * d) ∧ b + e < (a + c + 2 * d) ∧ c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_036
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    : a + 2 * b < (a + c + 2 * d) ∧ b + d < (a + c + 2 * d) ∧ 2 * c < (a + c + 2 * d) ∧ g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_037
    {a b c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + f < 2 * d)
    : b + c < (a + c + 2 * d) ∧ f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_038
    {a c d : ℕ}
    (h0 : a + 2 * d = 3 * c)
    : 4 * c = a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_039
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 5 * a ≤ 4 * b)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_040
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 7 * a ≤ 4 * c)
    (h3 : a + 2 * d = 3 * c)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_041
    {a b c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_042
    {a b c d e : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * e < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_043
    {a b c d f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_044
    {a b c d g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_045
    {a b c d e f g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : c + g < a + 2 * d)
    (h6 : f < a + d)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_046
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 3 * a ≤ 4 * b)
    (h2 : a + 2 * d = 3 * c)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_047
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 5 * a ≤ 4 * c)
    (h2 : a + 2 * d = 3 * c)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_048
    {a b c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_049
    {a b c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 9 * a ≤ 4 * e)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_050
    {a b c d f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_051
    {a b c d g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_052
    {a b c d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + b < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : f < a + d)
    : 3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_053
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a ≤ 4 * b)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_054
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 3 * a ≤ 4 * c)
    (h2 : a + 2 * d = 3 * c)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_055
    {a b c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_056
    {a b c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 7 * a ≤ 4 * e)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_057
    {a b c d f : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 9 * a ≤ 4 * f)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_058
    {a b c d g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_059
    {a b c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b < a + 2 * d)
    (h2 : 2 * b + c < 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : b + f < 2 * d)
    : 2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_060
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 5 * a ≤ 4 * b)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : b + f < 2 * d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_061
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : 7 * a ≤ 4 * c)
    (h4 : a + 2 * d = 3 * c)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_062
    {a b c d f : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_063
    {a b c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * e < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : f < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_064
    {a b c d f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_065
    {a b c d f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    (h5 : f < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_066
    {a b c d e f g : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * e < a + 2 * d)
    (h2 : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d)
    (h3 : 4 * c < 3 * a + 2 * d)
    (h4 : a + 2 * d = 3 * c)
    (h5 : b + c < a + d)
    (h6 : c + g < a + 2 * d)
    (h7 : f < a + d)
    : 4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d ∧ 3 * a + b + e < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * b + f < a + c + 2 * d ∧ a + b + c + e < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 3 * b + e < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ b + c + g < a + c + 2 * d ∧ b + d + f < a + c + 2 * d ∧ b + 2 * e < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d ∧ f + g < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_067
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 3 * a ≤ 4 * b)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + f < 2 * d)
    : 3 * a + b + c < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_068
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : 5 * a ≤ 4 * c)
    (h3 : a + 2 * d = 3 * c)
    : 3 * a + b + c < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_069
    {a b c d f : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 3 * a + b + c < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_070
    {a b c d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 9 * a ≤ 4 * e)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : f < a + d)
    : 3 * a + b + c < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_071
    {a b c d f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 3 * a + b + c < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_072
    {a b c d f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    (h5 : f < a + d)
    : 3 * a + b + c < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_073
    {a b c d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + b + c < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : f < a + d)
    : 3 * a + b + c < a + c + 2 * d ∧ 2 * a + 3 * b < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d ∧ 2 * a + b + e < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + 2 * b + d < a + c + 2 * d ∧ a + b + 2 * c < a + c + 2 * d ∧ 3 * b + c < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ 2 * b + f < a + c + 2 * d ∧ b + c + e < a + c + 2 * d ∧ b + 2 * d < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d ∧ e + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_074
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a ≤ 4 * b)
    (h3 : b + f < 2 * d)
    : 2 * a + b + c < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_075
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : 3 * a ≤ 4 * c)
    (h3 : a + 2 * d = 3 * c)
    : 2 * a + b + c < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_076
    {a b c d f : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 2 * a + b + c < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_077
    {a b c d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 7 * a ≤ 4 * e)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : f < a + d)
    : 2 * a + b + c < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_078
    {a b c d f : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 9 * a ≤ 4 * f)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 2 * a + b + c < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_079
    {a b c d f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    (h5 : f < a + d)
    : 2 * a + b + c < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_080
    {a b c d e f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b + c < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d)
    (h2 : 2 * b + c < 2 * d)
    (h3 : 2 * e < a + 2 * d)
    (h4 : a + 2 * d = 3 * c)
    (h5 : b + c < a + d)
    (h6 : b + f < 2 * d)
    : 2 * a + b + c < a + c + 2 * d ∧ a + 3 * b < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d ∧ a + b + e < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ 2 * b + d < a + c + 2 * d ∧ b + 2 * c < a + c + 2 * d ∧ c + f < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_081
    {a c d f g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    : 2 * c < (a + 2 * d) ∧ g < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_082
    {a c d e f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : 2 * e < a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    : e < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_083
    {a c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : a + 2 * d = 3 * c)
    : d < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_084
    {a c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    : c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_085
    {a c d e f g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : 2 * e < a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : c + g < a + 2 * d)
    : a + 2 * d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ d + f < (a + c + 2 * d) ∧ 2 * e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_086
    {a c d e f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : 2 * e < a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    : c + e < (a + c + 2 * d) ∧ 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_087
    {a c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : a + 2 * d = 3 * c)
    : a + f < (a + c + 2 * d) ∧ c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_088
    {a c d f g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    : 2 * c < (a + c + 2 * d) ∧ g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_089
    {a c d f g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    : f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_090
    {a b : ℕ}
    (h0 : 0 < a)
    (h1 : b = 0)
    : ¬ (5 * a ≤ 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_091
    {a c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 7 * a ≤ 4 * c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_092
    {a c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_093
    {a c d e : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * e < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_094
    {a c d f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_095
    {a c d g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_096
    {a c d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + d < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : f < a + d)
    : 3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_097
    {a b : ℕ}
    (h0 : 0 < a)
    (h1 : b = 0)
    : ¬ (3 * a ≤ 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_098
    {a c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 5 * a ≤ 4 * c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_099
    {a c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_100
    {a c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 9 * a ≤ 4 * e)
    (h3 : a + 2 * d = 3 * c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_101
    {a c d f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_102
    {a c d g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_103
    {a c d f : ℕ}
    (h0 : 2 * a + d < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : 2 * a + d < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_104
    {a b : ℕ}
    (h0 : 0 < a)
    (h1 : b = 0)
    : ¬ (a ≤ 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_105
    {a c d : ℕ}
    (h0 : 0 < a)
    (h1 : 3 * a ≤ 4 * c)
    (h2 : a + 2 * d = 3 * c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_106
    {a c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_107
    {a c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 7 * a ≤ 4 * e)
    (h3 : a + 2 * d = 3 * c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_108
    {a c d f : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 9 * a ≤ 4 * f)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_109
    {a c d g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_110
    {a c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : a + d < a + 2 * d)
    : a + d < a + 2 * d ∧ f < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_111
    {a c d f : ℕ}
    (h0 : 2 * c + 2 * f < a + 4 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 7 * a ≤ 4 * c)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_112
    {a c d f : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_113
    {a c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * e < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : f < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_114
    {a c d f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_115
    {a c d f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    (h4 : f < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_116
    {a c d e f g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : c + g < a + 2 * d)
    (h5 : f < a + d)
    : 4 * a + f < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d ∧ f + g < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_117
    {a c d f : ℕ}
    (h0 : 2 * c + 2 * f < a + 4 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 5 * a ≤ 4 * c)
    : 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_118
    {a c d f : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_119
    {a c d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 9 * a ≤ 4 * e)
    (h3 : a + 2 * d = 3 * c)
    (h4 : f < a + d)
    : 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_120
    {a c d f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_121
    {a c d f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    (h4 : f < a + d)
    : 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_122
    {a c d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    : 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d ∧ e + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_123
    {a c d f : ℕ}
    (h0 : 2 * c + 2 * f < a + 4 * d)
    (h1 : 3 * a ≤ 4 * c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_124
    {a c d f : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_125
    {a c d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 7 * a ≤ 4 * e)
    (h3 : a + 2 * d = 3 * c)
    (h4 : f < a + d)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_126
    {a c d f : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 9 * a ≤ 4 * f)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f < a + d)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_127
    {a c d f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : c + g < a + 2 * d)
    (h4 : f < a + d)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_128
    {a c d e f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + f < a + c + 2 * d)
    (h2 : 2 * c + 2 * f < a + 4 * d)
    (h3 : 2 * e < a + 2 * d)
    (h4 : a + 2 * d = 3 * c)
    : 2 * a + f < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ c + f < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_129
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    : 2 * b < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_130
    {a b c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : 2 * c + 2 * f < a + 4 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : b + f < 2 * d)
    : a + 2 * b + c < (a + c + 2 * d) ∧ 4 * b < (a + c + 2 * d) ∧ a + 2 * d < (a + c + 2 * d) ∧ b + c + d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ d + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_131
    {a b c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + f < 2 * d)
    : a + b + d < (a + c + 2 * d) ∧ 2 * b + c < (a + c + 2 * d) ∧ b + f < (a + c + 2 * d) ∧ 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_132
    {a b c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : b + f < 2 * d)
    (h5 : f < a + d)
    : a + b + c < (a + c + 2 * d) ∧ 3 * b < (a + c + 2 * d) ∧ a + f < (a + c + 2 * d) ∧ c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_133
    {a b c d e : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : e = 0)
    : ¬ (11 * a ≤ 4 * e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_134
    {a b c d f g : ℕ}
    (h0 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    (h5 : f < a + d)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_135
    {a b c d e : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : e = 0)
    : ¬ (9 * a ≤ 4 * e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_136
    {a b c d f : ℕ}
    (h0 : 3 * a + b < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_137
    {a b c d e : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : e = 0)
    : ¬ (7 * a ≤ 4 * e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_138
    {a b c d f g : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : c + g < a + 2 * d)
    (h6 : f < a + d)
    : 4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ a + 2 * b + f < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ b + c + g < a + c + 2 * d ∧ b + d + f < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ 3 * d < a + c + 2 * d ∧ f + g < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_139
    {a b c d f : ℕ}
    (h0 : 3 * a + b + c < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 3 * a + b + c < a + c + 2 * d ∧ 2 * a + 3 * b < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + 2 * b + d < a + c + 2 * d ∧ a + b + 2 * c < a + c + 2 * d ∧ 3 * b + c < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ 2 * b + f < a + c + 2 * d ∧ b + 2 * d < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_140
    {a b c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b + c < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d)
    (h2 : 2 * b + c < 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : b + f < 2 * d)
    : 2 * a + b + c < a + c + 2 * d ∧ a + 3 * b < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ 2 * b + d < a + c + 2 * d ∧ b + 2 * c < a + c + 2 * d ∧ c + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_141
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    : a + 2 * b < (a + 2 * d) ∧ b + d < (a + 2 * d) ∧ 2 * c < (a + 2 * d) ∧ g < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_142
    {a b c d e : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : 2 * e < a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : a + 2 * b + c < (a + c + 2 * d) ∧ 4 * b < (a + c + 2 * d) ∧ a + 2 * d < (a + c + 2 * d) ∧ 2 * b + e < (a + c + 2 * d) ∧ b + c + d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ 2 * e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_143
    {a b c d e : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : 2 * e < a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : a + b + d < (a + c + 2 * d) ∧ 2 * b + c < (a + c + 2 * d) ∧ c + e < (a + c + 2 * d) ∧ 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_144
    {a b c d e : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : 2 * e < a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : a + b + c < (a + c + 2 * d) ∧ 3 * b < (a + c + 2 * d) ∧ b + e < (a + c + 2 * d) ∧ c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_145
    {a b c d g : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    : a + 2 * b < (a + c + 2 * d) ∧ b + d < (a + c + 2 * d) ∧ 2 * c < (a + c + 2 * d) ∧ g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_146
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    : b + c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_147
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 5 * a ≤ 4 * b)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_148
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 7 * a ≤ 4 * c)
    (h3 : a + 2 * d = 3 * c)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_149
    {a b c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_150
    {a b c d e : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * e < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_151
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f = 0)
    : ¬ (13 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_152
    {a b c d g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_153
    {a b c d e g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : c + g < a + 2 * d)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ d + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_154
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f = 0)
    : ¬ (11 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_155
    {a b c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + b < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_156
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : f = 0)
    : ¬ (9 * a ≤ 4 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_157
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b < a + 2 * d)
    (h2 : 2 * b + c < 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_158
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 5 * a ≤ 4 * b)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_159
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 7 * a ≤ 4 * c)
    (h3 : a + 2 * d = 3 * c)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_160
    {a b c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_161
    {a b c d e : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * e < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_162
    {a b c d g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_163
    {a b c d e g : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * e < a + 2 * d)
    (h2 : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d)
    (h3 : 4 * c < 3 * a + 2 * d)
    (h4 : a + 2 * d = 3 * c)
    (h5 : b + c < a + d)
    (h6 : c + g < a + 2 * d)
    : 4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 3 * a + b + e < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + b + c + e < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 3 * b + e < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ b + c + g < a + c + 2 * d ∧ b + 2 * e < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_164
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 3 * a ≤ 4 * b)
    (h2 : a + 2 * d = 3 * c)
    : 3 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_165
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 5 * a ≤ 4 * c)
    (h2 : a + 2 * d = 3 * c)
    : 3 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_166
    {a b c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 3 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_167
    {a b c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 9 * a ≤ 4 * e)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 3 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_168
    {a b c d g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    : 3 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_169
    {a b c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + b + c < a + c + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 3 * a + b + c < a + c + 2 * d ∧ 2 * a + 3 * b < a + c + 2 * d ∧ 2 * a + b + e < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + 2 * b + d < a + c + 2 * d ∧ a + b + 2 * c < a + c + 2 * d ∧ 3 * b + c < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ b + c + e < a + c + 2 * d ∧ b + 2 * d < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_170
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a ≤ 4 * b)
    : 2 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_171
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 3 * a ≤ 4 * c)
    (h2 : a + 2 * d = 3 * c)
    : 2 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_172
    {a b c d : ℕ}
    (h0 : 4 * c < 3 * a + 2 * d)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : 2 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_173
    {a b c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : 7 * a ≤ 4 * e)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 2 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_174
    {a b c d g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : c + g < a + 2 * d)
    : 2 * a + b + c < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_175
    {a b c d e : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * a + b + c < a + c + 2 * d)
    (h2 : 2 * b + c < 2 * d)
    (h3 : 2 * e < a + 2 * d)
    (h4 : a + 2 * d = 3 * c)
    (h5 : b + c < a + d)
    : 2 * a + b + c < a + c + 2 * d ∧ a + 3 * b < a + c + 2 * d ∧ a + b + e < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ 2 * b + d < a + c + 2 * d ∧ b + 2 * c < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_176
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    : a + 2 * b < (a + 2 * d) ∧ b + d < (a + 2 * d) ∧ 2 * c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_177
    {a b c d e f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : 2 * c + 2 * f < a + 4 * d)
    (h3 : 2 * e < a + 2 * d)
    (h4 : a + 2 * d = 3 * c)
    (h5 : b + f < 2 * d)
    : a + 2 * b + c < (a + c + 2 * d) ∧ 4 * b < (a + c + 2 * d) ∧ a + 2 * d < (a + c + 2 * d) ∧ 2 * b + e < (a + c + 2 * d) ∧ b + c + d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ d + f < (a + c + 2 * d) ∧ 2 * e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_178
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    : a + 2 * b < (a + c + 2 * d) ∧ b + d < (a + c + 2 * d) ∧ 2 * c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_179
    {a b c d g : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : g = 0)
    : ¬ (15 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_180
    {a b c d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : f < a + d)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_181
    {a b c d g : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : g = 0)
    : ¬ (13 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_182
    {a b c d g : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : g = 0)
    : ¬ (11 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_183
    {a b c d e f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * e < a + 2 * d)
    (h2 : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d)
    (h3 : 4 * c < 3 * a + 2 * d)
    (h4 : a + 2 * d = 3 * c)
    (h5 : b + c < a + d)
    (h6 : f < a + d)
    : 4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d ∧ 3 * a + b + e < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * b + f < a + c + 2 * d ∧ a + b + c + e < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 3 * b + e < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ b + d + f < a + c + 2 * d ∧ b + 2 * e < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_184
    {a c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : a + 2 * d = 3 * c)
    : 2 * c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_185
    {a c d e f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : 2 * e < a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    : a + 2 * d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ d + f < (a + c + 2 * d) ∧ 2 * e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_186
    {a c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    : 2 * c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_187
    {a c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * c + 2 * f < a + 4 * d)
    (h2 : a + 2 * d = 3 * c)
    : f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_188
    {a g : ℕ}
    (h0 : 0 < a)
    (h1 : g = 0)
    : ¬ (15 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_189
    {a g : ℕ}
    (h0 : 0 < a)
    (h1 : g = 0)
    : ¬ (13 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_190
    {a g : ℕ}
    (h0 : 0 < a)
    (h1 : g = 0)
    : ¬ (11 * a ≤ 4 * g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_191
    {a c d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : f < a + d)
    : 4 * a + f < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_192
    {a b c d f : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : 2 * c + 2 * f < a + 4 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + f < 2 * d)
    : a + 2 * b + c < (a + c + 2 * d) ∧ 4 * b < (a + c + 2 * d) ∧ a + 2 * d < (a + c + 2 * d) ∧ b + c + d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ d + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_193
    {a b c d f : ℕ}
    (h0 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (h1 : 4 * c < 3 * a + 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    (h4 : f < a + d)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ c + f < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_194
    {a b c d f : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    (h5 : f < a + d)
    : 4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ a + 2 * b + f < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ b + d + f < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ 3 * d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_195
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : a + 2 * b < (a + 2 * d) ∧ b + d < (a + 2 * d) ∧ 2 * c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_196
    {a b c d : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : a + 2 * d = 3 * c)
    (h2 : b + c < a + d)
    : c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_197
    {a b c d : ℕ}
    (h0 : 0 < a)
    (h1 : 2 * b + c < 2 * d)
    (h2 : a + 2 * d = 3 * c)
    (h3 : b + c < a + d)
    : a + 2 * b < (a + c + 2 * d) ∧ b + d < (a + c + 2 * d) ∧ 2 * c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_198
    {a b c d e : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (h2 : 4 * c < 3 * a + 2 * d)
    (h3 : a + 2 * d = 3 * c)
    (h4 : b + c < a + d)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ d + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_199
    {a b c d e : ℕ}
    (h0 : 2 * b + c < 2 * d)
    (h1 : 2 * e < a + 2 * d)
    (h2 : 3 * a + c + d < a + c + 2 * d ∧ 4 * a + b + c < a + c + 2 * d)
    (h3 : 4 * c < 3 * a + 2 * d)
    (h4 : a + 2 * d = 3 * c)
    (h5 : b + c < a + d)
    : 4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 3 * a + b + e < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + b + c + e < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 3 * b + e < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ b + 2 * e < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_200
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_201
    {a b c e g : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : c + g < 2 * e)
    : b + g < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_202
    {a b c e f : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    : c + f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_203
    {a b d e : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : a + 2 * d < 2 * e)
    : d + e < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_204
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_205
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + b + f < 2 * e)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_206
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_207
    {a b c e : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : 4 * e = 3 * a + 6 * b)
    : b + 2 * c = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_208
    {a b e : ℕ}
    (h0 : 2 * b < e)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_209
    {a b c d e : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : a + b + c + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_210
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_211
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_212
    {a b d e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + b + f < 2 * e)
    : a + d + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_213
    {a b c e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : c + g < 2 * e)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_214
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_215
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    : b + d + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_216
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_217
    {a b c e g : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : c + g < 2 * e)
    : e + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_218
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_219
    {a b c d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    (h4 : a + b + f < 2 * e)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_220
    {a b c d e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    (h4 : a + b + f < 2 * e)
    (h5 : c + g < 2 * e)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_221
    {a b c d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    (h4 : a + b + f < 2 * e)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_222
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_223
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + b + f < 2 * e)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_224
    {a b c e : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : 4 * e = 3 * a + 6 * b)
    : 2 * c + e = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_225
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
private theorem astra4wPowerNat103_226
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 6 * a ≤ e + f)
    (h3 : a + b + f < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_227
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * d < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_228
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 6 * a ≤ 2 * b + f)
    (h3 : a + b + f < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_229
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ b + c + e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_230
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 6 * a ≤ b + 2 * d)
    (h3 : a + 2 * d < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_231
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ 2 * c + d)
    (h4 : a + 2 * d < 2 * e)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_232
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ 3 * b + c)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_233
    {a b c d e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : a + b + f < 2 * e)
    (h6 : c + g < 2 * e)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_234
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
private theorem astra4wPowerNat103_235
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ e + f)
    (h3 : a + b + f < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_236
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_237
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ 2 * b + f)
    (h3 : a + b + f < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_238
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ b + c + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_239
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : a + 2 * d < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_240
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 2 * c + d)
    (h4 : a + 2 * d < 2 * e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_241
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 3 * b + c)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_242
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
private theorem astra4wPowerNat103_243
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
private theorem astra4wPowerNat103_244
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ e + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_245
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_246
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 2 * b + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_247
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ b + c + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_248
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_249
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_250
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ 3 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_251
    {a b e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ b + e)
    (h2 : 4 * e = 3 * a + 6 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_252
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a ≤ c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_253
    {a b e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : 4 * e = 3 * a + 6 * b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_254
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a < a + 3 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_255
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
private theorem astra4wPowerNat103_256
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ e + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_257
    {a b d e : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_258
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ 2 * b + f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_259
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ b + c + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_260
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_261
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 2 * c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_262
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 3 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_263
    {a b e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ b + e)
    (h2 : 4 * e = 3 * a + 6 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_264
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_265
    {a b e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a ≤ b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_266
    {a b e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ f)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_267
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_268
    {a b c e : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_269
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
private theorem astra4wPowerNat103_270
    {a b e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_271
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a ≤ 2 * b + d)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_272
    {a b e f : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_273
    {a b c e : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_274
    {a b d e : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_275
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_276
    {a b c e : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_277
    {a b e : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_278
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_279
    {a b e : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_280
    {a b e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_281
    {a b c e : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_282
    {a b d e : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_283
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 4 * b)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_284
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 7 * a ≤ 4 * c)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_285
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 9 * a ≤ 4 * d)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_286
    {a b c d e : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_287
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
private theorem astra4wPowerNat103_288
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
private theorem astra4wPowerNat103_289
    {a b c d e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : a + b + f < 2 * e)
    (h6 : c + g < 2 * e)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_290
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 4 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_291
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 4 * c)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_292
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 7 * a ≤ 4 * d)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_293
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 9 * a ≤ 4 * e)
    (h4 : a + 2 * d < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_294
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
private theorem astra4wPowerNat103_295
    {a b c d e g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + 2 * d < 2 * e)
    (h5 : c + g < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_296
    {a b c d e f : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_297
    {a b d e : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a ≤ 4 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_298
    {a b c d e : ℕ}
    (h0 : 2 * e = a + 2 * b + c)
    (h1 : 3 * a ≤ 4 * c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + 2 * d < 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_299
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ 4 * d)
    (h3 : a + 2 * d < 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_300
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 7 * a ≤ 4 * e)
    (h3 : a + 2 * d < 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_301
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 9 * a ≤ 4 * f)
    (h3 : a + 2 * d < 2 * e)
    (h4 : a + b + f < 2 * e)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_302
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
private theorem astra4wPowerNat103_303
    {a b c d e f : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_304
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_305
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : a + b + c < (a + 2 * b + e) ∧ 3 * b < (a + 2 * b + e) ∧ a + f < (a + 2 * b + e) ∧ b + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_306
    {a b c e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : c + g < 2 * e)
    : a + 2 * b < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_307
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    : b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_308
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
private theorem astra4wPowerNat103_309
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 2 * b + d)
    (h4 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_310
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * d < 5 * a)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 6 * a ≤ b + 2 * d)
    (h4 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_311
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
private theorem astra4wPowerNat103_312
    {a b c e f g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a < a + 3 * b)
    (h4 : a + b + f < 2 * e)
    (h5 : c + g < 2 * e)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_313
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
private theorem astra4wPowerNat103_314
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_315
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : d = 0)
    (h4 : g < a + e)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_316
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
private theorem astra4wPowerNat103_317
    {a b c e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * a < a + 3 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_318
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
private theorem astra4wPowerNat103_319
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_320
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    (h4 : g < a + e)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_321
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
private theorem astra4wPowerNat103_322
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
private theorem astra4wPowerNat103_323
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
private theorem astra4wPowerNat103_324
    {a b d e : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_325
    {a b d e g : ℕ}
    (h0 : 2 * b < e)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    (h4 : g < a + e)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_326
    {a b c d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 2 * c + d)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_327
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
private theorem astra4wPowerNat103_328
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
private theorem astra4wPowerNat103_329
    {a b d e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a ≤ 2 * b + d)
    (h3 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_330
    {a b d e f : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : a + b + f < 2 * e)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_331
    {a b c d e : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_332
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
private theorem astra4wPowerNat103_333
    {a b d e g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * b < e)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : d = 0)
    (h4 : g < a + e)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_334
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 4 * b)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_335
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 7 * a ≤ 4 * c)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_336
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    (h3 : d = 0)
    : ¬ (9 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_337
    {a b c e : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_338
    {a b c e f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_339
    {a b c e g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    : 3 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_340
    {a b c e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a + b + c < a + 2 * b + e)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_341
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 3 * a ≤ 4 * b)
    (h3 : 4 * e = 3 * a + 6 * b)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_342
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 5 * a ≤ 4 * c)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_343
    {a b d e f : ℕ}
    (h0 : 2 * b < e)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : a + b + f < 2 * e)
    (h3 : d = 0)
    : ¬ (7 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_344
    {a b c e : ℕ}
    (h0 : 2 * b < e)
    (h1 : 2 * e = a + 2 * b + c)
    (h2 : 4 * e = 3 * a + 6 * b)
    (h3 : 9 * a ≤ 4 * e)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_345
    {a b c e f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_346
    {a b c e g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : c + g < 2 * e)
    : 2 * a + b + c < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat103_347
    {a b c e f : ℕ}
    (h0 : 2 * a + b + c < a + 2 * b + e)
    (h1 : 2 * b < e)
    (h2 : 2 * e = a + 2 * b + c)
    (h3 : 4 * e = 3 * a + 6 * b)
    (h4 : a + b + f < 2 * e)
    : 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BCEFG` / `EE·BBB·BBC·BCC·CCC` dies on power system `S00` (carriers κ, ξ). -/
theorem quarticChamberBCEFG59810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG59810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat103_308 hcq13 hAD hcq0 h hDn hcq9)
      · exact Or.inr (by exact astra4wPowerNat103_226 hcq13 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_309 hcq13 hAD hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat103_228 hcq13 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_229 hcq13 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_310 hcq13 hAD hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat103_311 hcq13 hAD hcq1 hcq0 h hDn)
      · exact Or.inr (by exact astra4wPowerNat103_232 hcq13 hcq1 hcq0 h)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_312 hcq13 hcq1 hcq0 h hcq4 hcq7)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_313 hcq13 hAD hcq0 h hDn hcq9)
      · exact Or.inr (by exact astra4wPowerNat103_235 hcq13 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_314 hcq13 h hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_237 hcq13 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_238 hcq13 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_315 hcq13 hcq0 h hDn hcq9)
      · exact Or.inr (by exact astra4wPowerNat103_316 hcq13 hcq1 hcq0 h hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_241 hcq13 hcq1 hcq0 h)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_317 hcq13 hcq1 h hcq0 hcq7)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_318 hcq13 hAD h hcq0 hDn hcq9)
      · exact Or.inr (by exact astra4wPowerNat103_244 hcq13 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_319 hcq13 h hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_246 hcq13 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_247 hcq13 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_320 hcq13 h hcq0 hDn hcq9)
      · exact Or.inr (by exact astra4wPowerNat103_321 hcq13 hcq1 h hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_250 hcq13 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_251 hcq13 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_322 hcq13 hAD hcq1 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_253 hcq13 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_254 hcq13 hcq1 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_323 hcq13 hcq1 h hcq0 hcq7 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_256 hcq13 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_324 h hcq13 hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_258 hcq13 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_259 hcq13 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_325 hcq13 h hcq0 hDn hcq9)
      · exact Or.inr (by exact astra4wPowerNat103_326 hcq13 hcq1 h hcq0 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_262 hcq13 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_263 hcq13 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_327 hcq13 hcq1 h hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_265 hcq13 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_266 hcq13 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_267 hcq13 hcq1 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_268 h hcq13 hcq1 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_328 h hcq13 hcq1 hcq0 hcq7 hDn)
    · exact Or.inr (by exact astra4wPowerNat103_270 h hcq13 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat103_329 hcq13 hcq0 h hDn)
    · exact Or.inr (by exact astra4wPowerNat103_272 h hcq13 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat103_273 h hcq13 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat103_330 h hcq13 hcq0 hcq4 hDn)
    · exact Or.inr (by exact astra4wPowerNat103_331 h hcq13 hcq1 hcq0 hDn)
    · exact Or.inr (by exact astra4wPowerNat103_276 h hcq13 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat103_277 h hcq13 hcq0)
    · exact Or.inr (by exact astra4wPowerNat103_332 h hcq13 hcq1 hcq0 hcq4 hDn)
    · exact Or.inr (by exact astra4wPowerNat103_279 h hcq13 hcq0)
    · exact Or.inr (by exact astra4wPowerNat103_280 h hcq13 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat103_281 h hcq13 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat103_333 h hcq13 hcq0 hDn hcq9)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by exact astra4wPowerNat103_201 hcq1 hcq7) (by exact astra4wPowerNat103_202 hcq1 hcq0 hcq4) hz0l hz0beta (Or.inr (by exact astra4wPowerNat103_204 hcq13 hcq1 hcq0 hcq4)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat103_206 hcq13 hcq0 hcq4)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top_S00 hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_207 hcq1 hcq0)
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
      · exact Or.inr (by exact astra4wPowerNat103_334 hcq13 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_335 hcq13 hcq1 hcq0 h)
      · exact absurd h (by exact astra4wPowerNat103_336 hcq13 hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_337 h hcq13 hcq1 hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_338 h hcq13 hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_339 h hcq13 hcq1 hcq0 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_340 hcq13 hcq1 h hcq0 hcq4)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_341 hcq13 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_342 hcq13 hcq1 hcq0 h)
      · exact absurd h (by exact astra4wPowerNat103_343 hcq13 hcq0 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat103_344 hcq13 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_345 h hcq13 hcq1 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_346 h hcq13 hcq1 hcq0 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_347 h hcq13 hcq1 hcq0 hcq4)
  have hr1 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by exact astra4wPowerNat103_208 hcq13) (by exact astra4wPowerNat103_211 hcq13 hcq1 hcq0) (by exact astra4wPowerNat103_213 hcq13 hcq1 hcq7) (by exact astra4wPowerNat103_214 hcq13 hcq1 hcq0 hcq4) (by exact astra4wPowerNat103_217 hcq1 hcq7) (by exact astra4wPowerNat103_218 hcq13 hcq0 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat103_304 hcq13 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat103_305 hcq13 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat103_306 hcq13 hcq1 hcq0 hcq4 hcq7)) (Or.inr (by exact astra4wPowerNat103_307 hcq13 hcq1 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat103_222 hcq13 hcq0 hcq4))
  have hct1 := xiQuarticChamberFace5810_coeff_top_S00 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat103_224 hcq1 hcq0)
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
/-- Chamber `BCDEFG` / `EE·BBB·BBC·BCC·CCC` dies on power system `S00` (carriers κ, ξ). -/
theorem quarticChamberBCDEFG127810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG127810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat103_225 hcq18 hcq1 hcq0 h hcq8 hcq7)
      · exact Or.inr (by exact astra4wPowerNat103_226 hcq18 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_227 hcq18 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_228 hcq18 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_229 hcq18 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_230 hcq18 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_231 hcq18 hcq1 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_232 hcq18 hcq1 hcq0 h)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_233 hcq18 hcq1 hcq0 h hcq8 hcq4 hcq7)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_234 hcq18 hcq1 hcq0 h hcq8 hcq7)
      · exact Or.inr (by exact astra4wPowerNat103_235 hcq18 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_236 hcq18 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_237 hcq18 hcq0 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_238 hcq18 hcq1 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_239 hcq18 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_240 hcq18 hcq1 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_241 hcq18 hcq1 hcq0 h)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_242 hcq18 hcq1 h hcq0 hcq8 hcq7)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_243 hcq18 hcq1 h hcq0 hcq8 hcq7)
      · exact Or.inr (by exact astra4wPowerNat103_244 hcq18 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_245 hcq18 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_246 hcq18 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_247 hcq18 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_248 hcq18 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_249 hcq18 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_250 hcq18 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_251 hcq18 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_252 hcq18 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_253 hcq18 h hcq0)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_254 hcq18 hcq1 h hcq0)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_255 hcq18 hcq1 h hcq0 hcq8 hcq7)
      · exact Or.inr (by exact astra4wPowerNat103_256 hcq18 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_257 h hcq18 hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_258 hcq18 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_259 hcq18 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_260 hcq18 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_261 hcq18 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_262 hcq18 hcq1 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_263 hcq18 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_264 hcq18 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_265 hcq18 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_266 hcq18 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_267 hcq18 hcq1 h hcq0)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_268 h hcq18 hcq1 hcq0)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_269 h hcq18 hcq1 hcq0 hcq8 hcq7)
    · exact Or.inr (by exact astra4wPowerNat103_270 h hcq18 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat103_271 hcq18 hcq0 hcq8 h)
    · exact Or.inr (by exact astra4wPowerNat103_272 h hcq18 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat103_273 h hcq18 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat103_274 h hcq18 hcq0 hcq8)
    · exact Or.inr (by exact astra4wPowerNat103_275 h hcq18 hcq1 hcq0 hcq8)
    · exact Or.inr (by exact astra4wPowerNat103_276 h hcq18 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat103_277 h hcq18 hcq0)
    · exact Or.inr (by exact astra4wPowerNat103_278 h hcq18 hcq1 hcq0 hcq8)
    · exact Or.inr (by exact astra4wPowerNat103_279 h hcq18 hcq0)
    · exact Or.inr (by exact astra4wPowerNat103_280 h hcq18 hcq0 hcq4)
    · exact Or.inr (by exact astra4wPowerNat103_281 h hcq18 hcq1 hcq0)
    · exact Or.inr (by exact astra4wPowerNat103_282 h hcq18 hcq0 hcq8)
  have hr0 : (kappaQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest1810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat103_200 hcq18 hcq0 hcq8) (by exact astra4wPowerNat103_201 hcq1 hcq7) (by exact astra4wPowerNat103_202 hcq1 hcq0 hcq4) (by exact astra4wPowerNat103_203 hcq0 hcq8) hz0l hz0beta (Or.inr (by exact astra4wPowerNat103_204 hcq18 hcq1 hcq0 hcq4)) hz0delta (Or.inr (by exact astra4wPowerNat103_205 hcq18 hcq0 hcq8 hcq4)) hz0zeta (Or.inr (by exact astra4wPowerNat103_206 hcq18 hcq0 hcq4)) hz0theta
  have hct0 := kappaQuarticChamberFace1810_coeff_top_S00 hAne hBne hCne (D := D) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_207 hcq1 hcq0)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_283 hcq18 hcq1 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_284 hcq18 hcq1 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_285 hcq18 hcq1 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_286 h hcq18 hcq1 hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_287 h hcq18 hcq1 hcq0 hcq8 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_288 h hcq18 hcq1 hcq0 hcq8 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_289 hcq18 hcq1 h hcq0 hcq8 hcq4 hcq7)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_290 hcq18 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_291 hcq18 hcq1 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_292 hcq18 hcq1 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_293 hcq18 hcq1 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_294 h hcq18 hcq1 hcq0 hcq8 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_295 h hcq18 hcq1 hcq0 hcq8 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_296 h hcq18 hcq1 hcq0 hcq4)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_297 hcq8 h)
      · exact Or.inr (by exact astra4wPowerNat103_298 hcq1 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_299 hcq18 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_300 hcq18 hcq0 h hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_301 hcq18 hcq0 h hcq8 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_302 h hcq18 hcq1 hcq0 hcq8 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_303 h hcq18 hcq1 hcq0 hcq4)
  have hr1 : (xiQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest5810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat103_208 hcq18) (by exact astra4wPowerNat103_209 hcq1 hcq0 hcq8) (by exact astra4wPowerNat103_210 hcq18 hcq0 hcq8) (by exact astra4wPowerNat103_211 hcq18 hcq1 hcq0) (by exact astra4wPowerNat103_212 hcq0 hcq8 hcq4) (by exact astra4wPowerNat103_213 hcq18 hcq1 hcq7) (by exact astra4wPowerNat103_214 hcq18 hcq1 hcq0 hcq4) (by exact astra4wPowerNat103_215 hcq18 hcq0 hcq8) (by exact astra4wPowerNat103_216 hcq18 hcq1 hcq0 hcq8) (by exact astra4wPowerNat103_217 hcq1 hcq7) (by exact astra4wPowerNat103_218 hcq18 hcq0 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat103_219 hcq18 hcq1 hcq0 hcq8 hcq4)) hz1delta (Or.inr (by exact astra4wPowerNat103_220 hcq18 hcq1 hcq0 hcq8 hcq4 hcq7)) (Or.inr (by exact astra4wPowerNat103_221 hcq18 hcq1 hcq0 hcq8 hcq4)) (Or.inr (by exact astra4wPowerNat103_222 hcq18 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat103_223 hcq18 hcq0 hcq8 hcq4))
  have hct1 := xiQuarticChamberFace5810_coeff_top_S00 hAne hBne hCne hEne (D := D) (F := F) (G := G) (by exact astra4wPowerNat103_224 hcq1 hcq0)
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
/-- Chamber `BCDE` / `DD·CCC` dies on power system `S05` (carriers μ, π). -/
theorem quarticChamberBCDE6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDE6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_147 hcq4 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_148 hcq4 hcq10 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_149 hcq10 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_150 h hcq1 hcq10 hcq0 hcq8)
      · exact absurd h (by exact astra4wPowerNat103_151 hcq4 hcq10 hcq0 hFn)
      · exact absurd h (by exact astra4wPowerNat103_179 hcq4 hcq10 hcq0 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_198 hcq1 h hcq10 hcq0 hcq8)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_046 hcq4 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_047 hcq4 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_048 hcq10 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_049 hcq1 hcq10 h hcq0 hcq8)
      · exact absurd h (by exact astra4wPowerNat103_154 hcq4 hcq10 hcq0 hFn)
      · exact absurd h (by exact astra4wPowerNat103_181 hcq4 hcq10 hcq0 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_155 hcq1 h hcq10 hcq0 hcq8)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_053 hcq4 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_054 hcq4 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_055 hcq10 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_056 hcq1 hcq10 h hcq0 hcq8)
      · exact absurd h (by exact astra4wPowerNat103_156 hcq4 hcq10 hcq0 hFn)
      · exact absurd h (by exact astra4wPowerNat103_182 hcq4 hcq10 hcq0 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_157 hApos h hcq4 hcq0 hcq8)
  have hr0 : (muQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest12810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz hGz (by exact astra4wPowerNat103_000 hcq4) (by exact astra4wPowerNat103_001 hcq4 hcq0 hcq8) (by exact astra4wPowerNat103_003 hcq4 hcq1 hcq0 hcq8) (by exact astra4wPowerNat103_004 hcq8) (by exact astra4wPowerNat103_007 hcq1) hz0l hz0beta (Or.inr (by exact astra4wPowerNat103_195 hApos hcq4 hcq0 hcq8)) hz0delta (Or.inr (by exact astra4wPowerNat103_009 hApos hcq4 hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat103_010 hApos hcq4 hcq0 hcq8)) (Or.inr (by exact astra4wPowerNat103_196 hcq4 hcq0 hcq8)) (Or.inr (by exact astra4wPowerNat103_012 hApos hcq4 hcq0))
  have hct0 := muQuarticChamberFace12810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_013 hcq0)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_158 hcq4 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_159 hcq4 hcq10 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_160 hcq10 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_161 h hcq1 hcq10 hcq0 hcq8)
      · exact absurd h (by exact astra4wPowerNat103_151 hcq4 hcq10 hcq0 hFn)
      · exact absurd h (by exact astra4wPowerNat103_179 hcq4 hcq10 hcq0 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_199 hcq4 hcq1 h hcq10 hcq0 hcq8)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_164 hcq4 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_165 hcq4 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_166 hcq10 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_167 hcq1 hcq10 h hcq0 hcq8)
      · exact absurd h (by exact astra4wPowerNat103_154 hcq4 hcq10 hcq0 hFn)
      · exact absurd h (by exact astra4wPowerNat103_181 hcq4 hcq10 hcq0 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_169 hcq1 h hcq10 hcq0 hcq8)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_170 hcq4 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_171 hcq4 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_172 hcq10 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat103_173 hcq1 hcq10 h hcq0 hcq8)
      · exact absurd h (by exact astra4wPowerNat103_156 hcq4 hcq10 hcq0 hFn)
      · exact absurd h (by exact astra4wPowerNat103_182 hcq4 hcq10 hcq0 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_175 hApos h hcq4 hcq1 hcq0 hcq8)
  have hr1 : (piQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest5810_natDegree_lt_of_live_BCDE l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz hGz (by exact astra4wPowerNat103_014 hcq4 hcq0) (by exact astra4wPowerNat103_015 hcq4 hcq0 hcq8) (by exact astra4wPowerNat103_016 hcq4) (by exact astra4wPowerNat103_017 hcq4 hcq0 hcq8) (by exact astra4wPowerNat103_020 hcq4 hcq1 hcq0) (by exact astra4wPowerNat103_022 hcq4 hcq1 hcq0 hcq8) (by exact astra4wPowerNat103_023 hcq0 hcq8) (by exact astra4wPowerNat103_024 hcq8) (by exact astra4wPowerNat103_030 hcq1) (by exact astra4wPowerNat103_031 hcq1 hcq10 hcq0) hz1l hz1beta (Or.inr (by exact astra4wPowerNat103_142 hApos hcq4 hcq1 hcq0 hcq8)) hz1delta (Or.inr (by exact astra4wPowerNat103_143 hApos hcq4 hcq1 hcq0 hcq8)) (Or.inr (by exact astra4wPowerNat103_144 hApos hcq4 hcq1 hcq0 hcq8)) (Or.inr (by exact astra4wPowerNat103_197 hApos hcq4 hcq0 hcq8)) (Or.inr (by exact astra4wPowerNat103_146 hApos hcq4 hcq0))
  have hct1 := piQuarticChamberFace5810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_038 hcq0)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact quarticPowerInnerS05810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hCc hDc


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
/-- Chamber `BCDF` / `DD·CCC` dies on power system `S05` (carriers μ, π). -/
theorem quarticChamberBCDF24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDF24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_039 hcq6 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat103_040 hcq6 hcq10 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_041 hcq10 h hcq0 hcq9)
      · exact absurd h (by exact astra4wPowerNat103_133 hcq6 hcq10 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_043 h hcq10 hcq0 hcq9 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_179 hcq6 hcq10 hcq0 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_193 h hcq10 hcq0 hcq9 hcq3)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_046 hcq6 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_047 hcq6 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_048 hcq10 h hcq0 hcq9)
      · exact absurd h (by exact astra4wPowerNat103_135 hcq6 hcq10 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_050 h hcq10 hcq0 hcq9 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_181 hcq6 hcq10 hcq0 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_136 h hcq10 hcq0 hcq9 hcq3)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_053 hcq6 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_054 hcq6 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_055 hcq10 h hcq0 hcq9)
      · exact absurd h (by exact astra4wPowerNat103_137 hcq6 hcq10 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_057 hcq10 h hcq0 hcq9 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_182 hcq6 hcq10 hcq0 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_059 hApos h hcq6 hcq0 hcq9 hcq1)
  have hr0 : (muQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest12810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz hGz (by exact astra4wPowerNat103_000 hcq6) (by exact astra4wPowerNat103_001 hcq6 hcq0 hcq9) (by exact astra4wPowerNat103_002 hcq1) (by exact astra4wPowerNat103_004 hcq9) (by exact astra4wPowerNat103_006 hcq3) hz0l hz0beta (Or.inr (by exact astra4wPowerNat103_176 hApos hcq6 hcq0)) hz0delta (Or.inr (by exact astra4wPowerNat103_129 hApos hcq6 hcq0)) (Or.inr (by exact astra4wPowerNat103_010 hApos hcq6 hcq0 hcq9)) (Or.inr (by exact astra4wPowerNat103_011 hApos hcq6)) (Or.inr (by exact astra4wPowerNat103_012 hApos hcq6 hcq0))
  have hct0 := muQuarticChamberFace12810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_013 hcq0)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_060 hcq6 h hcq0 hcq9 hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_061 hcq6 hcq2 hcq10 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_062 hcq10 h hcq0 hcq9 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_133 hcq6 hcq10 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_064 h hcq10 hcq0 hcq9 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_179 hcq6 hcq10 hcq0 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_194 hcq6 h hcq10 hcq0 hcq9 hcq3)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_067 hcq6 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_068 hcq6 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_069 hcq10 h hcq0 hcq9 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_135 hcq6 hcq10 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_071 h hcq10 hcq0 hcq9 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_181 hcq6 hcq10 hcq0 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_139 h hcq10 hcq0 hcq9 hcq3)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_074 hcq6 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_075 hcq6 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_076 hcq10 h hcq0 hcq9 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_137 hcq6 hcq10 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_078 hcq10 h hcq0 hcq9 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_182 hcq6 hcq10 hcq0 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_140 hApos h hcq6 hcq0 hcq9 hcq1)
  have hr1 : (piQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest5810_natDegree_lt_of_live_BCDF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz hGz (by exact astra4wPowerNat103_014 hcq6 hcq0) (by exact astra4wPowerNat103_015 hcq6 hcq0 hcq9) (by exact astra4wPowerNat103_016 hcq6) (by exact astra4wPowerNat103_017 hcq6 hcq0 hcq9) (by exact astra4wPowerNat103_019 hcq1) (by exact astra4wPowerNat103_021 hcq6 hcq0 hcq9 hcq3) (by exact astra4wPowerNat103_023 hcq0 hcq9) (by exact astra4wPowerNat103_024 hcq9) (by exact astra4wPowerNat103_025 hcq2 hcq0) (by exact astra4wPowerNat103_029 hcq3) hz1l hz1beta (Or.inr (by exact astra4wPowerNat103_192 hApos hcq6 hcq2 hcq0 hcq1)) hz1delta (Or.inr (by exact astra4wPowerNat103_131 hApos hcq6 hcq0 hcq1)) (Or.inr (by exact astra4wPowerNat103_132 hApos hcq6 hcq0 hcq9 hcq1 hcq3)) (Or.inr (by exact astra4wPowerNat103_178 hApos hcq6 hcq0)) (Or.inr (by exact astra4wPowerNat103_037 hApos hcq6 hcq0 hcq1))
  have hct1 := piQuarticChamberFace5810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_038 hcq0)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact quarticPowerInnerS05810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hCc hDc


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
/-- Chamber `CDEF` / `DD·CCC` dies on power system `S05` (carriers μ, π). -/
theorem quarticChamberCDEF14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF14810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_090 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_091 hcq7 h)
      · exact Or.inr (by exact astra4wPowerNat103_092 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_093 h hcq2 hcq7 hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_094 h hcq7 hcq0 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_188 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_096 hcq2 h hcq7 hcq0 hcq3)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_097 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_098 hcq7 h)
      · exact Or.inr (by exact astra4wPowerNat103_099 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_100 hcq2 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_101 h hcq7 hcq0 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_189 hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_103 h hcq7 hcq0 hcq3)
  have hz0delta : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_104 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_105 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_106 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_107 hcq2 hcq7 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_108 hcq7 h hcq0 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_190 hApos hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_110 hApos hcq1 hcq0 h)
  have hr0 : (muQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest12810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hBz hGz (by exact astra4wPowerNat103_006 hcq3) (by exact astra4wPowerNat103_007 hcq2) hz0l hz0beta (Or.inr (by exact astra4wPowerNat103_184 hApos hcq1 hcq0)) hz0delta (Or.inr (by exact astra4wPowerNat103_082 hApos hcq1 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat103_083 hApos hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat103_084 hApos hcq1))
  have hct0 := muQuarticChamberFace12810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_013 hcq0)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_090 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_111 hcq1 hcq7 h)
      · exact Or.inr (by exact astra4wPowerNat103_112 hcq7 h hcq0 hcq3)
      · exact Or.inr (by exact astra4wPowerNat103_113 h hcq2 hcq7 hcq0 hcq3)
      · exact Or.inr (by exact astra4wPowerNat103_114 h hcq7 hcq0 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_188 hApos hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_191 hcq2 h hcq7 hcq0 hcq3)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_097 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_117 hcq1 hcq7 h)
      · exact Or.inr (by exact astra4wPowerNat103_118 hcq7 h hcq0 hcq3)
      · exact Or.inr (by exact astra4wPowerNat103_119 hcq2 hcq7 h hcq0 hcq3)
      · exact Or.inr (by exact astra4wPowerNat103_120 h hcq7 hcq0 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_189 hApos hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_122 hcq2 h hcq7 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_104 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_123 hcq1 h)
      · exact Or.inr (by exact astra4wPowerNat103_124 hcq7 h hcq0 hcq3)
      · exact Or.inr (by exact astra4wPowerNat103_125 hcq2 hcq7 h hcq0 hcq3)
      · exact Or.inr (by exact astra4wPowerNat103_126 hcq7 h hcq0 hcq3)
      · exact absurd h (by exact astra4wPowerNat103_190 hApos hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_128 hApos h hcq1 hcq2 hcq0)
  have hr1 : (piQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest5810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hBz hGz (by exact astra4wPowerNat103_025 hcq1 hcq0) (by exact astra4wPowerNat103_029 hcq3) (by exact astra4wPowerNat103_030 hcq2) (by exact astra4wPowerNat103_031 hcq2 hcq7 hcq0) hz1l hz1beta (Or.inr (by exact astra4wPowerNat103_185 hApos hcq1 hcq2 hcq0)) hz1delta (Or.inr (by exact astra4wPowerNat103_086 hApos hcq1 hcq2 hcq0)) (Or.inr (by exact astra4wPowerNat103_087 hApos hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat103_186 hApos hcq1)) (Or.inr (by exact astra4wPowerNat103_187 hApos hcq1 hcq0))
  have hct1 := piQuarticChamberFace5810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_038 hcq0)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact quarticPowerInnerS05810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hCc hDc


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
/-- Chamber `BCDEF` / `DD·CCC` dies on power system `S05` (carriers μ, π). -/
theorem quarticChamberBCDEF42810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEF42810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_039 hcq9 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_040 hcq9 hcq15 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_041 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_042 h hcq3 hcq15 hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_043 h hcq15 hcq0 hcq13 hcq4)
      · exact absurd h (by exact astra4wPowerNat103_179 hcq9 hcq15 hcq0 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_180 hcq3 h hcq15 hcq0 hcq13 hcq4)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_046 hcq9 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_047 hcq9 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_048 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_049 hcq3 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_050 h hcq15 hcq0 hcq13 hcq4)
      · exact absurd h (by exact astra4wPowerNat103_181 hcq9 hcq15 hcq0 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_052 hcq3 h hcq15 hcq0 hcq13 hcq4)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_053 hcq9 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_054 hcq9 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_055 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_056 hcq3 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_057 hcq15 h hcq0 hcq13 hcq4)
      · exact absurd h (by exact astra4wPowerNat103_182 hcq9 hcq15 hcq0 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_059 hApos h hcq9 hcq0 hcq13 hcq1)
  have hr0 : (muQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest12810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hGz (by exact astra4wPowerNat103_000 hcq9) (by exact astra4wPowerNat103_001 hcq9 hcq0 hcq13) (by exact astra4wPowerNat103_002 hcq1) (by exact astra4wPowerNat103_003 hcq9 hcq3 hcq0 hcq13) (by exact astra4wPowerNat103_004 hcq13) (by exact astra4wPowerNat103_006 hcq4) (by exact astra4wPowerNat103_007 hcq3) hz0l hz0beta (Or.inr (by exact astra4wPowerNat103_176 hApos hcq9 hcq0)) hz0delta (Or.inr (by exact astra4wPowerNat103_009 hApos hcq9 hcq3 hcq0)) (Or.inr (by exact astra4wPowerNat103_010 hApos hcq9 hcq0 hcq13)) (Or.inr (by exact astra4wPowerNat103_011 hApos hcq9)) (Or.inr (by exact astra4wPowerNat103_012 hApos hcq9 hcq0))
  have hct0 := muQuarticChamberFace12810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_013 hcq0)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_060 hcq9 h hcq0 hcq13 hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_061 hcq9 hcq2 hcq15 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_062 hcq15 h hcq0 hcq13 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_063 h hcq3 hcq15 hcq0 hcq13 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_064 h hcq15 hcq0 hcq13 hcq4)
      · exact absurd h (by exact astra4wPowerNat103_179 hcq9 hcq15 hcq0 hGn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_183 hcq9 hcq3 h hcq15 hcq0 hcq13 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_067 hcq9 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_068 hcq9 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_069 hcq15 h hcq0 hcq13 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_070 hcq3 hcq15 h hcq0 hcq13 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_071 h hcq15 hcq0 hcq13 hcq4)
      · exact absurd h (by exact astra4wPowerNat103_181 hcq9 hcq15 hcq0 hGn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_073 hcq3 h hcq15 hcq0 hcq13 hcq4)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_074 hcq9 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_075 hcq9 hcq2 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_076 hcq15 h hcq0 hcq13 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_077 hcq3 hcq15 h hcq0 hcq13 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_078 hcq15 h hcq0 hcq13 hcq4)
      · exact absurd h (by exact astra4wPowerNat103_182 hcq9 hcq15 hcq0 hGn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_080 hApos h hcq9 hcq3 hcq0 hcq13 hcq1)
  have hr1 : (piQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest5810_natDegree_lt_of_live_BCDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hGz (by exact astra4wPowerNat103_014 hcq9 hcq0) (by exact astra4wPowerNat103_015 hcq9 hcq0 hcq13) (by exact astra4wPowerNat103_016 hcq9) (by exact astra4wPowerNat103_017 hcq9 hcq0 hcq13) (by exact astra4wPowerNat103_019 hcq1) (by exact astra4wPowerNat103_020 hcq9 hcq3 hcq0) (by exact astra4wPowerNat103_021 hcq9 hcq0 hcq13 hcq4) (by exact astra4wPowerNat103_022 hcq9 hcq3 hcq0 hcq13) (by exact astra4wPowerNat103_023 hcq0 hcq13) (by exact astra4wPowerNat103_024 hcq13) (by exact astra4wPowerNat103_025 hcq2 hcq0) (by exact astra4wPowerNat103_027 hcq9 hcq3 hcq0 hcq4) (by exact astra4wPowerNat103_029 hcq4) (by exact astra4wPowerNat103_030 hcq3) (by exact astra4wPowerNat103_031 hcq3 hcq15 hcq0) hz1l hz1beta (Or.inr (by exact astra4wPowerNat103_177 hApos hcq9 hcq2 hcq3 hcq0 hcq1)) hz1delta (Or.inr (by exact astra4wPowerNat103_034 hApos hcq9 hcq3 hcq0 hcq1)) (Or.inr (by exact astra4wPowerNat103_035 hApos hcq9 hcq3 hcq0 hcq13 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat103_178 hApos hcq9 hcq0)) (Or.inr (by exact astra4wPowerNat103_037 hApos hcq9 hcq0 hcq1))
  have hct1 := piQuarticChamberFace5810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_038 hcq0)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact quarticPowerInnerS05810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hCc hDc


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
/-- Chamber `BCDEG` / `DD·CCC` dies on power system `S05` (carriers μ, π). -/
theorem quarticChamberBCDEG42810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEG42810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_147 hcq9 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_148 hcq9 hcq15 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_149 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_150 h hcq3 hcq15 hcq0 hcq13)
      · exact absurd h (by exact astra4wPowerNat103_151 hcq9 hcq15 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat103_152 h hcq15 hcq0 hcq13 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_153 hcq3 h hcq15 hcq0 hcq13 hcq2)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_046 hcq9 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_047 hcq9 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_048 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_049 hcq3 hcq15 h hcq0 hcq13)
      · exact absurd h (by exact astra4wPowerNat103_154 hcq9 hcq15 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat103_051 h hcq15 hcq0 hcq13 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_155 hcq3 h hcq15 hcq0 hcq13)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_053 hcq9 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_054 hcq9 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_055 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_056 hcq3 hcq15 h hcq0 hcq13)
      · exact absurd h (by exact astra4wPowerNat103_156 hcq9 hcq15 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat103_058 h hcq15 hcq0 hcq13 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_157 hApos h hcq9 hcq0 hcq13)
  have hr0 : (muQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest12810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by exact astra4wPowerNat103_000 hcq9) (by exact astra4wPowerNat103_001 hcq9 hcq0 hcq13) (by exact astra4wPowerNat103_003 hcq9 hcq3 hcq0 hcq13) (by exact astra4wPowerNat103_004 hcq13) (by exact astra4wPowerNat103_005 hcq2) (by exact astra4wPowerNat103_007 hcq3) hz0l hz0beta (Or.inr (by exact astra4wPowerNat103_141 hApos hcq9 hcq0 hcq13 hcq2)) hz0delta (Or.inr (by exact astra4wPowerNat103_009 hApos hcq9 hcq3 hcq0)) (Or.inr (by exact astra4wPowerNat103_010 hApos hcq9 hcq0 hcq13)) (Or.inr (by exact astra4wPowerNat103_011 hApos hcq9)) (Or.inr (by exact astra4wPowerNat103_012 hApos hcq9 hcq0))
  have hct0 := muQuarticChamberFace12810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_013 hcq0)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_158 hcq9 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_159 hcq9 hcq15 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_160 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_161 h hcq3 hcq15 hcq0 hcq13)
      · exact absurd h (by exact astra4wPowerNat103_151 hcq9 hcq15 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat103_162 h hcq15 hcq0 hcq13 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_163 hcq9 hcq3 h hcq15 hcq0 hcq13 hcq2)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_164 hcq9 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_165 hcq9 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_166 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_167 hcq3 hcq15 h hcq0 hcq13)
      · exact absurd h (by exact astra4wPowerNat103_154 hcq9 hcq15 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat103_168 h hcq15 hcq0 hcq13 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_169 hcq3 h hcq15 hcq0 hcq13)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_170 hcq9 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_171 hcq9 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_172 hcq15 h hcq0 hcq13)
      · exact Or.inr (by exact astra4wPowerNat103_173 hcq3 hcq15 h hcq0 hcq13)
      · exact absurd h (by exact astra4wPowerNat103_156 hcq9 hcq15 hcq0 hFn)
      · exact Or.inr (by exact astra4wPowerNat103_174 h hcq15 hcq0 hcq13 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_175 hApos h hcq9 hcq3 hcq0 hcq13)
  have hr1 : (piQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest5810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by exact astra4wPowerNat103_014 hcq9 hcq0) (by exact astra4wPowerNat103_015 hcq9 hcq0 hcq13) (by exact astra4wPowerNat103_016 hcq9) (by exact astra4wPowerNat103_017 hcq9 hcq0 hcq13) (by exact astra4wPowerNat103_018 hcq9 hcq0 hcq2) (by exact astra4wPowerNat103_020 hcq9 hcq3 hcq0) (by exact astra4wPowerNat103_022 hcq9 hcq3 hcq0 hcq13) (by exact astra4wPowerNat103_023 hcq0 hcq13) (by exact astra4wPowerNat103_024 hcq13) (by exact astra4wPowerNat103_026 hcq0 hcq13 hcq2) (by exact astra4wPowerNat103_028 hcq2) (by exact astra4wPowerNat103_030 hcq3) (by exact astra4wPowerNat103_031 hcq3 hcq15 hcq0) (by exact astra4wPowerNat103_032 hcq0 hcq2) hz1l hz1beta (Or.inr (by exact astra4wPowerNat103_142 hApos hcq9 hcq3 hcq0 hcq13)) hz1delta (Or.inr (by exact astra4wPowerNat103_143 hApos hcq9 hcq3 hcq0 hcq13)) (Or.inr (by exact astra4wPowerNat103_144 hApos hcq9 hcq3 hcq0 hcq13)) (Or.inr (by exact astra4wPowerNat103_145 hApos hcq9 hcq0 hcq13 hcq2)) (Or.inr (by exact astra4wPowerNat103_146 hApos hcq9 hcq0))
  have hct1 := piQuarticChamberFace5810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_038 hcq0)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact quarticPowerInnerS05810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hCc hDc


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
/-- Chamber `BCDFG` / `DD·CCC` dies on power system `S05` (carriers μ, π). -/
theorem quarticChamberBCDFG60810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG60810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_039 hcq11 h hcq0 hcq14)
      · exact Or.inr (by exact astra4wPowerNat103_040 hcq11 hcq15 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_041 hcq15 h hcq0 hcq14)
      · exact absurd h (by exact astra4wPowerNat103_133 hcq11 hcq15 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_043 h hcq15 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat103_044 h hcq15 hcq0 hcq14 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_134 h hcq15 hcq0 hcq14 hcq4 hcq5)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_046 hcq11 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_047 hcq11 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_048 hcq15 h hcq0 hcq14)
      · exact absurd h (by exact astra4wPowerNat103_135 hcq11 hcq15 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_050 h hcq15 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat103_051 h hcq15 hcq0 hcq14 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_136 h hcq15 hcq0 hcq14 hcq5)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_053 hcq11 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_054 hcq11 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_055 hcq15 h hcq0 hcq14)
      · exact absurd h (by exact astra4wPowerNat103_137 hcq11 hcq15 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_057 hcq15 h hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat103_058 h hcq15 hcq0 hcq14 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_059 hApos h hcq11 hcq0 hcq14 hcq1)
  have hr0 : (muQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest12810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by exact astra4wPowerNat103_000 hcq11) (by exact astra4wPowerNat103_001 hcq11 hcq0 hcq14) (by exact astra4wPowerNat103_002 hcq1) (by exact astra4wPowerNat103_004 hcq14) (by exact astra4wPowerNat103_005 hcq4) (by exact astra4wPowerNat103_006 hcq5) hz0l hz0beta (Or.inr (by exact astra4wPowerNat103_008 hApos hcq11 hcq0 hcq4)) hz0delta (Or.inr (by exact astra4wPowerNat103_129 hApos hcq11 hcq0)) (Or.inr (by exact astra4wPowerNat103_010 hApos hcq11 hcq0 hcq14)) (Or.inr (by exact astra4wPowerNat103_011 hApos hcq11)) (Or.inr (by exact astra4wPowerNat103_012 hApos hcq11 hcq0))
  have hct0 := muQuarticChamberFace12810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_013 hcq0)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_060 hcq11 h hcq0 hcq14 hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_061 hcq11 hcq3 hcq15 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_062 hcq15 h hcq0 hcq14 hcq5)
      · exact absurd h (by exact astra4wPowerNat103_133 hcq11 hcq15 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_064 h hcq15 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat103_065 h hcq15 hcq0 hcq14 hcq4 hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_138 hcq11 h hcq15 hcq0 hcq14 hcq4 hcq5)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_067 hcq11 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_068 hcq11 hcq3 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_069 hcq15 h hcq0 hcq14 hcq5)
      · exact absurd h (by exact astra4wPowerNat103_135 hcq11 hcq15 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_071 h hcq15 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat103_072 h hcq15 hcq0 hcq14 hcq4 hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_139 h hcq15 hcq0 hcq14 hcq5)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_074 hcq11 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_075 hcq11 hcq3 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_076 hcq15 h hcq0 hcq14 hcq5)
      · exact absurd h (by exact astra4wPowerNat103_137 hcq11 hcq15 hcq0 hEn)
      · exact Or.inr (by exact astra4wPowerNat103_078 hcq15 h hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat103_079 h hcq15 hcq0 hcq14 hcq4 hcq5)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_140 hApos h hcq11 hcq0 hcq14 hcq1)
  have hr1 : (piQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest5810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz (by exact astra4wPowerNat103_014 hcq11 hcq0) (by exact astra4wPowerNat103_015 hcq11 hcq0 hcq14) (by exact astra4wPowerNat103_016 hcq11) (by exact astra4wPowerNat103_017 hcq11 hcq0 hcq14) (by exact astra4wPowerNat103_018 hcq11 hcq0 hcq4) (by exact astra4wPowerNat103_019 hcq1) (by exact astra4wPowerNat103_021 hcq11 hcq0 hcq14 hcq5) (by exact astra4wPowerNat103_023 hcq0 hcq14) (by exact astra4wPowerNat103_024 hcq14) (by exact astra4wPowerNat103_025 hcq3 hcq0) (by exact astra4wPowerNat103_026 hcq0 hcq14 hcq4) (by exact astra4wPowerNat103_028 hcq4) (by exact astra4wPowerNat103_029 hcq5) (by exact astra4wPowerNat103_032 hcq0 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat103_130 hApos hcq11 hcq3 hcq0 hcq14 hcq1)) hz1delta (Or.inr (by exact astra4wPowerNat103_131 hApos hcq11 hcq0 hcq1)) (Or.inr (by exact astra4wPowerNat103_132 hApos hcq11 hcq0 hcq14 hcq1 hcq5)) (Or.inr (by exact astra4wPowerNat103_036 hApos hcq11 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat103_037 hApos hcq11 hcq0 hcq1))
  have hct1 := piQuarticChamberFace5810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_038 hcq0)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact quarticPowerInnerS05810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hCc hDc


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
/-- Chamber `CDEFG` / `DD·CCC` dies on power system `S05` (carriers μ, π). -/
theorem quarticChamberCDEFG38810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG38810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    exact (Nat.ne_of_gt hApos) hz0
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_090 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_091 hcq12 h)
      · exact Or.inr (by exact astra4wPowerNat103_092 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_093 h hcq3 hcq12 hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_094 h hcq12 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_095 h hcq12 hcq0 hcq2)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_096 hcq3 h hcq12 hcq0 hcq4)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_097 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_098 hcq12 h)
      · exact Or.inr (by exact astra4wPowerNat103_099 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_100 hcq3 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_101 h hcq12 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_102 h hcq12 hcq0 hcq2)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_103 h hcq12 hcq0 hcq4)
  have hz0delta : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_104 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_105 hApos h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_106 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_107 hcq3 hcq12 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_108 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_109 h hcq12 hcq0 hcq2)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_110 hApos hcq1 hcq0 h)
  have hr0 : (muQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest12810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hBz (by exact astra4wPowerNat103_005 hcq2) (by exact astra4wPowerNat103_006 hcq4) (by exact astra4wPowerNat103_007 hcq3) hz0l hz0beta (Or.inr (by exact astra4wPowerNat103_081 hApos hcq1 hcq0 hcq2)) hz0delta (Or.inr (by exact astra4wPowerNat103_082 hApos hcq1 hcq3 hcq0)) (Or.inr (by exact astra4wPowerNat103_083 hApos hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat103_084 hApos hcq1))
  have hct0 := muQuarticChamberFace12810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_013 hcq0)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_090 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_111 hcq1 hcq12 h)
      · exact Or.inr (by exact astra4wPowerNat103_112 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_113 h hcq3 hcq12 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_114 h hcq12 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_115 h hcq12 hcq0 hcq2 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_116 hcq3 h hcq12 hcq0 hcq2 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_097 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_117 hcq1 hcq12 h)
      · exact Or.inr (by exact astra4wPowerNat103_118 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_119 hcq3 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_120 h hcq12 hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_121 h hcq12 hcq0 hcq2 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_122 hcq3 h hcq12 hcq0)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat103_104 hApos hBn)
      · exact Or.inr (by exact astra4wPowerNat103_123 hcq1 h)
      · exact Or.inr (by exact astra4wPowerNat103_124 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_125 hcq3 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_126 hcq12 h hcq0 hcq4)
      · exact Or.inr (by exact astra4wPowerNat103_127 h hcq12 hcq0 hcq2 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_128 hApos h hcq1 hcq3 hcq0)
  have hr1 : (piQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest5810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hBz (by exact astra4wPowerNat103_025 hcq1 hcq0) (by exact astra4wPowerNat103_028 hcq2) (by exact astra4wPowerNat103_029 hcq4) (by exact astra4wPowerNat103_030 hcq3) (by exact astra4wPowerNat103_031 hcq3 hcq12 hcq0) (by exact astra4wPowerNat103_032 hcq0 hcq2) hz1l hz1beta (Or.inr (by exact astra4wPowerNat103_085 hApos hcq1 hcq3 hcq0 hcq2)) hz1delta (Or.inr (by exact astra4wPowerNat103_086 hApos hcq1 hcq3 hcq0)) (Or.inr (by exact astra4wPowerNat103_087 hApos hcq1 hcq0)) (Or.inr (by exact astra4wPowerNat103_088 hApos hcq1 hcq0 hcq2)) (Or.inr (by exact astra4wPowerNat103_089 hApos hcq1 hcq0 hcq2))
  have hct1 := piQuarticChamberFace5810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_038 hcq0)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact quarticPowerInnerS05810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hCc hDc


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
/-- Chamber `BCDEFG` / `DD·CCC` dies on power system `S05` (carriers μ, π). -/
theorem quarticChamberBCDEFG114810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG114810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_039 hcq15 h hcq0 hcq19)
      · exact Or.inr (by exact astra4wPowerNat103_040 hcq15 hcq21 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_041 hcq21 h hcq0 hcq19)
      · exact Or.inr (by exact astra4wPowerNat103_042 h hcq5 hcq21 hcq0 hcq19)
      · exact Or.inr (by exact astra4wPowerNat103_043 h hcq21 hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_044 h hcq21 hcq0 hcq19 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_045 hcq5 h hcq21 hcq0 hcq19 hcq4 hcq6)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_046 hcq15 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_047 hcq15 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_048 hcq21 h hcq0 hcq19)
      · exact Or.inr (by exact astra4wPowerNat103_049 hcq5 hcq21 h hcq0 hcq19)
      · exact Or.inr (by exact astra4wPowerNat103_050 h hcq21 hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_051 h hcq21 hcq0 hcq19 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_052 hcq5 h hcq21 hcq0 hcq19 hcq6)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_053 hcq15 hcq0 h)
      · exact Or.inr (by exact astra4wPowerNat103_054 hcq15 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_055 hcq21 h hcq0 hcq19)
      · exact Or.inr (by exact astra4wPowerNat103_056 hcq5 hcq21 h hcq0 hcq19)
      · exact Or.inr (by exact astra4wPowerNat103_057 hcq21 h hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_058 h hcq21 hcq0 hcq19 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_059 hApos h hcq15 hcq0 hcq19 hcq1)
  have hr0 : (muQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat103_000 hcq15) (by exact astra4wPowerNat103_001 hcq15 hcq0 hcq19) (by exact astra4wPowerNat103_002 hcq1) (by exact astra4wPowerNat103_003 hcq15 hcq5 hcq0 hcq19) (by exact astra4wPowerNat103_004 hcq19) (by exact astra4wPowerNat103_005 hcq4) (by exact astra4wPowerNat103_006 hcq6) (by exact astra4wPowerNat103_007 hcq5) hz0l hz0beta (Or.inr (by exact astra4wPowerNat103_008 hApos hcq15 hcq0 hcq4)) hz0delta (Or.inr (by exact astra4wPowerNat103_009 hApos hcq15 hcq5 hcq0)) (Or.inr (by exact astra4wPowerNat103_010 hApos hcq15 hcq0 hcq19)) (Or.inr (by exact astra4wPowerNat103_011 hApos hcq15)) (Or.inr (by exact astra4wPowerNat103_012 hApos hcq15 hcq0))
  have hct0 := muQuarticChamberFace12810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_013 hcq0)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face12_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_060 hcq15 h hcq0 hcq19 hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_061 hcq15 hcq3 hcq21 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_062 hcq21 h hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_063 h hcq5 hcq21 hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_064 h hcq21 hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_065 h hcq21 hcq0 hcq19 hcq4 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_066 hcq15 hcq5 h hcq21 hcq0 hcq19 hcq4 hcq6)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_067 hcq15 h hcq0 hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_068 hcq15 hcq3 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_069 hcq21 h hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_070 hcq5 hcq21 h hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_071 h hcq21 hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_072 h hcq21 hcq0 hcq19 hcq4 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_073 hcq5 h hcq21 hcq0 hcq19 hcq6)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat103_074 hcq15 hcq0 h hcq1)
      · exact Or.inr (by exact astra4wPowerNat103_075 hcq15 hcq3 h hcq0)
      · exact Or.inr (by exact astra4wPowerNat103_076 hcq21 h hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_077 hcq5 hcq21 h hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_078 hcq21 h hcq0 hcq19 hcq6)
      · exact Or.inr (by exact astra4wPowerNat103_079 h hcq21 hcq0 hcq19 hcq4 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat103_080 hApos h hcq15 hcq5 hcq0 hcq19 hcq1)
  have hr1 : (piQuarticChamberRest5810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest5810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat103_014 hcq15 hcq0) (by exact astra4wPowerNat103_015 hcq15 hcq0 hcq19) (by exact astra4wPowerNat103_016 hcq15) (by exact astra4wPowerNat103_017 hcq15 hcq0 hcq19) (by exact astra4wPowerNat103_018 hcq15 hcq0 hcq4) (by exact astra4wPowerNat103_019 hcq1) (by exact astra4wPowerNat103_020 hcq15 hcq5 hcq0) (by exact astra4wPowerNat103_021 hcq15 hcq0 hcq19 hcq6) (by exact astra4wPowerNat103_022 hcq15 hcq5 hcq0 hcq19) (by exact astra4wPowerNat103_023 hcq0 hcq19) (by exact astra4wPowerNat103_024 hcq19) (by exact astra4wPowerNat103_025 hcq3 hcq0) (by exact astra4wPowerNat103_026 hcq0 hcq19 hcq4) (by exact astra4wPowerNat103_027 hcq15 hcq5 hcq0 hcq6) (by exact astra4wPowerNat103_028 hcq4) (by exact astra4wPowerNat103_029 hcq6) (by exact astra4wPowerNat103_030 hcq5) (by exact astra4wPowerNat103_031 hcq5 hcq21 hcq0) (by exact astra4wPowerNat103_032 hcq0 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat103_033 hApos hcq15 hcq3 hcq5 hcq0 hcq19 hcq1)) hz1delta (Or.inr (by exact astra4wPowerNat103_034 hApos hcq15 hcq5 hcq0 hcq1)) (Or.inr (by exact astra4wPowerNat103_035 hApos hcq15 hcq5 hcq0 hcq19 hcq1 hcq6)) (Or.inr (by exact astra4wPowerNat103_036 hApos hcq15 hcq0 hcq4)) (Or.inr (by exact astra4wPowerNat103_037 hApos hcq15 hcq0 hcq1))
  have hct1 := piQuarticChamberFace5810_coeff_top_S05 hAne hCne hDne (B := B) (E := E) (F := F) (G := G) (by exact astra4wPowerNat103_038 hcq0)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp1
  rw [degreeZeroPiQuartic810_eq_face5_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : piQuarticPowerInnerS05810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact quarticPowerInnerS05810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hCc hDc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
