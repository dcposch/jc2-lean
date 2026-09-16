import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
import Grok810ScaleZeroQuarticChamberDefs3Scratch
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
private theorem astra4wPowerNat114_000
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 4 * b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_001
    {a b d e f : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b + e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_002
    {a b d f : ℕ}
    (h0 : d < a + b)
    : d + f < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_003
    {a b d f g : ℕ}
    (h0 : a + 2 * f = 2 * g)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 2 * b < (a + b + f) ∧ b + d < (a + b + f) ∧ g < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_004
    {a b d e f : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b < (a + b + f) ∧ e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_005
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a + b < (a + b + f) ∧ d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_006
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_007
    {a b d f : ℕ}
    (h0 : b + f = 2 * d)
    : a + 2 * d = a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_008
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a + 4 * b < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_009
    {a b d e f : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    : a + 2 * b + e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_010
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * b + d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_011
    {a b d f g : ℕ}
    (h0 : a + 2 * f = 2 * g)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b + g < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_012
    {a b d e f : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + d + e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_013
    {a b d f : ℕ}
    (h0 : b + f = 2 * d)
    (h1 : d < a + b)
    : 2 * f < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_014
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a + b + d < (a + d + f) ∧ b + f < (a + d + f) ∧ 2 * d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_015
    {a b d f g : ℕ}
    (h0 : a + 2 * f = 2 * g)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 2 * b < (a + d + f) ∧ b + d < (a + d + f) ∧ g < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_016
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a + d < (a + d + f) ∧ f < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_017
    {a b d e f : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * b < (a + d + f) ∧ e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_018
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_019
    {a b d e f g : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + f = 2 * d)
    : e + g = a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_020
    {a b f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    : 2 * a + 4 * b < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_021
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : d < a + b)
    : a + 3 * b + d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_022
    {a b f g : ℕ}
    (h0 : a + 2 * f = 2 * g)
    (h1 : a + 4 * b < 2 * f)
    : a + 2 * b + g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_023
    {a b d e f : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 4 * b < 2 * f)
    : a + b + d + e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_024
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 3 * b + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_025
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : d < a + b)
    : 2 * b + 2 * d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_026
    {a b d f g : ℕ}
    (h0 : a + 2 * f = 2 * g)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : b + d + g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_027
    {a b d e f : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : b + e + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_028
    {a b d e f : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : 2 * d + e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_029
    {a b d e f : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * b < (a + 2 * f) ∧ a + 2 * d < (a + 2 * f) ∧ 2 * b + e < (a + 2 * f) ∧ d + f < (a + 2 * f) ∧ 2 * e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_030
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : a + b + d < (a + 2 * f) ∧ b + f < (a + 2 * f) ∧ 2 * d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_031
    {a b d e f : ℕ}
    (h0 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * b < (a + 2 * f) ∧ a + f < (a + 2 * f) ∧ b + e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_032
    {a b d f g : ℕ}
    (h0 : a + 2 * f = 2 * g)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : a + 2 * b < (a + 2 * f) ∧ b + d < (a + 2 * f) ∧ g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_033
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_034
    {a b f : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 4 * b < 2 * f)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_035
    {a b c d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : c = 0)
    (h3 : d < a + b)
    : ¬ (7 * a ≤ 4 * c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_036
    {a b d f : ℕ}
    (h0 : 9 * a ≤ 4 * d)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_037
    {a b d e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_038
    {a b d f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_039
    {a b d f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_040
    {a b d e f g : ℕ}
    (h0 : 4 * a + b < a + b + f)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ 2 * b + d < a + b + f ∧ b + g < a + b + f ∧ d + e < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_041
    {a b f : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 4 * b < 2 * f)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_042
    {a b c d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : c = 0)
    (h3 : d < a + b)
    : ¬ (5 * a ≤ 4 * c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_043
    {a b d f : ℕ}
    (h0 : 7 * a ≤ 4 * d)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_044
    {a b d e f : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_045
    {a b d f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_046
    {a b d f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_047
    {a b d e f : ℕ}
    (h0 : 3 * a + b < a + b + f)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_048
    {a b f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : a ≤ 4 * b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_049
    {a b c d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : b + f = 2 * d)
    (h2 : c = 0)
    (h3 : d < a + b)
    : ¬ (3 * a ≤ 4 * c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_050
    {a b d f : ℕ}
    (h0 : 5 * a ≤ 4 * d)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_051
    {a b d e f : ℕ}
    (h0 : 7 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_052
    {a b d f : ℕ}
    (h0 : 9 * a ≤ 4 * f)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_053
    {a b d f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_054
    {a b d f : ℕ}
    (h0 : 2 * a + b < a + b + f)
    (h1 : b + f = 2 * d)
    (h2 : d < a + b)
    : 2 * a + b < a + b + f ∧ a + d < a + b + f ∧ f < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_055
    {a b d f : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 4 * b < 2 * f)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_056
    {a b d f : ℕ}
    (h0 : 9 * a ≤ 4 * d)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_057
    {a b d e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_058
    {a b d f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_059
    {a b d f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_060
    {a b d e f g : ℕ}
    (h0 : 4 * a + d < a + d + f)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 4 * a + d < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + 2 * d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_061
    {a b d f : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 4 * b < 2 * f)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_062
    {a b d f : ℕ}
    (h0 : 7 * a ≤ 4 * d)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_063
    {a b d e f : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_064
    {a b d f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_065
    {a b d f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_066
    {a b d e f : ℕ}
    (h0 : 3 * a + d < a + d + f)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + d < a + d + f ∧ a + 3 * b < a + d + f ∧ 2 * a + f < a + d + f ∧ a + b + e < a + d + f ∧ 2 * b + d < a + d + f ∧ d + e < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_067
    {a b d f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : a ≤ 4 * b)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_068
    {a b d f : ℕ}
    (h0 : 5 * a ≤ 4 * d)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_069
    {a b d e f : ℕ}
    (h0 : 7 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_070
    {a b d f : ℕ}
    (h0 : 9 * a ≤ 4 * f)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_071
    {a b d f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_072
    {a b d e f : ℕ}
    (h0 : 2 * a + d < a + d + f)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + d < a + d + f ∧ 3 * b < a + d + f ∧ a + f < a + d + f ∧ b + e < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_073
    {a b f : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 4 * b < 2 * f)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_074
    {a b d f : ℕ}
    (h0 : 9 * a ≤ 4 * d)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_075
    {a b d e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_076
    {a b d f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_077
    {a b d f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_078
    {a b d e f g : ℕ}
    (h0 : 4 * a + f < a + 2 * f)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : b + f = 2 * d)
    (h5 : d < a + b)
    : 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_079
    {a b f : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 4 * b < 2 * f)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_080
    {a b d f : ℕ}
    (h0 : 7 * a ≤ 4 * d)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_081
    {a b d e f : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_082
    {a b d f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_083
    {a b d f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_084
    {a b d e f : ℕ}
    (h0 : 3 * a + f < a + 2 * f)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + b + e < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + d + e < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ e + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_085
    {a b f : ℕ}
    (h0 : a + 4 * b < 2 * f)
    (h1 : a ≤ 4 * b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_086
    {a b d f : ℕ}
    (h0 : 5 * a ≤ 4 * d)
    (h1 : a + 4 * b < 2 * f)
    (h2 : d < a + b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_087
    {a b d e f : ℕ}
    (h0 : 7 * a ≤ 4 * e)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_088
    {a b d f : ℕ}
    (h0 : 9 * a ≤ 4 * f)
    (h1 : a + 4 * b < 2 * f)
    (h2 : b + f = 2 * d)
    (h3 : d < a + b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_089
    {a b d f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_090
    {a b d e f : ℕ}
    (h0 : 2 * a + f < a + 2 * f)
    (h1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (h2 : a + 4 * b < 2 * f)
    (h3 : b + f = 2 * d)
    (h4 : d < a + b)
    : a + 3 * b < a + 2 * f ∧ 2 * a + f < a + 2 * f ∧ a + b + e < a + 2 * f ∧ 2 * b + d < a + 2 * f ∧ d + e < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_091
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 2 * b + d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_092
    {a b c f g : ℕ}
    (h0 : a + 2 * f = 2 * g)
    (h1 : c + g < a + b + f)
    : b + 2 * c < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_093
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : c + g < a + b + f)
    : c + f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_094
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    : d + e < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_095
    {a b c f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : c + g < a + b + f)
    : b + c < (a + 3 * b) ∧ f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_096
    {a b c d f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : c + g < a + b + f)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_097
    {a b c f g : ℕ}
    (h0 : a + 2 * f = 2 * g)
    (h1 : c + g < a + b + f)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_098
    {a b f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    : b + g = a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_099
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : a + 4 * b < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_100
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    : a + b + c + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_101
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * b + d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_102
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    (h4 : e + g < 2 * a + b + f)
    : 2 * b + 2 * c < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_103
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + b + f = 2 * e)
    : a + d + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_104
    {a b e f g : ℕ}
    (h0 : a + b + f = 2 * e)
    (h1 : e + g < 2 * a + b + f)
    : 2 * b + g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_105
    {a b c e f g : ℕ}
    (h0 : a + 2 * f = 2 * g)
    (h1 : a + b + f = 2 * e)
    (h2 : c + g < a + b + f)
    (h3 : e + g < 2 * a + b + f)
    : b + c + f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_106
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : b + d + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_107
    {a b c e f g : ℕ}
    (h0 : a + 2 * f = 2 * g)
    (h1 : c + g < a + b + f)
    : 2 * c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_108
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    (h4 : e + g < 2 * a + b + f)
    : c + 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_109
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 2 * f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_110
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : a + b + d < (a + 2 * b + e) ∧ 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_111
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_112
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : a + d < (a + 2 * b + e) ∧ b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_113
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    (h4 : e + g < 2 * a + b + f)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_114
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_115
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    : e + g = a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_116
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_117
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ e + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_118
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_119
    {a b e f g : ℕ}
    (h0 : 6 * a ≤ 2 * b + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_120
    {a b c e f g : ℕ}
    (h0 : 6 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : c + g < a + b + f)
    (h3 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_121
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 6 * a ≤ b + 2 * d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_122
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 6 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_123
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 6 * a ≤ 3 * b + c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_124
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a < a + 3 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_125
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_126
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ e + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_127
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_128
    {a b e f g : ℕ}
    (h0 : 5 * a ≤ 2 * b + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_129
    {a b c e f g : ℕ}
    (h0 : 5 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : c + g < a + b + f)
    (h3 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_130
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 5 * a ≤ b + 2 * d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_131
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_132
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a ≤ 3 * b + c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_133
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a < a + 3 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_134
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_135
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ e + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_136
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_137
    {a b e f g : ℕ}
    (h0 : 4 * a ≤ 2 * b + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_138
    {a b c e f g : ℕ}
    (h0 : 4 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : c + g < a + b + f)
    (h3 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_139
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_140
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_141
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_142
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_143
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ c + d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_144
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_145
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a < a + 3 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_146
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ d + g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_147
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ e + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_148
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_149
    {a b e f g : ℕ}
    (h0 : 3 * a ≤ 2 * b + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_150
    {a b c e f g : ℕ}
    (h0 : 3 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : c + g < a + b + f)
    (h3 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_151
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_152
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_153
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_154
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_155
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ c + d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_156
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : a ≤ b)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_157
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_158
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_159
    {a b c e f g : ℕ}
    (h0 : 2 * a < a + 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_160
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_161
    {a b e f g : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_162
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : a ≤ 2 * b + d)
    (h4 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_163
    {a b e f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_164
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : c + g < a + b + f)
    (h3 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_165
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_166
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_167
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_168
    {a b e f g : ℕ}
    (h0 : 2 * a ≤ b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_169
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_170
    {a b e f g : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_171
    {a b e f g : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_172
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_173
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_174
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 5 * a ≤ 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_175
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 7 * a ≤ 4 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_176
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_177
    {a b d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_178
    {a b d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_179
    {a b d e f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_180
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a + f < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : e + g < 2 * a + b + f)
    : 4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_181
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 3 * a ≤ 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_182
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 5 * a ≤ 4 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_183
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_184
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 9 * a ≤ 4 * e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_185
    {a b d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_186
    {a b d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_187
    {a b c d e f g : ℕ}
    (h0 : 2 * a + f < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_188
    {a b d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : a + b + f = 2 * e)
    (h2 : a ≤ 4 * b)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_189
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 3 * a ≤ 4 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_190
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_191
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 7 * a ≤ 4 * e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_192
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 9 * a ≤ 4 * f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_193
    {a b d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_194
    {a b c d e f g : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_195
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : f < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_196
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : d < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_197
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : b < (a + 3 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_198
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : a + b + d < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ 2 * d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_199
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : a + 2 * b < (a + 2 * b + e) ∧ b + d < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_200
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : a + d < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_201
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * b < (a + 2 * b + e) ∧ e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_202
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : d < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_203
    {a b c d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ b + c + e)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_204
    {a b c d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ 2 * c + d)
    (h3 : a + b + f = 2 * e)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_205
    {a b c d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ 3 * b + c)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_206
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a < a + 3 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_207
    {a b c d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ b + c + e)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_208
    {a b c d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ 2 * c + d)
    (h3 : a + b + f = 2 * e)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_209
    {a b c d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ 3 * b + c)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_210
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a < a + 3 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_211
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ b + c + e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_212
    {a b c d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ 2 * c + d)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_213
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a ≤ 3 * b + c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_214
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ c + d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c < 2 * a)
    (h6 : c = 0)
    (h7 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_215
    {a b e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a < a + 3 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_216
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c + e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_217
    {a b c d e f : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ 2 * c + d)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : d < a + b)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_218
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 3 * b + c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_219
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ c + d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c < 2 * a)
    (h6 : c = 0)
    (h7 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_220
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ b + c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_221
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_222
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c = 0)
    (h6 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_223
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_224
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * d < b + f)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c = 0)
    (h6 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_225
    {a b c e f g : ℕ}
    (h0 : 2 * a ≤ b + c)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c < 2 * a)
    (h5 : c = 0)
    (h6 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_226
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : e + g < 2 * a + b + f)
    : ¬ (7 * a ≤ 4 * c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_227
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a + f < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : e + g < 2 * a + b + f)
    : 4 * a + d < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_228
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 3 * a ≤ 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_229
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : e + g < 2 * a + b + f)
    : ¬ (5 * a ≤ 4 * c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_230
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_231
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 9 * a ≤ 4 * e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_232
    {a b d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_233
    {a b d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * d < b + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + d < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_234
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + d < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + d < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_235
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c = 0)
    (h5 : e + g < 2 * a + b + f)
    : ¬ (3 * a ≤ 4 * c) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_236
    {a b d e f g : ℕ}
    (h0 : 2 * a + d < a + 2 * b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + d < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_237
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    (h4 : e + g < 2 * a + b + f)
    : 2 * b + c < (a + 2 * b + e) ∧ b + f < (a + 2 * b + e) ∧ c + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_238
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    (h4 : e + g < 2 * a + b + f)
    : a + b + c < (a + 2 * b + e) ∧ 3 * b < (a + 2 * b + e) ∧ a + f < (a + 2 * b + e) ∧ b + e < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_239
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    : a + 2 * b < (a + 2 * b + e) ∧ 2 * c < (a + 2 * b + e) ∧ g < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_240
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    (h4 : e + g < 2 * a + b + f)
    : b + c < (a + 2 * b + e) ∧ f < (a + 2 * b + e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_241
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 6 * a ≤ d + g)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_242
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ 2 * b + d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_243
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
private theorem astra4wPowerNat114_244
    {a b c d e f g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 6 * a ≤ 2 * c + d)
    (h4 : a + 2 * f = 2 * g)
    (h5 : a + b + f = 2 * e)
    (h6 : c + g < a + b + f)
    (h7 : d = 0)
    : 5 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_245
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 5 * a < a + 3 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_246
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ d + g)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_247
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ 2 * b + d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_248
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 5 * a ≤ b + 2 * d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_249
    {a b c d e f g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 5 * a ≤ 2 * c + d)
    (h4 : a + 2 * f = 2 * g)
    (h5 : a + b + f = 2 * e)
    (h6 : c + g < a + b + f)
    (h7 : d = 0)
    : 4 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_250
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 4 * a < a + 3 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_251
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ d + g)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_252
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ 2 * b + d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_253
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ b + 2 * d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_254
    {a b c d e f g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : 4 * a ≤ 2 * c + d)
    (h4 : a + 2 * f = 2 * g)
    (h5 : a + b + f = 2 * e)
    (h6 : c + g < a + b + f)
    (h7 : d = 0)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_255
    {a b c d e f g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 4 * a ≤ c + d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    (h7 : e + g < 2 * a + b + f)
    : 3 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_256
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ d + g)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : d = 0)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_257
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : d = 0)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_258
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ b + 2 * d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_259
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : d = 0)
    (h6 : e + g < 2 * a + b + f)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_260
    {a b c d e f g : ℕ}
    (h0 : 2 * e < 3 * a + 2 * b)
    (h1 : 2 * f = a + 4 * b)
    (h2 : 3 * a ≤ c + d)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : 2 * a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_261
    {a b d e f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : d = 0)
    (h5 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_262
    {a b d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : a ≤ 2 * b + d)
    (h4 : d = 0)
    (h5 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_263
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ b + 2 * d)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_264
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : d = 0)
    (h6 : e + g < 2 * a + b + f)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_265
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_266
    {a b c d e f g : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * e < 3 * a + 2 * b)
    (h2 : 2 * f = a + 4 * b)
    (h3 : a + 2 * f = 2 * g)
    (h4 : a + b + f = 2 * e)
    (h5 : c + g < a + b + f)
    (h6 : d = 0)
    : a < a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_267
    {a b e f g : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_268
    {a b c e f g : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_269
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    (h4 : d = 0)
    (h5 : e + g < 2 * a + b + f)
    : ¬ (9 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_270
    {a b e f g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_271
    {a b e f g : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_272
    {a b e f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_273
    {a b c e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : 3 * a + f < a + 2 * b + e)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_274
    {a b e f g : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_275
    {a b c e f g : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_276
    {a b c d e f g : ℕ}
    (h0 : 2 * f = a + 4 * b)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : c + g < a + b + f)
    (h4 : d = 0)
    (h5 : e + g < 2 * a + b + f)
    : ¬ (7 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_277
    {a b e f g : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_278
    {a b e f g : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_279
    {a b e f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + b + f = 2 * e)
    (h3 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_280
    {a b c e f g : ℕ}
    (h0 : 2 * a + f < a + 2 * b + e)
    (h1 : 2 * f = a + 4 * b)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + b + f = 2 * e)
    (h4 : c + g < a + b + f)
    (h5 : e + g < 2 * a + b + f)
    : 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_281
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    : a + 3 * b < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_282
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * b + d < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_283
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    : b + 2 * c < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_284
    {a b d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * e < a + b + f)
    (h2 : a + 2 * f = 2 * g)
    : d + e < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_285
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : b + c < (b + g) ∧ f < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_286
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : d < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_287
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : b < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_288
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    : a < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_289
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    : c + f = b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_290
    {a b c f : ℕ}
    (h0 : b + c < f)
    : a + 2 * b + c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_291
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : 4 * b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_292
    {a b d f : ℕ}
    (h0 : 2 * d < b + f)
    : a + 2 * d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_293
    {a b c e f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 2 * b + e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_294
    {a b c d f : ℕ}
    (h0 : b + c < f)
    (h1 : d < a + b)
    : b + c + d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_295
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    : 3 * c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_296
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    (h4 : f < 2 * a + b)
    : a + 2 * b < (a + b + f) ∧ b + d < (a + b + f) ∧ 2 * c < (a + b + f) ∧ g < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_297
    {a b c e f : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 2 * b < (a + b + f) ∧ e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_298
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d < a + b)
    (h3 : f < 2 * a + b)
    : a + b < (a + b + f) ∧ d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_299
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_300
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_301
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    : 2 * a + 4 * b < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_302
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d < a + b)
    : a + 3 * b + d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_303
    {a b c f : ℕ}
    (h0 : b + c < f)
    : a + 2 * b + 2 * c < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_304
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : 4 * b + c < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_305
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    : a + 2 * b + g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_306
    {a b c f : ℕ}
    (h0 : b + c < f)
    : a + b + c + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_307
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * e < a + b + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + c < f)
    : a + b + d + e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_308
    {a b c d f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : b + c < f)
    : a + c + 2 * d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_309
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : 3 * b + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_310
    {a b c e f : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 2 * b + c + e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_311
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d < a + b)
    : 2 * b + 2 * d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_312
    {a b c d f : ℕ}
    (h0 : b + c < f)
    (h1 : d < a + b)
    : b + 2 * c + d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_313
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    : 4 * c < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_314
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : b + d + g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_315
    {a b c e f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : b + e + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_316
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    : 2 * c + g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_317
    {a b c d f : ℕ}
    (h0 : b + c < f)
    (h1 : d < a + b)
    : c + d + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_318
    {a b c e f : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : b + c < f)
    : c + 2 * e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_319
    {a b c d e f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * e < a + b + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * d + e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_320
    {a b c d e f g : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : 2 * e < a + b + f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + 2 * f = 2 * g)
    (h4 : b + c < f)
    (h5 : d < a + b)
    (h6 : e + g < 2 * a + b + f)
    (h7 : f < 2 * a + b)
    : a + 2 * b + c < (a + 2 * f) ∧ 4 * b < (a + 2 * f) ∧ a + 2 * d < (a + 2 * f) ∧ 2 * b + e < (a + 2 * f) ∧ b + c + d < (a + 2 * f) ∧ 3 * c < (a + 2 * f) ∧ d + f < (a + 2 * f) ∧ 2 * e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_321
    {a b c d e f : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    (h4 : f < 2 * a + b)
    : a + b + d < (a + 2 * f) ∧ 2 * b + c < (a + 2 * f) ∧ b + f < (a + 2 * f) ∧ c + e < (a + 2 * f) ∧ 2 * d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_322
    {a b c d e f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : a + b + c < (a + 2 * f) ∧ 3 * b < (a + 2 * f) ∧ a + f < (a + 2 * f) ∧ b + e < (a + 2 * f) ∧ c + d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_323
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    (h4 : f < 2 * a + b)
    : a + 2 * b < (a + 2 * f) ∧ b + d < (a + 2 * f) ∧ 2 * c < (a + 2 * f) ∧ g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_324
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : b + c < (a + 2 * f) ∧ f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_325
    {a b d g : ℕ}
    (h0 : 6 * a ≤ d + g)
    (h1 : d < a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_326
    {a b e f g : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : 6 * a ≤ e + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_327
    {a b c d f g : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_328
    {a b c f g : ℕ}
    (h0 : 6 * a ≤ 2 * b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_329
    {a b c e f g : ℕ}
    (h0 : 6 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_330
    {a b c d f g : ℕ}
    (h0 : 6 * a ≤ b + 2 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_331
    {a b c d f g : ℕ}
    (h0 : 6 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_332
    {a b c f g : ℕ}
    (h0 : 6 * a ≤ 3 * b + c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_333
    {a b c d e f g : ℕ}
    (h0 : 5 * a < b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : e + g < 2 * a + b + f)
    (h6 : f < 2 * a + b)
    : 5 * a < b + g ∧ 3 * a + c < b + g ∧ 2 * a + 2 * b < b + g ∧ 2 * a + e < b + g ∧ a + b + d < b + g ∧ a + 2 * c < b + g ∧ 2 * b + c < b + g ∧ a + g < b + g ∧ b + f < b + g ∧ c + e < b + g ∧ 2 * d < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_334
    {a b d g : ℕ}
    (h0 : 5 * a ≤ d + g)
    (h1 : d < a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_335
    {a b e f g : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : 5 * a ≤ e + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_336
    {a b c d f g : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_337
    {a b c f g : ℕ}
    (h0 : 5 * a ≤ 2 * b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_338
    {a b c e f g : ℕ}
    (h0 : 5 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_339
    {a b c d f g : ℕ}
    (h0 : 5 * a ≤ b + 2 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_340
    {a b c d f g : ℕ}
    (h0 : 5 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_341
    {a b c f g : ℕ}
    (h0 : 5 * a ≤ 3 * b + c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_342
    {a b c d e f g : ℕ}
    (h0 : 4 * a < b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : e + g < 2 * a + b + f)
    (h6 : f < 2 * a + b)
    : 4 * a < b + g ∧ 2 * a + c < b + g ∧ a + 2 * b < b + g ∧ a + e < b + g ∧ b + d < b + g ∧ 2 * c < b + g ∧ g < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_343
    {a b d g : ℕ}
    (h0 : 4 * a ≤ d + g)
    (h1 : d < a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_344
    {a b e f g : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : 4 * a ≤ e + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_345
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_346
    {a b c f g : ℕ}
    (h0 : 4 * a ≤ 2 * b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_347
    {a b c e f g : ℕ}
    (h0 : 4 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_348
    {a b c d f g : ℕ}
    (h0 : 4 * a ≤ b + 2 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_349
    {a b c d f g : ℕ}
    (h0 : 4 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_350
    {a b c f g : ℕ}
    (h0 : 4 * a ≤ 3 * b + c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_351
    {a b c e f g : ℕ}
    (h0 : 4 * a ≤ b + e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_352
    {a b c d f g : ℕ}
    (h0 : 4 * a ≤ c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_353
    {a b c f g : ℕ}
    (h0 : 4 * a ≤ 3 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_354
    {a b c e f g : ℕ}
    (h0 : 3 * a < b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 3 * a < b + g ∧ a + c < b + g ∧ 2 * b < b + g ∧ e < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_355
    {a b d g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : d < a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_356
    {a b e f g : ℕ}
    (h0 : 3 * a ≤ e + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : e + g < 2 * a + b + f)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_357
    {a b c d f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_358
    {a b c f g : ℕ}
    (h0 : 3 * a ≤ 2 * b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_359
    {a b c e f g : ℕ}
    (h0 : 3 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_360
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ b + 2 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_361
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_362
    {a b c f g : ℕ}
    (h0 : 3 * a ≤ 3 * b + c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_363
    {a b c e f g : ℕ}
    (h0 : 3 * a ≤ b + e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_364
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_365
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a ≤ b)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_366
    {a b c f g : ℕ}
    (h0 : 3 * a ≤ f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_367
    {a b c f g : ℕ}
    (h0 : 3 * a ≤ b + c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_368
    {a b c f g : ℕ}
    (h0 : 2 * a < b + g)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : 2 * a < b + g ∧ c < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_369
    {a b c f : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_370
    {a b c f : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_371
    {a b c d f : ℕ}
    (h0 : 9 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_372
    {a b c e f g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_373
    {a b c f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_374
    {a b c f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_375
    {a b c d e f g : ℕ}
    (h0 : 4 * a + b < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : e + g < 2 * a + b + f)
    (h6 : f < 2 * a + b)
    : 4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_376
    {a b c f : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_377
    {a b c f : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_378
    {a b c d f : ℕ}
    (h0 : 7 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_379
    {a b c e f g : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_380
    {a b c f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_381
    {a b c f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_382
    {a b c d e f g : ℕ}
    (h0 : 3 * a + b < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : e + g < 2 * a + b + f)
    (h6 : f < 2 * a + b)
    : 3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f ∧ c + d < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_383
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a ≤ 4 * b)
    (h2 : b + c < f)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_384
    {a b c f : ℕ}
    (h0 : 3 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_385
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_386
    {a b c e f g : ℕ}
    (h0 : 7 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_387
    {a b c f : ℕ}
    (h0 : 9 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_388
    {a b c f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_389
    {a b c d f : ℕ}
    (h0 : 2 * a + b < a + b + f)
    (h1 : b + c < f)
    (h2 : d < a + b)
    (h3 : f < 2 * a + b)
    : 2 * a + b < a + b + f ∧ a + d < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_390
    {a b c f : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_391
    {a b c f : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_392
    {a b c d f : ℕ}
    (h0 : 9 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_393
    {a b c e f g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_394
    {a b c f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_395
    {a b c f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_396
    {a b c d e f g : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : 4 * a + f < a + 2 * f)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + 2 * f = 2 * g)
    (h4 : b + c < f)
    (h5 : d < a + b)
    (h6 : e + g < 2 * a + b + f)
    (h7 : f < 2 * a + b)
    : 4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_397
    {a b c f : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_398
    {a b c f : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_399
    {a b c d f : ℕ}
    (h0 : 7 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_400
    {a b c e f g : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_401
    {a b c f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_402
    {a b c f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_403
    {a b c d e f g : ℕ}
    (h0 : 3 * a + f < a + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : e + g < 2 * a + b + f)
    (h6 : f < 2 * a + b)
    : 3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + b + e < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ a + d + e < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + c + e < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f ∧ e + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_404
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a ≤ 4 * b)
    (h2 : b + c < f)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_405
    {a b c f : ℕ}
    (h0 : 3 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_406
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_407
    {a b c e f g : ℕ}
    (h0 : 7 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_408
    {a b c f : ℕ}
    (h0 : 9 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_409
    {a b c f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat114_410
    {a b c d e f g : ℕ}
    (h0 : 2 * a + f < a + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : e + g < 2 * a + b + f)
    (h6 : f < 2 * a + b)
    : 2 * a + b + c < a + 2 * f ∧ a + 3 * b < a + 2 * f ∧ 2 * a + f < a + 2 * f ∧ a + b + e < a + 2 * f ∧ a + c + d < a + 2 * f ∧ 2 * b + d < a + 2 * f ∧ b + 2 * c < a + 2 * f ∧ c + f < a + 2 * f ∧ d + e < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `BCDEFG` / `BF·BG·CF·CG` dies on power system `S16` (carriers κ, μ, π). -/
theorem quarticChamberBCDEFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG6810 A B C D E F G)
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq3 hcq5 hcq7 hcq10 hcq13 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_325 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_326 hcq7 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_327 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_328 h hcq1 hcq0 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_329 h hcq0 hcq14 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_330 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_331 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_332 h hcq1 hcq0 hcq14 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_333 h hcq1 hcq0 hcq14 hcq5 hcq9 hcq10)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_334 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_335 hcq7 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_336 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_337 h hcq1 hcq0 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_338 h hcq0 hcq14 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_339 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_340 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_341 h hcq1 hcq0 hcq14 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_342 h hcq1 hcq0 hcq14 hcq5 hcq9 hcq10)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_343 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_344 hcq7 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_345 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_346 h hcq1 hcq0 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_347 h hcq0 hcq14 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_348 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_349 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_350 h hcq1 hcq0 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_351 h hcq1 hcq0 hcq14 hcq9 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_352 h hcq1 hcq0 hcq14 hcq5 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_353 h hcq1 hcq0 hcq14 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_354 h hcq1 hcq0 hcq14 hcq9 hcq10)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_355 h hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_356 h hcq0 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_357 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_358 h hcq1 hcq0 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_359 h hcq0 hcq14 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_360 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_361 h hcq1 hcq0 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_362 h hcq1 hcq0 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_363 h hcq1 hcq0 hcq14 hcq9 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_364 h hcq1 hcq0 hcq14 hcq5 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_365 hcq1 hcq0 h hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_366 h hcq1 hcq0 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_367 h hcq1 hcq0 hcq14 hcq10)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_368 h hcq14 hcq10)
  have hr0 : (kappaQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest16810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat114_281 hcq1 hcq0 hcq14) (by exact astra4wPowerNat114_282 hcq1 hcq0 hcq14 hcq5) (by exact astra4wPowerNat114_283 hcq1 hcq0 hcq14) (by exact astra4wPowerNat114_284 hcq3 hcq7 hcq0) hz0l hz0beta (Or.inr (by exact astra4wPowerNat114_285 hcq1 hcq0 hcq14 hcq10)) hz0delta (Or.inr (by exact astra4wPowerNat114_286 hcq1 hcq0 hcq14 hcq5)) hz0zeta (Or.inr (by exact astra4wPowerNat114_287 hcq1 hcq0 hcq14 hcq10)) (Or.inr (by exact astra4wPowerNat114_288 hcq1 hcq0 hcq14))
  have hct0 := kappaQuarticChamberFace16810_coeff_top_S16 hBne hCne hFne hGne (A := A) (D := D) (E := E) (by exact astra4wPowerNat114_289 hcq1 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + G.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face16_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS16810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_369 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_370 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_371 h hcq1 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_372 h hcq1 hcq0 hcq14 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_373 h hcq1 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_374 h hcq1 hcq0 hcq14 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_375 h hcq1 hcq0 hcq14 hcq5 hcq9 hcq10)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_376 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_377 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_378 h hcq1 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_379 h hcq1 hcq0 hcq14 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_380 h hcq1 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_381 h hcq1 hcq0 hcq14 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_382 h hcq1 hcq0 hcq14 hcq5 hcq9 hcq10)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_383 hcq1 h hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_384 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_385 h hcq1 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_386 h hcq1 hcq0 hcq14 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_387 h hcq1 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_388 h hcq1 hcq0 hcq14 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_389 h hcq14 hcq5 hcq10)
  have hr1 : (muQuarticChamberRest20810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest20810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat114_290 hcq14) (by exact astra4wPowerNat114_291 hcq1 hcq14 hcq10) (by exact astra4wPowerNat114_292 hcq3) (by exact astra4wPowerNat114_293 hcq1 hcq0 hcq14 hcq9) (by exact astra4wPowerNat114_294 hcq14 hcq5) (by exact astra4wPowerNat114_295 hcq1 hcq14) (by exact astra4wPowerNat114_002 hcq5) (by exact hcq7) hz1l hz1beta (Or.inr (by exact astra4wPowerNat114_296 hcq1 hcq0 hcq14 hcq5 hcq10)) hz1delta (Or.inr (by exact astra4wPowerNat114_297 hcq7 hcq1 hcq14 hcq10)) (Or.inr (by exact astra4wPowerNat114_298 hcq1 hcq14 hcq5 hcq10)) (Or.inr (by exact astra4wPowerNat114_299 hcq1 hcq14 hcq10)) (Or.inr (by exact astra4wPowerNat114_300 hcq1 hcq14 hcq10))
  have hct1 := muQuarticChamberFace20810_coeff_top_S16 hAne hBne hCne hFne hGne (D := D) (E := E) (by exact hcq2.symm)
  have hq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp1
  rw [degreeZeroMuQuartic810_eq_face20_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : muQuarticPowerInnerS16810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_390 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_391 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_392 h hcq1 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_393 h hcq1 hcq0 hcq14 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_394 h hcq1 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_395 h hcq1 hcq0 hcq14 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_396 hcq7 h hcq1 hcq0 hcq14 hcq5 hcq9 hcq10)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_397 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_398 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_399 h hcq1 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_400 h hcq1 hcq0 hcq14 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_401 h hcq1 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_402 h hcq1 hcq0 hcq14 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_403 h hcq1 hcq0 hcq14 hcq5 hcq9 hcq10)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_404 hcq1 h hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_405 h hcq1 hcq14)
      · exact Or.inr (by exact astra4wPowerNat114_406 h hcq1 hcq14 hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_407 h hcq1 hcq0 hcq14 hcq9)
      · exact Or.inr (by exact astra4wPowerNat114_408 h hcq1 hcq14 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_409 h hcq1 hcq0 hcq14 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_410 h hcq1 hcq0 hcq14 hcq5 hcq9 hcq10)
  have hr2 : (piQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest14810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by exact astra4wPowerNat114_301 hcq1 hcq14) (by exact astra4wPowerNat114_302 hcq1 hcq14 hcq5) (by exact astra4wPowerNat114_303 hcq14) (by exact astra4wPowerNat114_304 hcq1 hcq14 hcq10) (by exact astra4wPowerNat114_305 hcq1 hcq0 hcq14) (by exact astra4wPowerNat114_306 hcq14) (by exact astra4wPowerNat114_307 hcq3 hcq7 hcq1 hcq14) (by exact astra4wPowerNat114_308 hcq3 hcq14) (by exact astra4wPowerNat114_309 hcq1 hcq14 hcq10) (by exact astra4wPowerNat114_310 hcq7 hcq1 hcq14 hcq10) (by exact astra4wPowerNat114_311 hcq1 hcq14 hcq5) (by exact astra4wPowerNat114_312 hcq14 hcq5) (by exact astra4wPowerNat114_313 hcq1 hcq14) (by exact astra4wPowerNat114_314 hcq1 hcq0 hcq14 hcq5) (by exact astra4wPowerNat114_315 hcq1 hcq0 hcq14 hcq9) (by exact astra4wPowerNat114_316 hcq1 hcq0 hcq14) (by exact astra4wPowerNat114_317 hcq14 hcq5) (by exact astra4wPowerNat114_318 hcq7 hcq14) (by exact astra4wPowerNat114_319 hcq3 hcq7 hcq1 hcq14 hcq5) hz2l hz2beta (Or.inr (by exact astra4wPowerNat114_320 hcq3 hcq7 hcq1 hcq0 hcq14 hcq5 hcq9 hcq10)) hz2delta (Or.inr (by exact astra4wPowerNat114_321 hcq7 hcq1 hcq14 hcq5 hcq10)) (Or.inr (by exact astra4wPowerNat114_322 hcq1 hcq0 hcq14 hcq5 hcq9 hcq10)) (Or.inr (by exact astra4wPowerNat114_323 hcq1 hcq0 hcq14 hcq5 hcq10)) (Or.inr (by exact astra4wPowerNat114_324 hcq1 hcq14 hcq10))
  have hct2 := piQuarticChamberFace14810_coeff_top_S16 hAne hFne hGne (B := B) (C := C) (D := D) (E := E) (by exact hcq0.symm)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticPowerInnerS16810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS16810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hAc hBc hCc hFc hGc


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
/-- Chamber `BCEFG` / `BF·BG·EE·BBB` dies on power system `S18` (carriers κ, ξ). -/
theorem quarticChamberBCEFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG13810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat114_241 hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_117 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_242 hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_119 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_120 h hcq0 hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_243 hAD hcq5 hcq2 h hcq1 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_244 hAD hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_123 hcq2 h hcq0 hcq1 hcq4 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_245 hcq2 h hcq0 hcq1 hcq4 hcq6)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_246 hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_126 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_247 hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_128 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_129 h hcq0 hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_248 hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_249 hAD hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_132 hcq2 h hcq0 hcq1 hcq4 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_250 hcq2 h hcq0 hcq1 hcq4 hcq6)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_251 hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_135 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_252 hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_137 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_138 h hcq0 hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_253 hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_254 hAD hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_141 hcq2 h hcq0 hcq1 hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_142 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_255 hAD hcq2 h hcq0 hcq1 hcq4 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_144 hcq2 h hcq0 hcq1 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_145 hcq2 h hcq0 hcq1 hcq4 hcq6)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_256 hcq2 h hcq0 hcq1 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_147 hcq2 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_257 h hcq2 hcq0 hcq1 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_149 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_150 h hcq0 hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_258 hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_259 hcq2 h hcq0 hcq1 hcq4 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_153 hcq2 h hcq0 hcq1 hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_154 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_260 hcq5 hcq2 h hcq0 hcq1 hcq4 hDn)
      · exact Or.inr (by exact astra4wPowerNat114_156 hcq2 hcq0 hcq1 h hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_157 hcq2 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_158 hcq2 h hcq0 hcq1 hcq4 hcq6)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_159 h hcq2 hcq0 hcq1 hcq4 hcq6)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_261 h hcq2 hcq0 hcq1 hDn hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_161 h hcq2 hcq0 hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_262 hcq2 hcq0 hcq1 h hDn hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_163 h hcq0 hcq1 hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_164 h hcq0 hcq4 hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_263 h hcq5 hcq2 hcq0 hcq1 hcq4 hDn)
    · exact Or.inr (by exact astra4wPowerNat114_264 h hcq2 hcq0 hcq1 hcq4 hDn hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_167 h hcq2 hcq0 hcq1 hcq4 hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_168 h hcq2 hcq0 hcq1 hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_265 h hcq5 hcq2 hcq0 hcq1 hcq4 hDn)
    · exact Or.inr (by exact astra4wPowerNat114_170 h hcq2 hcq0 hcq1 hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_171 h hcq0 hcq1 hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_172 h hcq2 hcq0 hcq1 hcq4 hcq6)
    · exact Or.inr (by exact astra4wPowerNat114_266 h hcq5 hcq2 hcq0 hcq1 hcq4 hDn)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by exact astra4wPowerNat114_092 hcq0 hcq4) (by exact astra4wPowerNat114_093 hcq2 hcq0 hcq4) hz0l hz0beta (Or.inr (by exact astra4wPowerNat114_095 hcq2 hcq0 hcq4)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat114_097 hcq0 hcq4)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top_S18 hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by exact astra4wPowerNat114_098 hcq2 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS18810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_267 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_268 h hcq0 hcq1 hcq4 hcq6)
      · exact absurd h (by exact astra4wPowerNat114_269 hcq2 hcq0 hcq1 hcq4 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_270 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_271 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_272 h hcq0 hcq1 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_273 hcq2 h hcq0 hcq1 hcq4 hcq6)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_274 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_275 h hcq0 hcq1 hcq4 hcq6)
      · exact absurd h (by exact astra4wPowerNat114_276 hcq2 hcq0 hcq1 hcq4 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_277 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_278 h hcq0 hcq1 hcq6)
      · exact Or.inr (by exact astra4wPowerNat114_279 h hcq0 hcq1 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_280 h hcq2 hcq0 hcq1 hcq4 hcq6)
  have hr1 : (xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest19810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by exact astra4wPowerNat114_099 hcq2 hcq0 hcq1 hcq6) (by exact astra4wPowerNat114_102 hcq2 hcq0 hcq1 hcq4 hcq6) (by exact astra4wPowerNat114_104 hcq1 hcq6) (by exact astra4wPowerNat114_105 hcq0 hcq1 hcq4 hcq6) (by exact astra4wPowerNat114_107 hcq0 hcq4) (by exact astra4wPowerNat114_109 hcq2 hcq0 hcq1 hcq6) hz1l hz1beta (Or.inr (by exact astra4wPowerNat114_237 hcq2 hcq0 hcq1 hcq4 hcq6)) (Or.inr (by exact astra4wPowerNat114_238 hcq2 hcq0 hcq1 hcq4 hcq6)) (Or.inr (by exact astra4wPowerNat114_239 hcq2 hcq0 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat114_240 hcq2 hcq0 hcq1 hcq4 hcq6)) (Or.inr (by exact astra4wPowerNat114_113 hcq2 hcq0 hcq1 hcq4 hcq6))
  have hct1 := xiQuarticChamberFace19810_coeff_top_S18 hAne hBne hEne hGne (C := C) (D := D) (F := F) (by exact astra4wPowerNat114_115 hcq2 hcq0)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS18810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS18810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hEc hGc


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
/-- Chamber `BDEFG` / `BF·BG·EE·BBB` dies on power system `S18` (carriers κ, ξ). -/
theorem quarticChamberBDEFG12810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG12810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
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
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * D.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_116 hcq3 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_117 hcq2 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_118 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_119 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_203 hcq7 hcq2 h hcq1 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_121 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_204 hcq7 hcq2 h hcq1 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_205 hcq7 hcq2 h hcq1 hCn hcq5)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_206 hcq3 hcq2 h hcq0 hcq1 hcq8)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_125 hcq3 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_126 hcq2 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_127 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_128 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_207 hcq7 hcq2 h hcq1 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_130 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_208 hcq7 hcq2 h hcq1 hAC hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_209 hcq7 hcq2 h hcq1 hCn hcq5)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_210 hcq3 hcq2 h hcq0 hcq1 hcq8)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_134 hcq3 hcq2 h hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_135 hcq2 h hcq0 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_136 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_137 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_211 hcq2 h hcq0 hcq1 hCn hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_139 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_212 hcq7 hcq2 h hcq1 hCn hcq5)
      · exact Or.inr (by exact astra4wPowerNat114_213 hcq2 h hcq0 hcq1 hCn hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_142 hcq2 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_214 hcq3 hcq2 h hcq0 hcq1 hAC hCn hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_144 hcq2 h hcq0 hcq1 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_215 hcq2 h hcq0 hcq1 hcq8)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_146 hcq3 hcq2 h hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_147 hcq2 h hcq0 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_148 h hcq3 hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_149 h hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_216 hcq2 h hcq0 hcq1 hCn hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_151 hcq3 h hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_217 hcq7 hcq2 h hcq1 hCn hcq5)
    · exact Or.inr (by exact astra4wPowerNat114_218 hcq2 h hcq0 hcq1 hCn hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_154 hcq2 h hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_219 hcq3 hcq2 h hcq0 hcq1 hAC hCn hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_156 hcq2 hcq0 hcq1 h hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_157 hcq2 h hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_220 hcq2 h hcq0 hcq1 hAC hCn hcq8)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_160 h hcq3 hcq2 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_161 h hcq2 hcq0 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_162 hcq3 hcq0 hcq1 h hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_163 h hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_221 h hcq2 hcq0 hcq1 hCn hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_165 h hcq3 hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_222 h hcq3 hcq2 hcq0 hcq1 hCn hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_223 h hcq2 hcq0 hcq1 hCn hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_168 h hcq2 hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_224 h hcq3 hcq2 hcq0 hcq1 hCn hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_170 h hcq2 hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_171 h hcq0 hcq1 hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_225 h hcq2 hcq0 hcq1 hAC hCn hcq8)
    · exact Or.inr (by exact astra4wPowerNat114_173 h hcq3 hcq2 hcq0 hcq1 hcq8)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz (by exact astra4wPowerNat114_091 hcq3 hcq0 hcq1 hcq8) (by exact astra4wPowerNat114_094 hcq3 hcq2 hcq1) hz0l hz0beta (Or.inr (by exact astra4wPowerNat114_195 hcq3 hcq2 hcq0 hcq1 hcq8)) hz0delta (Or.inr (by exact astra4wPowerNat114_196 hcq3 hcq2 hcq0 hcq1 hcq8)) hz0zeta (Or.inr (by exact astra4wPowerNat114_197 hcq3 hcq2 hcq0 hcq1 hcq8)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top_S18 hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by exact astra4wPowerNat114_098 hcq2 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS18810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_174 hcq3 h hcq0 hcq1 hcq8)
      · exact absurd h (by exact astra4wPowerNat114_226 hcq3 hcq2 hcq0 hcq1 hCn hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_176 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_177 h hcq3 hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_178 h hcq3 hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_179 h hcq3 hcq0 hcq1 hcq8)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_227 hcq3 hcq2 h hcq0 hcq1 hcq8)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_228 hcq3 h hcq0 hcq1 hcq8)
      · exact absurd h (by exact astra4wPowerNat114_229 hcq3 hcq2 hcq0 hcq1 hCn hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_230 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_231 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_232 h hcq3 hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_233 h hcq3 hcq0 hcq1 hcq8)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_234 hcq2 h hcq0 hcq1 hcq8)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_188 hcq3 hcq1 h)
      · exact absurd h (by exact astra4wPowerNat114_235 hcq3 hcq2 hcq0 hcq1 hCn hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_190 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_191 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_192 hcq3 h hcq0 hcq1 hcq8)
      · exact Or.inr (by exact astra4wPowerNat114_193 h hcq3 hcq0 hcq1 hcq8)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_236 h hcq2 hcq0 hcq1 hcq8)
  have hr1 : (xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest19810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz (by exact astra4wPowerNat114_099 hcq2 hcq0 hcq1 hcq8) (by exact astra4wPowerNat114_101 hcq3 hcq2 hcq0 hcq1 hcq8) (by exact astra4wPowerNat114_103 hcq3 hcq2 hcq1) (by exact astra4wPowerNat114_104 hcq1 hcq8) (by exact astra4wPowerNat114_106 hcq3 hcq0 hcq1 hcq8) (by exact astra4wPowerNat114_109 hcq2 hcq0 hcq1 hcq8) hz1l hz1beta (Or.inr (by exact astra4wPowerNat114_198 hcq3 hcq2 hcq0 hcq1 hcq8)) hz1delta (Or.inr (by exact astra4wPowerNat114_199 hcq3 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat114_200 hcq3 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat114_201 hcq3 hcq2 hcq0 hcq1 hcq8)) (Or.inr (by exact astra4wPowerNat114_202 hcq3 hcq2 hcq0 hcq1 hcq8))
  have hct1 := xiQuarticChamberFace19810_coeff_top_S18 hAne hBne hEne hGne (C := C) (D := D) (F := F) (by exact astra4wPowerNat114_115 hcq2 hcq0)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS18810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS18810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hEc hGc


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
/-- Chamber `BCDEFG` / `BF·BG·EE·BBB` dies on power system `S18` (carriers κ, ξ). -/
theorem quarticChamberBCDEFG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG25810 A B C D E F G)
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
      · exact Or.inr (by exact astra4wPowerNat114_116 hcq5 hcq2 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_117 hcq2 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_118 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_119 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_120 h hcq0 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_121 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_122 hcq5 h hcq0 hcq1 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_123 hcq2 h hcq0 hcq1 hcq4 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_124 hcq5 hcq2 h hcq0 hcq1 hcq4 hcq10)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + D.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * C.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_125 hcq5 hcq2 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_126 hcq2 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_127 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_128 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_129 h hcq0 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_130 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_131 hcq5 h hcq0 hcq1 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_132 hcq2 h hcq0 hcq1 hcq4 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_133 hcq5 hcq2 h hcq0 hcq1 hcq4 hcq10)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ E.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_134 hcq5 hcq2 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_135 hcq2 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_136 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_137 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_138 h hcq0 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_139 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_140 hcq5 h hcq0 hcq1 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_141 hcq2 h hcq0 hcq1 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_142 hcq2 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_143 hcq5 hcq2 h hcq0 hcq1 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_144 hcq2 h hcq0 hcq1 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_145 hcq2 h hcq0 hcq1 hcq4 hcq10)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ C.natDegree < A.natDegree + 3 * B.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_146 hcq5 hcq2 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_147 hcq2 h hcq0 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_148 h hcq5 hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_149 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_150 h hcq0 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_151 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_152 hcq5 h hcq0 hcq1 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_153 hcq2 h hcq0 hcq1 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_154 hcq2 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_155 hcq5 hcq2 h hcq0 hcq1 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_156 hcq2 hcq0 hcq1 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_157 hcq2 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_158 hcq2 h hcq0 hcq1 hcq4 hcq10)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_159 h hcq2 hcq0 hcq1 hcq4 hcq10)
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_160 h hcq5 hcq2 hcq1 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_161 h hcq2 hcq0 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_162 hcq5 hcq0 hcq1 h hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_163 h hcq0 hcq1 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_164 h hcq0 hcq4 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_165 h hcq5 hcq0 hcq1 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_166 h hcq5 hcq0 hcq1 hcq4 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_167 h hcq2 hcq0 hcq1 hcq4 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_168 h hcq2 hcq0 hcq1 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_169 h hcq5 hcq2 hcq0 hcq1 hcq4 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_170 h hcq2 hcq0 hcq1 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_171 h hcq0 hcq1 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_172 h hcq2 hcq0 hcq1 hcq4 hcq10)
    · exact Or.inr (by exact astra4wPowerNat114_173 h hcq5 hcq2 hcq0 hcq1 hcq10)
  have hr0 : (kappaQuarticChamberRest7810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest7810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat114_091 hcq5 hcq0 hcq1 hcq10) (by exact astra4wPowerNat114_092 hcq0 hcq4) (by exact astra4wPowerNat114_093 hcq2 hcq0 hcq4) (by exact astra4wPowerNat114_094 hcq5 hcq2 hcq1) hz0l hz0beta (Or.inr (by exact astra4wPowerNat114_095 hcq2 hcq0 hcq4)) hz0delta (Or.inr (by exact astra4wPowerNat114_096 hcq5 hcq2 hcq0 hcq4)) hz0zeta (Or.inr (by exact astra4wPowerNat114_097 hcq0 hcq4)) hz0theta
  have hct0 := kappaQuarticChamberFace7810_coeff_top_S18 hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by exact astra4wPowerNat114_098 hcq2 hcq0)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    exact hdp0
  rw [degreeZeroKappaQuartic810_eq_face7_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : kappaQuarticPowerInnerS18810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + 2 * B.natDegree + E.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 4 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_174 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_175 hcq5 h hcq0 hcq1 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_176 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_177 h hcq5 hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_178 h hcq5 hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_179 h hcq5 hcq0 hcq1 hcq10)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_180 hcq5 hcq2 h hcq0 hcq1 hcq4 hcq10)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_181 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_182 hcq5 h hcq0 hcq1 hcq4 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_183 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_184 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_185 h hcq5 hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_186 h hcq5 hcq0 hcq1 hcq10)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_187 h hcq2 hcq0 hcq1 hcq4 hcq10)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * B.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_188 hcq5 hcq1 h)
      · exact Or.inr (by exact astra4wPowerNat114_189 hcq5 h hcq0 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_190 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_191 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_192 hcq5 h hcq0 hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat114_193 h hcq5 hcq0 hcq1 hcq10)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_194 h hcq2 hcq0 hcq1 hcq4 hcq10)
  have hr1 : (xiQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * B.natDegree + E.natDegree :=
    xiQuarticChamberRest19810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat114_099 hcq2 hcq0 hcq1 hcq10) (by exact astra4wPowerNat114_100 hcq5 hcq0 hcq1 hcq4) (by exact astra4wPowerNat114_101 hcq5 hcq2 hcq0 hcq1 hcq10) (by exact astra4wPowerNat114_102 hcq2 hcq0 hcq1 hcq4 hcq10) (by exact astra4wPowerNat114_103 hcq5 hcq2 hcq1) (by exact astra4wPowerNat114_104 hcq1 hcq10) (by exact astra4wPowerNat114_105 hcq0 hcq1 hcq4 hcq10) (by exact astra4wPowerNat114_106 hcq5 hcq0 hcq1 hcq10) (by exact astra4wPowerNat114_107 hcq0 hcq4) (by exact astra4wPowerNat114_108 hcq5 hcq0 hcq1 hcq4 hcq10) (by exact astra4wPowerNat114_109 hcq2 hcq0 hcq1 hcq10) hz1l hz1beta (Or.inr (by exact astra4wPowerNat114_110 hcq5 hcq2 hcq0 hcq1 hcq4 hcq10)) hz1delta (Or.inr (by exact astra4wPowerNat114_111 hcq5 hcq2 hcq0 hcq1 hcq4 hcq10)) (Or.inr (by exact astra4wPowerNat114_112 hcq5 hcq2 hcq0 hcq1 hcq4 hcq10)) (Or.inr (by exact astra4wPowerNat114_113 hcq2 hcq0 hcq1 hcq4 hcq10)) (Or.inr (by exact astra4wPowerNat114_114 hcq5 hcq2 hcq0 hcq1 hcq4 hcq10))
  have hct1 := xiQuarticChamberFace19810_coeff_top_S18 hAne hBne hEne hGne (C := C) (D := D) (F := F) (by exact astra4wPowerNat114_115 hcq2 hcq0)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS18810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS18810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hAc hBc hEc hGc


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
/-- Chamber `BDEFG` / `BF·BG·DD·DE·EE` dies on power system `S20` (carriers μ, ξ, π). -/
theorem quarticChamberBDEFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < A.natDegree + B.natDegree + F.natDegree := by
    clear * - hApos; omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_034 h hcq11)
      · exact absurd h (by exact astra4wPowerNat114_035 hcq11 hcq1 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_036 h hcq11 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_037 h hcq2 hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_038 h hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_039 h hcq0 hcq11 hcq1 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_040 h hcq2 hcq0 hcq11 hcq1 hcq4)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_041 h hcq11)
      · exact absurd h (by exact astra4wPowerNat114_042 hcq11 hcq1 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_043 h hcq11 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_044 h hcq2 hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_045 h hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_046 h hcq0 hcq11 hcq1 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_047 h hcq2 hcq11 hcq1 hcq4)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_048 hcq11 h)
      · exact absurd h (by exact astra4wPowerNat114_049 hcq11 hcq1 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_050 h hcq11 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_051 h hcq2 hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_052 h hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_053 h hcq0 hcq11 hcq1 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_054 h hcq1 hcq4)
  have hr0 : (muQuarticChamberRest17810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest17810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hCz (by exact astra4wPowerNat114_000 hcq11 hcq1 hcq4) (by exact astra4wPowerNat114_001 hcq2 hcq11 hcq1 hcq4) (by exact astra4wPowerNat114_002 hcq4) hz0l hz0beta (Or.inr (by exact astra4wPowerNat114_003 hcq0 hcq11 hcq1 hcq4)) hz0delta (Or.inr (by exact astra4wPowerNat114_004 hcq2 hcq11 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat114_005 hcq11 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat114_006 hcq11 hcq1 hcq4))
  have hct0 := muQuarticChamberFace17810_coeff_top_S20 hAne hBne hDne hEne hFne (C := C) (G := G) (by exact astra4wPowerNat114_007 hcq1) (by exact hcq3.symm)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    exact hdp0
  rw [degreeZeroMuQuartic810_eq_face17_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : muQuarticPowerInnerS20810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + D.natDegree + F.natDegree := by
    clear * - hApos; omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_055 h hcq11)
      · exact absurd h (by exact astra4wPowerNat114_035 hcq11 hcq1 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_056 h hcq11 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_057 h hcq2 hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_058 h hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_059 h hcq0 hcq11 hcq1 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_060 h hcq2 hcq0 hcq11 hcq1 hcq4)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_061 h hcq11)
      · exact absurd h (by exact astra4wPowerNat114_042 hcq11 hcq1 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_062 h hcq11 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_063 h hcq2 hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_064 h hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_065 h hcq0 hcq11 hcq1 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_066 h hcq2 hcq11 hcq1 hcq4)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_067 hcq11 h)
      · exact absurd h (by exact astra4wPowerNat114_049 hcq11 hcq1 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_068 h hcq11 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_069 h hcq2 hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_070 h hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_071 h hcq0 hcq11 hcq1 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_072 h hcq2 hcq11 hcq1 hcq4)
  have hr1 : (xiQuarticChamberRest22810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest22810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hCz (by exact astra4wPowerNat114_008 hcq11 hcq1 hcq4) (by exact astra4wPowerNat114_009 hcq2 hcq11 hcq1) (by exact astra4wPowerNat114_010 hcq11 hcq1 hcq4) (by exact astra4wPowerNat114_011 hcq0 hcq11 hcq1 hcq4) (by exact astra4wPowerNat114_012 hcq2 hcq11 hcq1 hcq4) (by exact astra4wPowerNat114_013 hcq1 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat114_014 hcq11 hcq1 hcq4)) hz1delta (Or.inr (by exact astra4wPowerNat114_015 hcq0 hcq11 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat114_016 hcq11 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat114_017 hcq2 hcq11 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat114_018 hcq11 hcq1 hcq4))
  have hct1 := xiQuarticChamberFace22810_coeff_top_S20 hAne hDne hEne hFne hGne (B := B) (C := C) (by exact astra4wPowerNat114_019 hcq2 hcq0 hcq1)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    exact hdp1
  rw [degreeZeroXiQuartic810_eq_face22_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : xiQuarticPowerInnerS20810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < A.natDegree + 2 * F.natDegree := by
    clear * - hApos; omega
  have hz2l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_073 h hcq11)
      · exact absurd h (by exact astra4wPowerNat114_035 hcq11 hcq1 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_074 h hcq11 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_075 h hcq2 hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_076 h hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_077 h hcq0 hcq11 hcq1 hcq4)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_078 h hcq2 hcq0 hcq11 hcq1 hcq4)
  have hz2beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_079 h hcq11)
      · exact absurd h (by exact astra4wPowerNat114_042 hcq11 hcq1 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_080 h hcq11 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_081 h hcq2 hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_082 h hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_083 h hcq0 hcq11 hcq1 hcq4)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_084 h hcq2 hcq11 hcq1 hcq4)
  have hz2delta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat114_085 hcq11 h)
      · exact absurd h (by exact astra4wPowerNat114_049 hcq11 hcq1 hCn hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_086 h hcq11 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_087 h hcq2 hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_088 h hcq11 hcq1 hcq4)
      · exact Or.inr (by exact astra4wPowerNat114_089 h hcq0 hcq11 hcq1 hcq4)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat114_090 h hcq2 hcq11 hcq1 hcq4)
  have hr2 : (piQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest14810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hCz (by exact astra4wPowerNat114_020 hcq11) (by exact astra4wPowerNat114_021 hcq11 hcq4) (by exact astra4wPowerNat114_022 hcq0 hcq11) (by exact astra4wPowerNat114_023 hcq2 hcq11) (by exact astra4wPowerNat114_024 hcq11 hcq1 hcq4) (by exact astra4wPowerNat114_025 hcq11 hcq4) (by exact astra4wPowerNat114_026 hcq0 hcq11 hcq4) (by exact astra4wPowerNat114_027 hcq2 hcq11 hcq1 hcq4) (by exact astra4wPowerNat114_028 hcq2 hcq11 hcq4) hz2l hz2beta (Or.inr (by exact astra4wPowerNat114_029 hcq2 hcq11 hcq1 hcq4)) hz2delta (Or.inr (by exact astra4wPowerNat114_030 hcq11 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat114_031 hcq2 hcq11 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat114_032 hcq0 hcq11 hcq1 hcq4)) (Or.inr (by exact astra4wPowerNat114_033 hcq11 hcq1 hcq4))
  have hct2 := piQuarticChamberFace14810_coeff_top_S20 hAne hFne hGne (B := B) (C := C) (D := D) (E := E) (by exact hcq0.symm)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * F.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    exact hdp2
  rw [degreeZeroPiQuartic810_eq_face14_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : piQuarticPowerInnerS20810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS20810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hAc hBc hDc hEc hFc hGc


end QuarticChamberPowerKills810

end Max11DegreeRoutes
