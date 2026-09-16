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
private theorem astra4wPowerNat113_000
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    : a + 3 * b < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_001
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    : b + 2 * c < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_002
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : b + c < (b + g) ∧ f < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_003
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : b < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_004
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    : a < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_005
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    : c + f = b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_006
    {a b c f : ℕ}
    (h0 : b + c < f)
    : a + 2 * b + c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_007
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : 4 * b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_008
    {a b c e f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 2 * b + e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_009
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    : 3 * c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_010
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : a + 2 * b < (a + b + f) ∧ 2 * c < (a + b + f) ∧ g < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_011
    {a b c e f : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 2 * b < (a + b + f) ∧ e < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_012
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : a + b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_013
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : c < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_014
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_015
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    : 2 * a + 4 * b < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_016
    {a b c f : ℕ}
    (h0 : b + c < f)
    : a + 2 * b + 2 * c < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_017
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : 4 * b + c < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_018
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    : a + 2 * b + g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_019
    {a b c f : ℕ}
    (h0 : b + c < f)
    : a + b + c + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_020
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : 3 * b + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_021
    {a b c e f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 2 * b + c + e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_022
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    : 4 * c < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_023
    {a b c e f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : b + e + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_024
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    : 2 * c + g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_025
    {a b c e f : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : b + c < f)
    : c + 2 * e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_026
    {a b c e f g : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : a + 2 * b + c < (a + 2 * f) ∧ 4 * b < (a + 2 * f) ∧ 2 * b + e < (a + 2 * f) ∧ 3 * c < (a + 2 * f) ∧ 2 * e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_027
    {a b c e f : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 2 * b + c < (a + 2 * f) ∧ b + f < (a + 2 * f) ∧ c + e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_028
    {a b c e f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    (h4 : f < 2 * a + b)
    : a + b + c < (a + 2 * f) ∧ 3 * b < (a + 2 * f) ∧ a + f < (a + 2 * f) ∧ b + e < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_029
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : a + 2 * b < (a + 2 * f) ∧ 2 * c < (a + 2 * f) ∧ g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_030
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : b + c < (a + 2 * f) ∧ f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_031
    {a b d f g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 6 * a ≤ d + g)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : d = 0)
    (h5 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_032
    {a b e f g : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : 6 * a ≤ e + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_033
    {a b d e f g : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d = 0)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_034
    {a b c f g : ℕ}
    (h0 : 6 * a ≤ 2 * b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_035
    {a b c e f g : ℕ}
    (h0 : 6 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_036
    {a b d f g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 6 * a ≤ b + 2 * d)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : d = 0)
    (h5 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_037
    {a b c d e f g : ℕ}
    (h0 : 6 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : d = 0)
    (h5 : e + g < 2 * a + b + f)
    (h6 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_038
    {a b c f g : ℕ}
    (h0 : 6 * a ≤ 3 * b + c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_039
    {a b c e f g : ℕ}
    (h0 : 5 * a < b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 5 * a < b + g ∧ 3 * a + c < b + g ∧ 2 * a + 2 * b < b + g ∧ 2 * a + e < b + g ∧ a + 2 * c < b + g ∧ 2 * b + c < b + g ∧ a + g < b + g ∧ b + f < b + g ∧ c + e < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_040
    {a b d e f g : ℕ}
    (h0 : 5 * a ≤ d + g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d = 0)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_041
    {a b e f g : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : 5 * a ≤ e + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_042
    {a b d e f g : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d = 0)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_043
    {a b c f g : ℕ}
    (h0 : 5 * a ≤ 2 * b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_044
    {a b c e f g : ℕ}
    (h0 : 5 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_045
    {a b d e f g : ℕ}
    (h0 : 5 * a ≤ b + 2 * d)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d = 0)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_046
    {a b c d e f g : ℕ}
    (h0 : 5 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : d = 0)
    (h5 : e + g < 2 * a + b + f)
    (h6 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_047
    {a b c f g : ℕ}
    (h0 : 5 * a ≤ 3 * b + c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_048
    {a b c e f g : ℕ}
    (h0 : 4 * a < b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 4 * a < b + g ∧ 2 * a + c < b + g ∧ a + 2 * b < b + g ∧ a + e < b + g ∧ 2 * c < b + g ∧ g < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_049
    {a b d e f g : ℕ}
    (h0 : 4 * a ≤ d + g)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d = 0)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_050
    {a b e f g : ℕ}
    (h0 : 2 * e < a + b + f)
    (h1 : 4 * a ≤ e + f)
    (h2 : a + 2 * f = 2 * g)
    (h3 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_051
    {a b d e f g : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d = 0)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_052
    {a b c f g : ℕ}
    (h0 : 4 * a ≤ 2 * b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_053
    {a b c e f g : ℕ}
    (h0 : 4 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_054
    {a b d e f g : ℕ}
    (h0 : 4 * a ≤ b + 2 * d)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d = 0)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_055
    {a b c d e f g : ℕ}
    (h0 : 4 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : d = 0)
    (h5 : e + g < 2 * a + b + f)
    (h6 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_056
    {a b c f g : ℕ}
    (h0 : 4 * a ≤ 3 * b + c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_057
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
private theorem astra4wPowerNat113_058
    {a b c d f g : ℕ}
    (h0 : 2 * d < 5 * a)
    (h1 : 4 * a ≤ c + d)
    (h2 : a + 2 * b = 2 * c)
    (h3 : a + 2 * f = 2 * g)
    (h4 : b + c < f)
    (h5 : d = 0)
    (h6 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_059
    {a b c f g : ℕ}
    (h0 : 4 * a ≤ 3 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_060
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
private theorem astra4wPowerNat113_061
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d = 0)
    (h5 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_062
    {a b e f g : ℕ}
    (h0 : 3 * a ≤ e + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : e + g < 2 * a + b + f)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_063
    {a b c d f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d = 0)
    (h5 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_064
    {a b c f g : ℕ}
    (h0 : 3 * a ≤ 2 * b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_065
    {a b c e f g : ℕ}
    (h0 : 3 * a ≤ b + c + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : e + g < 2 * a + b + f)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_066
    {a b d e f g : ℕ}
    (h0 : 3 * a ≤ b + 2 * d)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d = 0)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_067
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d = 0)
    (h5 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_068
    {a b c f g : ℕ}
    (h0 : 3 * a ≤ 3 * b + c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_069
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
private theorem astra4wPowerNat113_070
    {a b c d e f g : ℕ}
    (h0 : 3 * a ≤ c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : d = 0)
    (h5 : e + g < 2 * a + b + f)
    (h6 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_071
    {a b c f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a ≤ b)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_072
    {a b c f g : ℕ}
    (h0 : 3 * a ≤ f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_073
    {a b c f g : ℕ}
    (h0 : 3 * a ≤ b + c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_074
    {a b c f g : ℕ}
    (h0 : 2 * a < b + g)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : 2 * a < b + g ∧ c < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_075
    {a b c f : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_076
    {a b c f : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_077
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    : ¬ (9 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_078
    {a b c e f g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_079
    {a b c f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_080
    {a b c f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_081
    {a b c e f g : ℕ}
    (h0 : 4 * a + b < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_082
    {a b c f : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_083
    {a b c f : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_084
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    : ¬ (7 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_085
    {a b c e f g : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_086
    {a b c f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_087
    {a b c f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_088
    {a b c e f g : ℕ}
    (h0 : 3 * a + b < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_089
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a ≤ 4 * b)
    (h2 : b + c < f)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_090
    {a b c f : ℕ}
    (h0 : 3 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_091
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d = 0)
    (h3 : f < 2 * a + b)
    : ¬ (5 * a ≤ 4 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_092
    {a b c e f g : ℕ}
    (h0 : 7 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_093
    {a b c f : ℕ}
    (h0 : 9 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_094
    {a b c f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_095
    {a b c f : ℕ}
    (h0 : 2 * a + b < a + b + f)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : 2 * a + b < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_096
    {a b c f : ℕ}
    (h0 : 5 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_097
    {a b c f : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_098
    {a b c e f g : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_099
    {a b c f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_100
    {a b c f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_101
    {a b c e f g : ℕ}
    (h0 : 4 * a + f < a + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ f + g < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_102
    {a b c f : ℕ}
    (h0 : 3 * a ≤ 4 * b)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_103
    {a b c f : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_104
    {a b c e f g : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_105
    {a b c f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_106
    {a b c f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_107
    {a b c e f g : ℕ}
    (h0 : 3 * a + f < a + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + b + e < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + c + e < a + 2 * f ∧ e + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_108
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a ≤ 4 * b)
    (h2 : b + c < f)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_109
    {a b c f : ℕ}
    (h0 : 3 * a ≤ 4 * c)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_110
    {a b c e f g : ℕ}
    (h0 : 7 * a ≤ 4 * e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_111
    {a b c f : ℕ}
    (h0 : 9 * a ≤ 4 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_112
    {a b c f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : f < 2 * a + b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_113
    {a b c e f g : ℕ}
    (h0 : 2 * a + f < a + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e + g < 2 * a + b + f)
    (h5 : f < 2 * a + b)
    : 2 * a + b + c < a + 2 * f ∧ a + 3 * b < a + 2 * f ∧ 2 * a + f < a + 2 * f ∧ a + b + e < a + 2 * f ∧ b + 2 * c < a + 2 * f ∧ c + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_114
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * b + d < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_115
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : d < (b + g) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_116
    {a b d f : ℕ}
    (h0 : 2 * d < b + f)
    : a + 2 * d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_117
    {a b c d f : ℕ}
    (h0 : b + c < f)
    (h1 : d < a + b)
    : b + c + d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_118
    {a b d f : ℕ}
    (h0 : d < a + b)
    : d + f < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_119
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    (h4 : f < 2 * a + b)
    : a + 2 * b < (a + b + f) ∧ b + d < (a + b + f) ∧ 2 * c < (a + b + f) ∧ g < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_120
    {a b c f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : f < 2 * a + b)
    : 2 * b < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_121
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d < a + b)
    (h3 : f < 2 * a + b)
    : a + b < (a + b + f) ∧ d < (a + b + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_122
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d < a + b)
    : a + 3 * b + d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_123
    {a b c d f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : b + c < f)
    : a + c + 2 * d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_124
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d < a + b)
    : 2 * b + 2 * d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_125
    {a b c d f : ℕ}
    (h0 : b + c < f)
    (h1 : d < a + b)
    : b + 2 * c + d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_126
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : b + d + g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_127
    {a b c d f : ℕ}
    (h0 : b + c < f)
    (h1 : d < a + b)
    : c + d + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_128
    {a b c d f : ℕ}
    (h0 : 2 * d < b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    (h4 : f < 2 * a + b)
    : a + 2 * b + c < (a + 2 * f) ∧ 4 * b < (a + 2 * f) ∧ a + 2 * d < (a + 2 * f) ∧ b + c + d < (a + 2 * f) ∧ 3 * c < (a + 2 * f) ∧ d + f < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_129
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d < a + b)
    (h3 : f < 2 * a + b)
    : a + b + d < (a + 2 * f) ∧ 2 * b + c < (a + 2 * f) ∧ b + f < (a + 2 * f) ∧ 2 * d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_130
    {a b c d f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : d < a + b)
    (h3 : f < 2 * a + b)
    : a + b + c < (a + 2 * f) ∧ 3 * b < (a + 2 * f) ∧ a + f < (a + 2 * f) ∧ c + d < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_131
    {a b c d f g : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : a + 2 * f = 2 * g)
    (h2 : b + c < f)
    (h3 : d < a + b)
    (h4 : f < 2 * a + b)
    : a + 2 * b < (a + 2 * f) ∧ b + d < (a + 2 * f) ∧ 2 * c < (a + 2 * f) ∧ g < (a + 2 * f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_132
    {a b d g : ℕ}
    (h0 : 6 * a ≤ d + g)
    (h1 : d < a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_133
    {a b e f g : ℕ}
    (h0 : 6 * a ≤ e + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : e < 3 * a)
    (h4 : e = 0)
    (h5 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_134
    {a b c d f g : ℕ}
    (h0 : 5 * a ≤ 2 * b + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_135
    {a b c d e f g : ℕ}
    (h0 : 6 * a ≤ b + c + e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : d < a + b)
    (h5 : e = 0)
    (h6 : f < 2 * a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_136
    {a b c d f g : ℕ}
    (h0 : 6 * a ≤ b + 2 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_137
    {a b c d f g : ℕ}
    (h0 : 6 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 5 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_138
    {a b c d f g : ℕ}
    (h0 : 5 * a < b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : f < 2 * a + b)
    : 5 * a < b + g ∧ 3 * a + c < b + g ∧ 2 * a + 2 * b < b + g ∧ a + b + d < b + g ∧ a + 2 * c < b + g ∧ 2 * b + c < b + g ∧ a + g < b + g ∧ b + f < b + g ∧ 2 * d < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_139
    {a b d g : ℕ}
    (h0 : 5 * a ≤ d + g)
    (h1 : d < a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_140
    {a b d e f g : ℕ}
    (h0 : 5 * a ≤ e + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_141
    {a b c d f g : ℕ}
    (h0 : 4 * a ≤ 2 * b + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_142
    {a b c d e f g : ℕ}
    (h0 : 5 * a ≤ b + c + e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : d < a + b)
    (h5 : e = 0)
    (h6 : f < 2 * a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_143
    {a b c d f g : ℕ}
    (h0 : 5 * a ≤ b + 2 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_144
    {a b c d f g : ℕ}
    (h0 : 5 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 4 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_145
    {a b c d f g : ℕ}
    (h0 : 4 * a < b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : f < 2 * a + b)
    : 4 * a < b + g ∧ 2 * a + c < b + g ∧ a + 2 * b < b + g ∧ b + d < b + g ∧ 2 * c < b + g ∧ g < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_146
    {a b d g : ℕ}
    (h0 : 4 * a ≤ d + g)
    (h1 : d < a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_147
    {a b d e f g : ℕ}
    (h0 : 4 * a ≤ e + f)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_148
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ 2 * b + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_149
    {a b c d e f g : ℕ}
    (h0 : 4 * a ≤ b + c + e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : a + 4 * b < 2 * f)
    (h4 : d < a + b)
    (h5 : e = 0)
    (h6 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_150
    {a b c d f g : ℕ}
    (h0 : 4 * a ≤ b + 2 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_151
    {a b c d f g : ℕ}
    (h0 : 4 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_152
    {a b c e f g : ℕ}
    (h0 : 4 * a ≤ b + e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e < 3 * a)
    (h5 : e = 0)
    (h6 : f < 2 * a + b)
    : 3 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_153
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
private theorem astra4wPowerNat113_154
    {a b c f g : ℕ}
    (h0 : 3 * a < b + g)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : f < 2 * a + b)
    : 3 * a < b + g ∧ a + c < b + g ∧ 2 * b < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_155
    {a b d g : ℕ}
    (h0 : 3 * a ≤ d + g)
    (h1 : d < a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_156
    {a b c e f g : ℕ}
    (h0 : 3 * a ≤ e + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e = 0)
    (h5 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_157
    {a b c d f g : ℕ}
    (h0 : 2 * a ≤ 2 * b + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_158
    {a b c e f g : ℕ}
    (h0 : 3 * a ≤ b + c + e)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : e = 0)
    (h5 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_159
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ b + 2 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_160
    {a b c d f g : ℕ}
    (h0 : 3 * a ≤ 2 * c + d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_161
    {a b d e f g : ℕ}
    (h0 : 3 * a ≤ b + e)
    (h1 : a + 2 * f = 2 * g)
    (h2 : a + 4 * b < 2 * f)
    (h3 : d < a + b)
    (h4 : e = 0)
    (h5 : f < 2 * a + b)
    : 2 * a < b + g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_162
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
private theorem astra4wPowerNat113_163
    {a b c d f : ℕ}
    (h0 : 9 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 4 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_164
    {a b c e f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : e = 0)
    (h3 : f < 2 * a + b)
    : ¬ (11 * a ≤ 4 * e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_165
    {a b c d f g : ℕ}
    (h0 : 4 * a + b < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : f < 2 * a + b)
    : 4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_166
    {a b c d f : ℕ}
    (h0 : 7 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 3 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_167
    {a b c e f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : e = 0)
    (h3 : f < 2 * a + b)
    : ¬ (9 * a ≤ 4 * e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_168
    {a b c d f : ℕ}
    (h0 : 3 * a + b < a + b + f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    (h4 : f < 2 * a + b)
    : 3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_169
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * a + b < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_170
    {a b c e f : ℕ}
    (h0 : a + 2 * b = 2 * c)
    (h1 : b + c < f)
    (h2 : e = 0)
    (h3 : f < 2 * a + b)
    : ¬ (7 * a ≤ 4 * e) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_171
    {a b c d f : ℕ}
    (h0 : 2 * a + b < a + b + f)
    (h1 : b + c < f)
    (h2 : d < a + b)
    (h3 : f < 2 * a + b)
    : 2 * a + b < a + b + f ∧ a + d < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_172
    {a b c d f : ℕ}
    (h0 : 9 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 4 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_173
    {a b c d f g : ℕ}
    (h0 : 4 * a + f < a + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : a + 2 * f = 2 * g)
    (h3 : b + c < f)
    (h4 : d < a + b)
    (h5 : f < 2 * a + b)
    : 4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_174
    {a b c d f : ℕ}
    (h0 : 7 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 3 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_175
    {a b c d f : ℕ}
    (h0 : 3 * a + f < a + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    (h4 : f < 2 * a + b)
    : 3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_176
    {a b c d f : ℕ}
    (h0 : 5 * a ≤ 4 * d)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    : 2 * a + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_177
    {a b c d f : ℕ}
    (h0 : 2 * a + f < a + 2 * f)
    (h1 : a + 2 * b = 2 * c)
    (h2 : b + c < f)
    (h3 : d < a + b)
    (h4 : f < 2 * a + b)
    : 2 * a + b + c < a + 2 * f ∧ a + 3 * b < a + 2 * f ∧ 2 * a + f < a + 2 * f ∧ a + c + d < a + 2 * f ∧ 2 * b + d < a + 2 * f ∧ b + 2 * c < a + 2 * f ∧ c + f < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_178
    {a b c f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    : a + 3 * b < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_179
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * b + d < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_180
    {b c f : ℕ}
    (h0 : b + c < f)
    : b + 2 * c < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_181
    {a b c f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : b + g < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_182
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : b + c < (c + f) ∧ f < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_183
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : d < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_184
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : b < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_185
    {a b c f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    : a < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_186
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : a + 2 * b + c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_187
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 4 * b < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_188
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : a + b + f < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_189
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : e < a + c)
    : 2 * b + e < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_190
    {a b c d e f : ℕ}
    (h0 : b + c < f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : b + c + d < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_191
    {a c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    : c + g < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_192
    {a c d e f : ℕ}
    (h0 : c + f = d + e)
    (h1 : e < a + c)
    : d + f < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_193
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : a + 2 * b < (a + 2 * d) ∧ b + d < (a + 2 * d) ∧ 2 * c < (a + 2 * d) ∧ g < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_194
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * b < (a + 2 * d) ∧ e < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_195
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + b < (a + 2 * d) ∧ d < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_196
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_197
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : b < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_198
    {a c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    : 3 * c = a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_199
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : c + f = d + e)
    : 2 * e = a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_200
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + 4 * b < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_201
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    : a + 2 * b + e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_202
    {a b c d f : ℕ}
    (h0 : b + c < f)
    : a + b + c + d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_203
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * b + d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_204
    {a b c d e f : ℕ}
    (h0 : b + c < f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 2 * b + 2 * c < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_205
    {a b c d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * b + g < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_206
    {a b c d e f : ℕ}
    (h0 : b + c < f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : b + c + f < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_207
    {a b c d e f : ℕ}
    (h0 : b + c < f)
    (h1 : e < a + c)
    : b + d + e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_208
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : c + 2 * d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_209
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : c + f = d + e)
    : e + g < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_210
    {a c d e f : ℕ}
    (h0 : c + f = d + e)
    (h1 : e < a + c)
    : 2 * f < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_211
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + b + d < (a + d + f) ∧ 2 * b + c < (a + d + f) ∧ b + f < (a + d + f) ∧ c + e < (a + d + f) ∧ 2 * d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_212
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : a + 2 * b < (a + d + f) ∧ b + d < (a + d + f) ∧ 2 * c < (a + d + f) ∧ g < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_213
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + d < (a + d + f) ∧ b + c < (a + d + f) ∧ f < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_214
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * b < (a + d + f) ∧ e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_215
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_216
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    : 2 * c + e = a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_217
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : 2 * a + 4 * b < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_218
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + 3 * b + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_219
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : a + 2 * b + 2 * c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_220
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 4 * b + c < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_221
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    : a + 2 * b + g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_222
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    : a + b + c + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_223
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    : a + b + d + e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_224
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 3 * b + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_225
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : e < a + c)
    : 2 * b + c + e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_226
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * b + 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_227
    {a b c d e f : ℕ}
    (h0 : b + c < f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : b + 2 * c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_228
    {a b c d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : b + d + g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_229
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : e < a + c)
    : b + e + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_230
    {a c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    : 2 * c + g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_231
    {a c d e f : ℕ}
    (h0 : c + f = d + e)
    (h1 : e < a + c)
    : c + d + f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_232
    {a c d e : ℕ}
    (h0 : e < a + c)
    : 2 * d + e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_233
    {a c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : a + 2 * f = 4 * c)
    : 2 * g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_234
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + 2 * b + c < (a + c + 2 * d) ∧ 4 * b < (a + c + 2 * d) ∧ a + 2 * d < (a + c + 2 * d) ∧ 2 * b + e < (a + c + 2 * d) ∧ b + c + d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ d + f < (a + c + 2 * d) ∧ 2 * e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_235
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + b + d < (a + c + 2 * d) ∧ 2 * b + c < (a + c + 2 * d) ∧ b + f < (a + c + 2 * d) ∧ c + e < (a + c + 2 * d) ∧ 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_236
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + b + c < (a + c + 2 * d) ∧ 3 * b < (a + c + 2 * d) ∧ a + f < (a + c + 2 * d) ∧ b + e < (a + c + 2 * d) ∧ c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_237
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : a + 2 * b < (a + c + 2 * d) ∧ b + d < (a + c + 2 * d) ∧ 2 * c < (a + c + 2 * d) ∧ g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_238
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : b + c < (a + c + 2 * d) ∧ f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_239
    {a c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    : 4 * c = a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_240
    {a c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    : a + 2 * f = a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_241
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : c + f = d + e)
    : c + 2 * e = a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_242
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 6 * a ≤ d + g)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_243
    {a c e f : ℕ}
    (h0 : 6 * a ≤ e + f)
    (h1 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_244
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
private theorem astra4wPowerNat113_245
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
private theorem astra4wPowerNat113_246
    {a b c e f : ℕ}
    (h0 : 6 * a ≤ b + c + e)
    (h1 : b + c < f)
    (h2 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_247
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 6 * a ≤ b + 2 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_248
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 6 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 5 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_249
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
private theorem astra4wPowerNat113_250
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a < c + f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b + c < f)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 5 * a < c + f ∧ 3 * a + c < c + f ∧ 2 * a + 2 * b < c + f ∧ 2 * a + e < c + f ∧ a + b + d < c + f ∧ a + 2 * c < c + f ∧ 2 * b + c < c + f ∧ a + g < c + f ∧ b + f < c + f ∧ c + e < c + f ∧ 2 * d < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_251
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a ≤ d + g)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_252
    {a c e f : ℕ}
    (h0 : 5 * a ≤ e + f)
    (h1 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_253
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
private theorem astra4wPowerNat113_254
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
private theorem astra4wPowerNat113_255
    {a b c e f : ℕ}
    (h0 : 5 * a ≤ b + c + e)
    (h1 : b + c < f)
    (h2 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_256
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ b + 2 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_257
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_258
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
private theorem astra4wPowerNat113_259
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a < c + f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b + c < f)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 4 * a < c + f ∧ 2 * a + c < c + f ∧ a + 2 * b < c + f ∧ a + e < c + f ∧ b + d < c + f ∧ 2 * c < c + f ∧ g < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_260
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ d + g)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_261
    {a c e f : ℕ}
    (h0 : 4 * a ≤ e + f)
    (h1 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_262
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
private theorem astra4wPowerNat113_263
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
private theorem astra4wPowerNat113_264
    {a b c e f : ℕ}
    (h0 : 4 * a ≤ b + c + e)
    (h1 : b + c < f)
    (h2 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_265
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ b + 2 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_266
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_267
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
private theorem astra4wPowerNat113_268
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
private theorem astra4wPowerNat113_269
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_270
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
private theorem astra4wPowerNat113_271
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
private theorem astra4wPowerNat113_272
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ d + g)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_273
    {a c e f : ℕ}
    (h0 : 3 * a ≤ e + f)
    (h1 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_274
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
private theorem astra4wPowerNat113_275
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
private theorem astra4wPowerNat113_276
    {a b c e f : ℕ}
    (h0 : 3 * a ≤ b + c + e)
    (h1 : b + c < f)
    (h2 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_277
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ b + 2 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_278
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 2 * c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_279
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
private theorem astra4wPowerNat113_280
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
private theorem astra4wPowerNat113_281
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ c + d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_282
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
private theorem astra4wPowerNat113_283
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_284
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
private theorem astra4wPowerNat113_285
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
private theorem astra4wPowerNat113_286
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
private theorem astra4wPowerNat113_287
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
private theorem astra4wPowerNat113_288
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
private theorem astra4wPowerNat113_289
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
private theorem astra4wPowerNat113_290
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
private theorem astra4wPowerNat113_291
    {a b c d e f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * g < a + 2 * f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b + c < f)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_292
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b + c < f)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_293
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 4 * b)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_294
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 4 * c)
    (h2 : b + c < f)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_295
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_296
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 9 * a ≤ 4 * e)
    (h2 : b + c < f)
    (h3 : e < a + c)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_297
    {a b c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_298
    {a b c d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * g < a + 2 * f)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_299
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
private theorem astra4wPowerNat113_300
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : a ≤ 4 * b)
    (h3 : b + c < f)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_301
    {a b c d f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 4 * c)
    (h2 : b + c < f)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_302
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_303
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 7 * a ≤ 4 * e)
    (h2 : b + c < f)
    (h3 : e < a + c)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_304
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 9 * a ≤ 4 * f)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_305
    {a b c d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * g < a + 2 * f)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_306
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
private theorem astra4wPowerNat113_307
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a ≤ b + g)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_308
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_309
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ d + e)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_310
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
private theorem astra4wPowerNat113_311
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 2 * b + d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_312
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
private theorem astra4wPowerNat113_313
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a + d < a + d + f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b + c < f)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + c + e < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_314
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a ≤ b + g)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_315
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_316
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ d + e)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_317
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
private theorem astra4wPowerNat113_318
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 4 * a ≤ 2 * b + d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_319
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
private theorem astra4wPowerNat113_320
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
private theorem astra4wPowerNat113_321
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ b + g)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_322
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_323
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ d + e)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_324
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
private theorem astra4wPowerNat113_325
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ 2 * b + d)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_326
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
private theorem astra4wPowerNat113_327
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_328
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
private theorem astra4wPowerNat113_329
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
private theorem astra4wPowerNat113_330
    {a b c d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : 5 * a ≤ b + g)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_331
    {a c d e f : ℕ}
    (h0 : 5 * a ≤ c + f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_332
    {a c d e f : ℕ}
    (h0 : 5 * a ≤ d + e)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_333
    {a b c d e f : ℕ}
    (h0 : 4 * a ≤ 3 * b)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_334
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
private theorem astra4wPowerNat113_335
    {a b c d e f : ℕ}
    (h0 : 5 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_336
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a + f < a + c + 2 * d)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b + c < f)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d ∧ 3 * a + b + e < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * b + f < a + c + 2 * d ∧ a + b + c + e < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 3 * b + e < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ b + c + g < a + c + 2 * d ∧ b + d + f < a + c + 2 * d ∧ b + 2 * e < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d ∧ f + g < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_337
    {a b c d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : 4 * a ≤ b + g)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_338
    {a c d e f : ℕ}
    (h0 : 4 * a ≤ c + f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_339
    {a c d e f : ℕ}
    (h0 : 4 * a ≤ d + e)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_340
    {a b c d e f : ℕ}
    (h0 : a + 2 * f = 4 * c)
    (h1 : a ≤ b)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_341
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
private theorem astra4wPowerNat113_342
    {a b c d e f : ℕ}
    (h0 : 4 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_343
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
private theorem astra4wPowerNat113_344
    {a b c d e f g : ℕ}
    (h0 : 2 * g < a + 2 * f)
    (h1 : 3 * a ≤ b + g)
    (h2 : a + 2 * f = 4 * c)
    (h3 : b + c < f)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_345
    {a c d e f : ℕ}
    (h0 : 3 * a ≤ c + f)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_346
    {a c d e f : ℕ}
    (h0 : 3 * a ≤ d + e)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_347
    {a b c d e f : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b + c < f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_348
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
private theorem astra4wPowerNat113_349
    {a b c d e f : ℕ}
    (h0 : 3 * a ≤ b + 2 * c)
    (h1 : b + c < f)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_350
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a ≤ f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_351
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
private theorem astra4wPowerNat113_352
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
private theorem astra4wPowerNat113_353
    {a c d e f : ℕ}
    (h0 : 0 < c + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : f < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_354
    {a c d e f : ℕ}
    (h0 : 0 < c + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : d < (c + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_355
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * c < (a + 2 * d) ∧ g < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_356
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : e < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_357
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : d < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_358
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : c < (a + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_359
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : c + e < (a + d + f) ∧ 2 * d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_360
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * c < (a + d + f) ∧ g < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_361
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + d < (a + d + f) ∧ f < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_362
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : e < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_363
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : d < (a + d + f) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_364
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + 2 * d < (a + c + 2 * d) ∧ 3 * c < (a + c + 2 * d) ∧ d + f < (a + c + 2 * d) ∧ 2 * e < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_365
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : c + e < (a + c + 2 * d) ∧ 2 * d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_366
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + f < (a + c + 2 * d) ∧ c + d < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_367
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * c < (a + c + 2 * d) ∧ g < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_368
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : f < (a + c + 2 * d) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_369
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
private theorem astra4wPowerNat113_370
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
private theorem astra4wPowerNat113_371
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
private theorem astra4wPowerNat113_372
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
private theorem astra4wPowerNat113_373
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
private theorem astra4wPowerNat113_374
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 5 * a < c + f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 5 * a < c + f ∧ 3 * a + c < c + f ∧ 2 * a + e < c + f ∧ a + 2 * c < c + f ∧ a + g < c + f ∧ c + e < c + f ∧ 2 * d < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_375
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
private theorem astra4wPowerNat113_376
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
private theorem astra4wPowerNat113_377
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
private theorem astra4wPowerNat113_378
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
private theorem astra4wPowerNat113_379
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
private theorem astra4wPowerNat113_380
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a < c + f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a < c + f ∧ 2 * a + c < c + f ∧ a + e < c + f ∧ 2 * c < c + f ∧ g < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_381
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : 3 * a ≤ 2 * b + d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_382
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
private theorem astra4wPowerNat113_383
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
private theorem astra4wPowerNat113_384
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
private theorem astra4wPowerNat113_385
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : 4 * a ≤ 3 * b + c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_386
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
private theorem astra4wPowerNat113_387
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : 4 * a ≤ 3 * b)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 3 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_388
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a < c + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a < c + f ∧ a + c < c + f ∧ e < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_389
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
private theorem astra4wPowerNat113_390
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
private theorem astra4wPowerNat113_391
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
private theorem astra4wPowerNat113_392
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
private theorem astra4wPowerNat113_393
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : 3 * a ≤ 3 * b + c)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_394
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
private theorem astra4wPowerNat113_395
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : a ≤ b)
    (h5 : b = 0)
    : 2 * a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_396
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
private theorem astra4wPowerNat113_397
    {a c d e f : ℕ}
    (h0 : 2 * a < c + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a < c + f ∧ c < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_398
    {a c d e f g : ℕ}
    (h0 : 2 * a ≤ d + g)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * g < a + 2 * f)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_399
    {a c e f : ℕ}
    (h0 : 2 * a ≤ e + f)
    (h1 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_400
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
private theorem astra4wPowerNat113_401
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
private theorem astra4wPowerNat113_402
    {a b c e f : ℕ}
    (h0 : 2 * a ≤ b + c + e)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b = 0)
    (h3 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_403
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
private theorem astra4wPowerNat113_404
    {a c d e f : ℕ}
    (h0 : 2 * a ≤ 2 * c + d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_405
    {a b c d f g : ℕ}
    (h0 : 2 * a ≤ 3 * b + c)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 2 * g < a + 2 * f)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_406
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
private theorem astra4wPowerNat113_407
    {a c d e f : ℕ}
    (h0 : 2 * a ≤ c + d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_408
    {a b c d f g : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 2 * g < a + 2 * f)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_409
    {a c d e f : ℕ}
    (h0 : 2 * a ≤ f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_410
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
private theorem astra4wPowerNat113_411
    {a c d e f : ℕ}
    (h0 : 2 * a ≤ d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a < c + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_412
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b = 0)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : ¬ (5 * a ≤ 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_413
    {a c d e f : ℕ}
    (h0 : 7 * a ≤ 4 * c)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_414
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 9 * a ≤ 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_415
    {a c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * e)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_416
    {a c d e f : ℕ}
    (h0 : 13 * a ≤ 4 * f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_417
    {a c d e f g : ℕ}
    (h0 : 15 * a ≤ 4 * g)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * g < a + 2 * f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 3 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_418
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a + d < a + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_419
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b = 0)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : ¬ (3 * a ≤ 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_420
    {a c d e f : ℕ}
    (h0 : 5 * a ≤ 4 * c)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_421
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 7 * a ≤ 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_422
    {a c d e f : ℕ}
    (h0 : 9 * a ≤ 4 * e)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_423
    {a c d e f : ℕ}
    (h0 : 11 * a ≤ 4 * f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_424
    {a c d e f g : ℕ}
    (h0 : 13 * a ≤ 4 * g)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * g < a + 2 * f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 2 * a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_425
    {a c d e f : ℕ}
    (h0 : 2 * a + d < a + 2 * d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_426
    {a b c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : a + 2 * f = 4 * c)
    (h2 : b = 0)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : ¬ (a ≤ 4 * b) := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_427
    {a c d e f : ℕ}
    (h0 : 3 * a ≤ 4 * c)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_428
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 5 * a ≤ 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_429
    {a c d e f : ℕ}
    (h0 : 7 * a ≤ 4 * e)
    (h1 : a + 2 * f = 4 * c)
    (h2 : c + f = d + e)
    (h3 : e < a + c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_430
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 9 * a ≤ 4 * f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_431
    {a c d e f g : ℕ}
    (h0 : 11 * a ≤ 4 * g)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * g < a + 2 * f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : a + d < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_432
    {a c d e f : ℕ}
    (h0 : a + d < a + 2 * d)
    (h1 : c + f = d + e)
    (h2 : e < a + c)
    : a + d < a + 2 * d ∧ f < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_433
    {a b c d f g : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 2 * g < a + 2 * f)
    (h4 : 5 * a ≤ b + g)
    (h5 : a + 2 * f = 4 * c)
    (h6 : b = 0)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_434
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : 4 * a ≤ 3 * b)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 4 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_435
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
private theorem astra4wPowerNat113_436
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
private theorem astra4wPowerNat113_437
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a + d < a + d + f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a + d < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_438
    {a b c d f g : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 2 * g < a + 2 * f)
    (h4 : 4 * a ≤ b + g)
    (h5 : a + 2 * f = 4 * c)
    (h6 : b = 0)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_439
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : a ≤ b)
    (h5 : b = 0)
    : 3 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_440
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
private theorem astra4wPowerNat113_441
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
private theorem astra4wPowerNat113_442
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a + d < a + d + f)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + d < a + d + f ∧ 2 * a + f < a + d + f ∧ a + c + d < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_443
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_444
    {a b c d f g : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 2 * g < a + 2 * f)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_445
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : 3 * a ≤ 2 * b + d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 2 * a + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_446
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
private theorem astra4wPowerNat113_447
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
private theorem astra4wPowerNat113_448
    {a c d e f : ℕ}
    (h0 : 2 * a + d < a + d + f)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + d < a + d + f ∧ a + f < a + d + f ∧ c + d < a + d + f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_449
    {a b c d f g : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 2 * g < a + 2 * f)
    (h4 : 5 * a ≤ b + g)
    (h5 : a + 2 * f = 4 * c)
    (h6 : b = 0)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_450
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : 4 * a ≤ 3 * b)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 4 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_451
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
private theorem astra4wPowerNat113_452
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
private theorem astra4wPowerNat113_453
    {a c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 4 * a + f < a + c + 2 * d)
    (h3 : a + 2 * f = 4 * c)
    (h4 : c + f = d + e)
    (h5 : e < a + c)
    : 4 * a + f < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d ∧ f + g < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_454
    {a b c d f g : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 2 * g < a + 2 * f)
    (h4 : 4 * a ≤ b + g)
    (h5 : a + 2 * f = 4 * c)
    (h6 : b = 0)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_455
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : a + 2 * f = 4 * c)
    (h4 : a ≤ b)
    (h5 : b = 0)
    : 3 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_456
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
private theorem astra4wPowerNat113_457
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
private theorem astra4wPowerNat113_458
    {a c d e f : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 3 * a + f < a + c + 2 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d ∧ e + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_459
    {a b c d e f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * g < a + 2 * f)
    (h2 : 3 * a ≤ b + g)
    (h3 : a + 2 * f = 4 * c)
    (h4 : b = 0)
    (h5 : c + f = d + e)
    (h6 : e < a + c)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_460
    {a b c d f g : ℕ}
    (h0 : 2 * a ≤ 3 * b)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : 2 * d < a + 2 * c)
    (h3 : 2 * g < a + 2 * f)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_461
    {a b c d f g : ℕ}
    (h0 : 2 * c + 2 * f = a + 4 * d)
    (h1 : 2 * d < a + 2 * c)
    (h2 : 2 * g < a + 2 * f)
    (h3 : 3 * a ≤ 2 * b + d)
    (h4 : a + 2 * f = 4 * c)
    (h5 : b = 0)
    : 2 * a + f < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem astra4wPowerNat113_462
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
private theorem astra4wPowerNat113_463
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
private theorem astra4wPowerNat113_464
    {a c d e f : ℕ}
    (h0 : 2 * a + f < a + c + 2 * d)
    (h1 : 2 * c + 2 * f = a + 4 * d)
    (h2 : a + 2 * f = 4 * c)
    (h3 : c + f = d + e)
    (h4 : e < a + c)
    : 2 * a + f < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ c + f < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Chamber `CDEFG` / `CF·DD·DE·EE·CCC` dies on power system `S15` (carriers κ, μ, ξ, π). -/
theorem quarticChamberCDEFG19810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG19810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
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
    exact hnc (by clear * - hBn hcq0 hcq1 hcq3 hcq4 hcq5 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_242 hcq0 hcq4 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_243 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_369 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_370 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_371 hAB hcq0 hcq5 h hcq3 hBn hcq1)
      · exact Or.inr (by exact astra4wPowerNat113_372 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_248 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_373 hAB hcq0 hcq5 h hcq3 hBn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_374 hcq0 hcq4 h hcq3 hcq1 hcq7)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_251 hcq0 hcq4 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_252 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_375 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_376 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_377 hAB hcq0 hcq5 h hcq3 hBn hcq1)
      · exact Or.inr (by exact astra4wPowerNat113_378 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_257 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_379 hAB hcq0 hcq5 h hcq3 hBn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_380 hcq0 hcq4 h hcq3 hcq1 hcq7)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_260 hcq0 hcq4 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_261 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_381 hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_382 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_383 hcq0 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_384 hcq0 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_266 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_385 hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_386 hAB hcq0 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_269 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_387 hcq0 hcq5 hcq4 h hcq3 hBn)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_388 hcq0 h hcq3 hcq1 hcq7)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_272 hcq0 hcq4 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_273 h hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_389 h hcq0 hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_390 hcq0 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_391 hcq0 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_392 hcq0 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_278 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_393 hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_394 hAB hcq0 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_281 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_395 hcq0 hcq5 hcq4 hcq3 h hBn)
      · exact Or.inr (by exact astra4wPowerNat113_283 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_396 hAB hcq0 h hcq3 hBn hcq1 hcq7)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_397 h hcq0 hcq3 hcq1 hcq7)
  have hz0theta : theta = 0 ∨ (A.natDegree < C.natDegree + F.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_398 h hcq0 hcq4 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat113_399 h hcq7)
    · exact Or.inr (by exact astra4wPowerNat113_400 hcq0 hcq3 h hBn hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat113_401 h hcq0 hcq3 hBn hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat113_402 h hcq3 hBn hcq7)
    · exact Or.inr (by exact astra4wPowerNat113_403 h hcq0 hcq3 hBn hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat113_404 h hcq0 hcq3 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat113_405 h hcq0 hcq5 hcq4 hcq3 hBn)
    · exact Or.inr (by exact astra4wPowerNat113_406 h hcq0 hcq3 hBn hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat113_407 h hcq0 hcq3 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat113_408 h hcq0 hcq5 hcq4 hcq3 hBn)
    · exact Or.inr (by exact astra4wPowerNat113_409 h hcq0 hcq3 hcq1 hcq7)
    · exact Or.inr (by exact astra4wPowerNat113_410 h hAB hcq0 hcq5 hcq3 hBn)
    · exact Or.inr (by exact astra4wPowerNat113_411 h hcq0 hcq3 hcq1 hcq7)
  have hr0 : (kappaQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest14810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hBz hz0l hz0beta (Or.inr (by exact astra4wPowerNat113_353 hdp0 hcq0 hcq3 hcq1 hcq7)) hz0delta (Or.inr (by exact astra4wPowerNat113_354 hdp0 hcq0 hcq3 hcq1 hcq7)) hz0zeta hz0theta
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
      · exact absurd h (by exact astra4wPowerNat113_412 hcq0 hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_413 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_414 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_415 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_416 h hcq0 hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_417 h hcq0 hcq4 hcq3 hcq1 hcq7)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_418 hcq0 h hcq3 hcq1 hcq7)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat113_419 hcq0 hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_420 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_421 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_422 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_423 h hcq0 hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_424 h hcq0 hcq4 hcq3 hcq1 hcq7)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_425 h hcq0 hcq3 hcq1 hcq7)
  have hz1delta : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by exact astra4wPowerNat113_426 hcq0 hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_427 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_428 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_429 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_430 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_431 h hcq0 hcq4 hcq3 hcq1 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_432 h hcq1 hcq7)
  have hr1 : (muQuarticChamberRest18810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest18810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hBz (by exact astra4wPowerNat113_191 hcq0 hcq4) (by exact astra4wPowerNat113_192 hcq1 hcq7) hz1l hz1beta (Or.inr (by exact astra4wPowerNat113_355 hcq0 hcq4 hcq3 hcq1 hcq7)) hz1delta (Or.inr (by exact astra4wPowerNat113_356 hcq0 hcq3 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat113_357 hcq0 hcq3 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat113_358 hcq0 hcq3 hcq1 hcq7))
  have hct1 := muQuarticChamberFace18810_coeff_top_S15 hAne hCne hDne hEne (B := B) (F := F) (G := G) (by exact astra4wPowerNat113_198 hcq0 hcq3) (by exact astra4wPowerNat113_199 hcq0 hcq1)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_433 hAB hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_308 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_309 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_434 hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_435 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_436 hAB hcq0 hcq5 h hcq3 hBn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_437 hcq0 hcq4 h hcq3 hcq1 hcq7)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_438 hAB hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_315 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_316 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_439 hcq0 hcq5 hcq4 hcq3 h hBn)
      · exact Or.inr (by exact astra4wPowerNat113_440 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_441 hAB hcq0 hcq5 h hcq3 hBn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_442 hcq0 h hcq3 hcq1 hcq7)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_443 hcq0 hcq4 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_322 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_323 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_444 h hcq0 hcq5 hcq4 hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_445 hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_446 hcq0 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_327 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_447 hAB hcq0 h hcq3 hBn hcq1 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_448 h hcq0 hcq3 hcq1 hcq7)
  have hr2 : (xiQuarticChamberRest20810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest20810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hBz (by exact astra4wPowerNat113_208 hcq0 hcq3 hcq1 hcq7) (by exact astra4wPowerNat113_209 hcq0 hcq4 hcq1) (by exact astra4wPowerNat113_210 hcq1 hcq7) hz2l hz2beta (Or.inr (by exact astra4wPowerNat113_359 hcq0 hcq3 hcq1 hcq7)) hz2delta (Or.inr (by exact astra4wPowerNat113_360 hcq0 hcq4 hcq3 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat113_361 hcq0 hcq3 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat113_362 hcq0 hcq3 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat113_363 hcq0 hcq3 hcq1 hcq7))
  have hct2 := xiQuarticChamberFace20810_coeff_top_S15 hAne hCne hDne hEne hFne (B := B) (G := G) (by exact astra4wPowerNat113_216 hcq0 hcq3 hcq1)
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_449 hAB hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_331 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_332 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_450 hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_451 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_452 hAB hcq0 hcq5 h hcq3 hBn)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_453 hcq0 hcq4 h hcq3 hcq1 hcq7)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_454 hAB hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_338 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_339 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_455 hcq0 hcq5 hcq4 hcq3 h hBn)
      · exact Or.inr (by exact astra4wPowerNat113_456 hAB hcq0 hcq5 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_457 hAB hcq0 hcq5 h hcq3 hBn)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_458 hcq0 h hcq3 hcq1 hcq7)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_459 hcq0 hcq4 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_345 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_346 h hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_460 h hcq0 hcq5 hcq4 hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_461 hcq0 hcq5 hcq4 h hcq3 hBn)
      · exact Or.inr (by exact astra4wPowerNat113_462 hcq0 h hcq3 hBn hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_350 hcq0 h hcq3 hcq1 hcq7)
      · exact Or.inr (by exact astra4wPowerNat113_463 hAB hcq0 h hcq3 hBn hcq1 hcq7)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_464 h hcq0 hcq3 hcq1 hcq7)
  have hr3 : (piQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest12810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hBz (by exact astra4wPowerNat113_230 hcq0 hcq4) (by exact astra4wPowerNat113_231 hcq1 hcq7) (by exact astra4wPowerNat113_232 hcq7) (by exact astra4wPowerNat113_233 hcq0 hcq4 hcq3) hz3l hz3beta (Or.inr (by exact astra4wPowerNat113_364 hcq0 hcq3 hcq1 hcq7)) hz3delta (Or.inr (by exact astra4wPowerNat113_365 hcq0 hcq3 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat113_366 hcq0 hcq3 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat113_367 hcq0 hcq4 hcq3 hcq1 hcq7)) (Or.inr (by exact astra4wPowerNat113_368 hcq0 hcq3 hcq1 hcq7))
  have hct3 := piQuarticChamberFace12810_coeff_top_S15 hAne hCne hDne hEne hFne (B := B) (G := G) (by exact astra4wPowerNat113_239 hcq0 hcq3) (by exact astra4wPowerNat113_240 hcq0 hcq3) (by exact astra4wPowerNat113_241 hcq0 hcq1)
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
/-- Chamber `BCDEFG` / `CF·DD·DE·EE·CCC` dies on power system `S15` (carriers κ, μ, ξ, π). -/
theorem quarticChamberBCDEFG93810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG93810 A B C D E F G)
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq3 hcq4 hcq5 hcq7 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_242 hcq0 hcq6 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_243 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_244 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_245 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_246 h hcq18 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_247 hcq0 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_248 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_249 hcq0 h hcq3 hcq18 hcq1 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_250 hcq0 hcq6 h hcq3 hcq18 hcq1 hcq9)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_251 hcq0 hcq6 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_252 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_253 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_254 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_255 h hcq18 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_256 hcq0 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_257 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_258 hcq0 h hcq3 hcq18 hcq1 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_259 hcq0 hcq6 h hcq3 hcq18 hcq1 hcq9)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_260 hcq0 hcq6 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_261 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_262 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_263 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_264 h hcq18 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_265 hcq0 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_266 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_267 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_268 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_269 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_270 hcq0 h hcq3 hcq18 hcq1 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_271 hcq0 h hcq3 hcq18 hcq1 hcq9)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_272 hcq0 hcq6 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_273 h hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_274 h hcq0 hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_275 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_276 h hcq18 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_277 hcq0 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_278 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_279 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_280 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_281 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_282 hcq0 hcq3 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_283 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_284 hcq0 h hcq3 hcq18 hcq1 hcq9)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_285 h hcq0 hcq3 hcq18 hcq1 hcq9)
  have hr0 : (kappaQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest14810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by exact astra4wPowerNat113_178 hcq3 hcq18) (by exact astra4wPowerNat113_179 hcq0 hcq3 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_180 hcq18) (by exact astra4wPowerNat113_181 hcq6 hcq3 hcq18) hz0l hz0beta (Or.inr (by exact astra4wPowerNat113_182 hcq0 hcq3 hcq18 hcq1 hcq9)) hz0delta (Or.inr (by exact astra4wPowerNat113_183 hcq0 hcq3 hcq18 hcq1 hcq9)) hz0zeta (Or.inr (by exact astra4wPowerNat113_184 hcq0 hcq3 hcq18 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat113_185 hcq3 hcq18))
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_286 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_287 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_288 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_289 h hcq0 hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_290 h hcq0 hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_291 h hcq0 hcq6 hcq3 hcq18 hcq1 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_292 hcq0 hcq6 h hcq3 hcq18 hcq1 hcq9)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_293 hcq0 h hcq3 hcq18)
      · exact Or.inr (by exact astra4wPowerNat113_294 hcq0 h hcq18)
      · exact Or.inr (by exact astra4wPowerNat113_295 hcq0 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_296 hcq0 h hcq18 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_297 h hcq0 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_298 h hcq0 hcq6 hcq18 hcq1 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_299 hcq0 h hcq3 hcq18 hcq1 hcq9)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ F.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_300 hcq0 hcq3 h hcq18)
      · exact Or.inr (by exact astra4wPowerNat113_301 hcq0 h hcq18)
      · exact Or.inr (by exact astra4wPowerNat113_302 hcq0 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_303 hcq0 h hcq18 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_304 hcq0 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_305 h hcq0 hcq6 hcq18 hcq1 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_306 h hcq0 hcq3 hcq18 hcq1 hcq9)
  have hr1 : (muQuarticChamberRest18810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest18810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 (by exact astra4wPowerNat113_186 hcq0 hcq3 hcq18) (by exact astra4wPowerNat113_187 hcq3 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_188 hcq0 hcq3 hcq18) (by exact astra4wPowerNat113_189 hcq0 hcq3 hcq18 hcq9) (by exact astra4wPowerNat113_190 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_191 hcq0 hcq6) (by exact astra4wPowerNat113_192 hcq1 hcq9) hz1l hz1beta (Or.inr (by exact astra4wPowerNat113_193 hcq0 hcq6 hcq3 hcq18 hcq1 hcq9)) hz1delta (Or.inr (by exact astra4wPowerNat113_194 hcq0 hcq3 hcq18 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat113_195 hcq0 hcq3 hcq18 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat113_196 hcq0 hcq3 hcq18 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat113_197 hcq3 hcq18 hcq1 hcq9))
  have hct1 := muQuarticChamberFace18810_coeff_top_S15 hAne hCne hDne hEne (B := B) (F := F) (G := G) (by exact astra4wPowerNat113_198 hcq0 hcq3) (by exact astra4wPowerNat113_199 hcq0 hcq1)
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_307 hcq0 hcq6 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_308 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_309 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_310 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_311 hcq0 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_312 hcq0 h hcq3 hcq18 hcq1 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_313 hcq0 hcq6 h hcq3 hcq18 hcq1 hcq9)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_314 hcq0 hcq6 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_315 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_316 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_317 hcq0 hcq3 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_318 hcq0 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_319 hcq0 h hcq3 hcq18 hcq1 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_320 hcq0 h hcq3 hcq18 hcq1 hcq9)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_321 hcq0 hcq6 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_322 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_323 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_324 h hcq0 hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_325 hcq0 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_326 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_327 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_328 hcq0 h hcq3 hcq18 hcq1 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_329 h hcq0 hcq3 hcq18 hcq1 hcq9)
  have hr2 : (xiQuarticChamberRest20810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest20810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 (by exact astra4wPowerNat113_200 hcq3 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_201 hcq0 hcq3 hcq18 hcq1) (by exact astra4wPowerNat113_202 hcq18) (by exact astra4wPowerNat113_203 hcq0 hcq3 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_204 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_205 hcq6 hcq3 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_206 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_207 hcq18 hcq9) (by exact astra4wPowerNat113_208 hcq0 hcq3 hcq1 hcq9) (by exact astra4wPowerNat113_209 hcq0 hcq6 hcq1) (by exact astra4wPowerNat113_210 hcq1 hcq9) hz2l hz2beta (Or.inr (by exact astra4wPowerNat113_211 hcq0 hcq3 hcq18 hcq1 hcq9)) hz2delta (Or.inr (by exact astra4wPowerNat113_212 hcq0 hcq6 hcq3 hcq18 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat113_213 hcq0 hcq3 hcq18 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat113_214 hcq0 hcq3 hcq18 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat113_215 hcq0 hcq3 hcq18 hcq1 hcq9))
  have hct2 := xiQuarticChamberFace20810_coeff_top_S15 hAne hCne hDne hEne hFne (B := B) (G := G) (by exact astra4wPowerNat113_216 hcq0 hcq3 hcq1)
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
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_330 hcq6 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_331 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_332 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_333 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_334 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_335 h hcq18 hcq1 hcq9)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_336 hcq0 hcq6 h hcq3 hcq18 hcq1 hcq9)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_337 hcq6 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_338 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_339 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_340 hcq3 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_341 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_342 h hcq18 hcq1 hcq9)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_343 hcq0 h hcq3 hcq18 hcq1 hcq9)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_344 hcq6 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_345 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_346 h hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_347 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_348 hcq0 h hcq3 hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_349 h hcq18 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_350 hcq0 h hcq3 hcq1 hcq9)
      · exact Or.inr (by exact astra4wPowerNat113_351 hcq0 h hcq3 hcq18 hcq1 hcq9)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_352 h hcq0 hcq3 hcq18 hcq1 hcq9)
  have hr3 : (piQuarticChamberRest12810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest12810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 (by exact astra4wPowerNat113_217 hcq0 hcq3 hcq18) (by exact astra4wPowerNat113_218 hcq3 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_219 hcq0 hcq3 hcq18) (by exact astra4wPowerNat113_220 hcq3 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_221 hcq0 hcq6 hcq3 hcq18) (by exact astra4wPowerNat113_222 hcq0 hcq3 hcq18) (by exact astra4wPowerNat113_223 hcq0 hcq3 hcq18 hcq1) (by exact astra4wPowerNat113_224 hcq3 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_225 hcq0 hcq3 hcq18 hcq9) (by exact astra4wPowerNat113_226 hcq0 hcq3 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_227 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_228 hcq6 hcq3 hcq18 hcq1 hcq9) (by exact astra4wPowerNat113_229 hcq0 hcq3 hcq18 hcq9) (by exact astra4wPowerNat113_230 hcq0 hcq6) (by exact astra4wPowerNat113_231 hcq1 hcq9) (by exact astra4wPowerNat113_232 hcq9) (by exact astra4wPowerNat113_233 hcq0 hcq6 hcq3) hz3l hz3beta (Or.inr (by exact astra4wPowerNat113_234 hcq0 hcq3 hcq18 hcq1 hcq9)) hz3delta (Or.inr (by exact astra4wPowerNat113_235 hcq0 hcq3 hcq18 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat113_236 hcq0 hcq3 hcq18 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat113_237 hcq0 hcq6 hcq3 hcq18 hcq1 hcq9)) (Or.inr (by exact astra4wPowerNat113_238 hcq3 hcq18 hcq1 hcq9))
  have hct3 := piQuarticChamberFace12810_coeff_top_S15 hAne hCne hDne hEne hFne (B := B) (G := G) (by exact astra4wPowerNat113_239 hcq0 hcq3) (by exact astra4wPowerNat113_240 hcq0 hcq3) (by exact astra4wPowerNat113_241 hcq0 hcq1)
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
/-- Chamber `BCDFG` / `BF·BG·CF·CG` dies on power system `S16` (carriers κ, μ, π). -/
theorem quarticChamberBCDFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG6810 A B C D E F G)
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hEn hcq0 hcq1 hcq3 hcq4 hcq6 hcq9 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_132 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_133 h hcq0 hcq9 hAE hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_134 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_034 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_135 h hcq1 hcq0 hcq9 hcq4 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_136 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_137 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_038 h hcq1 hcq0 hcq10 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_138 h hcq1 hcq0 hcq10 hcq4 hcq6)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_139 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_140 h hcq0 hcq9 hcq4 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_141 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_043 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_142 h hcq1 hcq0 hcq9 hcq4 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_143 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_144 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_047 h hcq1 hcq0 hcq10 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_145 h hcq1 hcq0 hcq10 hcq4 hcq6)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_146 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_147 h hcq0 hcq9 hcq4 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_148 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_052 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_149 h hcq1 hcq0 hcq9 hcq4 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_150 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_151 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_056 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_152 h hcq1 hcq0 hcq10 hAE hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_153 h hcq1 hcq0 hcq10 hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_059 h hcq1 hcq0 hcq10 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_154 h hcq1 hcq10 hcq6)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_155 h hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_156 h hcq1 hcq0 hcq10 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_157 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_064 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_158 h hcq1 hcq0 hcq10 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_159 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_160 h hcq1 hcq0 hcq10 hcq4)
      · exact Or.inr (by exact astra4wPowerNat113_068 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_161 h hcq0 hcq9 hcq4 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_162 h hcq1 hcq0 hcq10 hcq4 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_071 hcq1 hcq0 h hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_072 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_073 h hcq1 hcq0 hcq10 hcq6)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_074 h hcq10 hcq6)
  have hr0 : (kappaQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest16810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hEz (by exact astra4wPowerNat113_000 hcq1 hcq0 hcq10) (by exact astra4wPowerNat113_114 hcq1 hcq0 hcq10 hcq4) (by exact astra4wPowerNat113_001 hcq1 hcq0 hcq10) hz0l hz0beta (Or.inr (by exact astra4wPowerNat113_002 hcq1 hcq0 hcq10 hcq6)) hz0delta (Or.inr (by exact astra4wPowerNat113_115 hcq1 hcq0 hcq10 hcq4)) hz0zeta (Or.inr (by exact astra4wPowerNat113_003 hcq1 hcq0 hcq10 hcq6)) (Or.inr (by exact astra4wPowerNat113_004 hcq1 hcq0 hcq10))
  have hct0 := kappaQuarticChamberFace16810_coeff_top_S16 hBne hCne hFne hGne (A := A) (D := D) (E := E) (by exact astra4wPowerNat113_005 hcq1 hcq0)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_075 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_076 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_163 h hcq1 hcq10 hcq4)
      · exact absurd h (by exact astra4wPowerNat113_164 hcq1 hcq10 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_079 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_080 h hcq1 hcq0 hcq10 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_165 h hcq1 hcq0 hcq10 hcq4 hcq6)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_082 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_083 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_166 h hcq1 hcq10 hcq4)
      · exact absurd h (by exact astra4wPowerNat113_167 hcq1 hcq10 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_086 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_087 h hcq1 hcq0 hcq10 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_168 h hcq1 hcq10 hcq4 hcq6)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_089 hcq1 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_090 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_169 h hcq1 hcq10 hcq4)
      · exact absurd h (by exact astra4wPowerNat113_170 hcq1 hcq10 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_093 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_094 h hcq1 hcq0 hcq10 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_171 h hcq10 hcq4 hcq6)
  have hr1 : (muQuarticChamberRest20810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest20810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hEz (by exact astra4wPowerNat113_006 hcq10) (by exact astra4wPowerNat113_007 hcq1 hcq10 hcq6) (by exact astra4wPowerNat113_116 hcq3) (by exact astra4wPowerNat113_117 hcq10 hcq4) (by exact astra4wPowerNat113_009 hcq1 hcq10) (by exact astra4wPowerNat113_118 hcq4) hz1l hz1beta (Or.inr (by exact astra4wPowerNat113_119 hcq1 hcq0 hcq10 hcq4 hcq6)) hz1delta (Or.inr (by exact astra4wPowerNat113_120 hcq1 hcq10 hcq6)) (Or.inr (by exact astra4wPowerNat113_121 hcq1 hcq10 hcq4 hcq6)) (Or.inr (by exact astra4wPowerNat113_013 hcq1 hcq10 hcq6)) (Or.inr (by exact astra4wPowerNat113_014 hcq1 hcq10 hcq6))
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_096 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_097 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_172 h hcq1 hcq10 hcq4)
      · exact absurd h (by exact astra4wPowerNat113_164 hcq1 hcq10 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_099 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_100 h hcq1 hcq0 hcq10 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_173 h hcq1 hcq0 hcq10 hcq4 hcq6)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_102 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_103 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_174 h hcq1 hcq10 hcq4)
      · exact absurd h (by exact astra4wPowerNat113_167 hcq1 hcq10 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_105 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_106 h hcq1 hcq0 hcq10 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_175 h hcq1 hcq10 hcq4 hcq6)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_108 hcq1 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_109 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_176 h hcq1 hcq10 hcq4)
      · exact absurd h (by exact astra4wPowerNat113_170 hcq1 hcq10 hEn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_111 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_112 h hcq1 hcq0 hcq10 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_177 h hcq1 hcq10 hcq4 hcq6)
  have hr2 : (piQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest14810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hEz (by exact astra4wPowerNat113_015 hcq1 hcq10) (by exact astra4wPowerNat113_122 hcq1 hcq10 hcq4) (by exact astra4wPowerNat113_016 hcq10) (by exact astra4wPowerNat113_017 hcq1 hcq10 hcq6) (by exact astra4wPowerNat113_018 hcq1 hcq0 hcq10) (by exact astra4wPowerNat113_019 hcq10) (by exact astra4wPowerNat113_123 hcq3 hcq10) (by exact astra4wPowerNat113_020 hcq1 hcq10 hcq6) (by exact astra4wPowerNat113_124 hcq1 hcq10 hcq4) (by exact astra4wPowerNat113_125 hcq10 hcq4) (by exact astra4wPowerNat113_022 hcq1 hcq10) (by exact astra4wPowerNat113_126 hcq1 hcq0 hcq10 hcq4) (by exact astra4wPowerNat113_024 hcq1 hcq0 hcq10) (by exact astra4wPowerNat113_127 hcq10 hcq4) hz2l hz2beta (Or.inr (by exact astra4wPowerNat113_128 hcq3 hcq1 hcq10 hcq4 hcq6)) hz2delta (Or.inr (by exact astra4wPowerNat113_129 hcq1 hcq10 hcq4 hcq6)) (Or.inr (by exact astra4wPowerNat113_130 hcq1 hcq10 hcq4 hcq6)) (Or.inr (by exact astra4wPowerNat113_131 hcq1 hcq0 hcq10 hcq4 hcq6)) (Or.inr (by exact astra4wPowerNat113_030 hcq1 hcq10 hcq6))
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
/-- Chamber `BCEFG` / `BF·BG·CF·CG` dies on power system `S16` (carriers κ, μ, π). -/
theorem quarticChamberBCEFG6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG6810 A B C D E F G)
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
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < B.natDegree + G.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq3 hcq6 hcq9 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_031 hAD h hcq0 hcq9 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_032 hcq3 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_033 h hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_034 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_035 h hcq0 hcq10 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_036 hAD h hcq0 hcq9 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_037 h hcq1 hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_038 h hcq1 hcq0 hcq10 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_039 h hcq1 hcq0 hcq10 hcq5 hcq6)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_040 h hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_041 hcq3 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_042 h hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_043 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_044 h hcq0 hcq10 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_045 h hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_046 h hcq1 hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_047 h hcq1 hcq0 hcq10 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_048 h hcq1 hcq0 hcq10 hcq5 hcq6)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_049 h hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_050 hcq3 h hcq0 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_051 h hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_052 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_053 h hcq0 hcq10 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_054 h hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_055 h hcq1 hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_056 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_057 h hcq1 hcq0 hcq10 hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_058 hAD h hcq1 hcq0 hcq10 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_059 h hcq1 hcq0 hcq10 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_060 h hcq1 hcq0 hcq10 hcq5 hcq6)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree ∧ C.natDegree < B.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_061 h hcq1 hcq0 hcq10 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_062 h hcq0 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_063 h hcq1 hcq0 hcq10 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_064 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_065 h hcq0 hcq10 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_066 h hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_067 h hcq1 hcq0 hcq10 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_068 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_069 h hcq1 hcq0 hcq10 hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_070 h hcq1 hcq0 hcq9 hDn hcq5 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_071 hcq1 hcq0 h hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_072 h hcq1 hcq0 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_073 h hcq1 hcq0 hcq10 hcq6)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_074 h hcq10 hcq6)
  have hr0 : (kappaQuarticChamberRest16810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest16810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by exact astra4wPowerNat113_000 hcq1 hcq0 hcq10) (by exact astra4wPowerNat113_001 hcq1 hcq0 hcq10) hz0l hz0beta (Or.inr (by exact astra4wPowerNat113_002 hcq1 hcq0 hcq10 hcq6)) hz0delta hz0zeta (Or.inr (by exact astra4wPowerNat113_003 hcq1 hcq0 hcq10 hcq6)) (Or.inr (by exact astra4wPowerNat113_004 hcq1 hcq0 hcq10))
  have hct0 := kappaQuarticChamberFace16810_coeff_top_S16 hBne hCne hFne hGne (A := A) (D := D) (E := E) (by exact astra4wPowerNat113_005 hcq1 hcq0)
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
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_075 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_076 h hcq1 hcq10)
      · exact absurd h (by exact astra4wPowerNat113_077 hcq1 hcq10 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_078 h hcq1 hcq0 hcq10 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_079 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_080 h hcq1 hcq0 hcq10 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_081 h hcq1 hcq0 hcq10 hcq5 hcq6)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_082 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_083 h hcq1 hcq10)
      · exact absurd h (by exact astra4wPowerNat113_084 hcq1 hcq10 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_085 h hcq1 hcq0 hcq10 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_086 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_087 h hcq1 hcq0 hcq10 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_088 h hcq1 hcq0 hcq10 hcq5 hcq6)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + B.natDegree + F.natDegree ∧ F.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + B.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_089 hcq1 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_090 h hcq1 hcq10)
      · exact absurd h (by exact astra4wPowerNat113_091 hcq1 hcq10 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_092 h hcq1 hcq0 hcq10 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_093 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_094 h hcq1 hcq0 hcq10 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_095 h hcq10 hcq6)
  have hr1 : (muQuarticChamberRest20810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + F.natDegree :=
    muQuarticChamberRest20810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hDz (by exact astra4wPowerNat113_006 hcq10) (by exact astra4wPowerNat113_007 hcq1 hcq10 hcq6) (by exact astra4wPowerNat113_008 hcq1 hcq0 hcq10 hcq5) (by exact astra4wPowerNat113_009 hcq1 hcq10) (by exact hcq3) hz1l hz1beta (Or.inr (by exact astra4wPowerNat113_010 hcq1 hcq0 hcq10 hcq6)) hz1delta (Or.inr (by exact astra4wPowerNat113_011 hcq3 hcq1 hcq10 hcq6)) (Or.inr (by exact astra4wPowerNat113_012 hcq1 hcq10 hcq6)) (Or.inr (by exact astra4wPowerNat113_013 hcq1 hcq10 hcq6)) (Or.inr (by exact astra4wPowerNat113_014 hcq1 hcq10 hcq6))
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
  have hz2l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 5 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_096 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_097 h hcq1 hcq10)
      · exact absurd h (by exact astra4wPowerNat113_077 hcq1 hcq10 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_098 h hcq1 hcq0 hcq10 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_099 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_100 h hcq1 hcq0 hcq10 hcq6)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_101 h hcq1 hcq0 hcq10 hcq5 hcq6)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * B.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_102 h hcq1 hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_103 h hcq1 hcq10)
      · exact absurd h (by exact astra4wPowerNat113_084 hcq1 hcq10 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_104 h hcq1 hcq0 hcq10 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_105 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_106 h hcq1 hcq0 hcq10 hcq6)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_107 h hcq1 hcq0 hcq10 hcq5 hcq6)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by exact astra4wPowerNat113_108 hcq1 h hcq10)
      · exact Or.inr (by exact astra4wPowerNat113_109 h hcq1 hcq10)
      · exact absurd h (by exact astra4wPowerNat113_091 hcq1 hcq10 hDn hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_110 h hcq1 hcq0 hcq10 hcq5)
      · exact Or.inr (by exact astra4wPowerNat113_111 h hcq1 hcq10 hcq6)
      · exact Or.inr (by exact astra4wPowerNat113_112 h hcq1 hcq0 hcq10 hcq6)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by exact astra4wPowerNat113_113 h hcq1 hcq0 hcq10 hcq5 hcq6)
  have hr2 : (piQuarticChamberRest14810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest14810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hDz (by exact astra4wPowerNat113_015 hcq1 hcq10) (by exact astra4wPowerNat113_016 hcq10) (by exact astra4wPowerNat113_017 hcq1 hcq10 hcq6) (by exact astra4wPowerNat113_018 hcq1 hcq0 hcq10) (by exact astra4wPowerNat113_019 hcq10) (by exact astra4wPowerNat113_020 hcq1 hcq10 hcq6) (by exact astra4wPowerNat113_021 hcq1 hcq0 hcq10 hcq5) (by exact astra4wPowerNat113_022 hcq1 hcq10) (by exact astra4wPowerNat113_023 hcq1 hcq0 hcq10 hcq5) (by exact astra4wPowerNat113_024 hcq1 hcq0 hcq10) (by exact astra4wPowerNat113_025 hcq3 hcq10) hz2l hz2beta (Or.inr (by exact astra4wPowerNat113_026 hcq3 hcq1 hcq0 hcq10 hcq5 hcq6)) hz2delta (Or.inr (by exact astra4wPowerNat113_027 hcq3 hcq1 hcq10 hcq6)) (Or.inr (by exact astra4wPowerNat113_028 hcq1 hcq0 hcq10 hcq5 hcq6)) (Or.inr (by exact astra4wPowerNat113_029 hcq1 hcq0 hcq10 hcq6)) (Or.inr (by exact astra4wPowerNat113_030 hcq1 hcq10 hcq6))
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
