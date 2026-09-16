import Grok810ScaleZeroQuarticSigmaLadderPart102Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart103Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart104Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart101Scratch

/-! Part 92 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_000
    {a b g : ℕ}
    (h0 : 4 * g < 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_001
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : 2 * c ≤ a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_002
    {a b d : ℕ}
    (h0 : 4 * d < a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_003
    {a b e : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_004
    {a b f : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_005
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_006
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_007
    {a b g : ℕ}
    (h0 : 7 * a + 6 * b < 4 * g)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_008
    {a b c g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_009
    {a b d g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_010
    {a b e g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_011
    {a b f g : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_012
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 4 * f = 5 * a + 6 * b)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_013
    {a b f : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_014
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_015
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_016
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_017
    {a b c f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_018
    {a b d f : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_019
    {a b e f : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_020
    {a b f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_021
    {a b c f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : 5 * a + 6 * b < 4 * f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_022
    {a b f g : ℕ}
    (h0 : 5 * a + 6 * b < 4 * f)
    (h1 : a + 2 * f < 2 * g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_023
    {a b c f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_024
    {a b d f g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_025
    {a b e f g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_026
    {a b e : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_027
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_028
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_029
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * f = 5 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_030
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_031
    {a b c e f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a + 6 * b < 4 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_032
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_033
    {a b e f g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_034
    {a b c e : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_035
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_036
    {a b e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_037
    {a b c e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_038
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_039
    {a e f g : ℕ}
    (h0 : 2 * f < a + 2 * e)
    (h1 : a + e < g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_040
    {a e f g : ℕ}
    (h0 : 2 * f = a + 2 * e)
    (h1 : a + e < g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_041
    {a b e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_042
    {a b c e f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_043
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_044
    {a b e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_045
    {a b c e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : 3 * a + 6 * b < 4 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_046
    {a b e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_047
    {a b c e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_048
    {a b d e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_049
    {a e f g : ℕ}
    (h0 : a + 2 * e < 2 * f)
    (h1 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_050
    {a b d : ℕ}
    (h0 : 4 * d = a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_051
    {a b d g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_052
    {a b d f : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_053
    {a b d f g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_054
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_055
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_056
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_057
    {a b d e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_058
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 6 * b < 4 * d)
    : 3 * c < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_059
    {a b d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_060
    {a b c d g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 2 * d < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_061
    {a d e g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_062
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f < a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_063
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f = a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_064
    {a b d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_065
    {a b c d f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_066
    {a d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_067
    {a b d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_068
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_069
    {a b d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_070
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_071
    {a d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + d < f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_072
    {a d e f g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_073
    {a d e g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_074
    {a d e f : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_075
    {a d e f g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_076
    {a b d e : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_077
    {a b c d e : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 6 * b < 4 * d)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_078
    {a b d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_079
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + e < g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_080
    {a d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_081
    {a b d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 6 * b < 4 * d)
    (h3 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_082
    {a b c d e f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 6 * b < 4 * d)
    (h4 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_083
    {a d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_084
    {a b d e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 6 * b < 4 * d)
    (h4 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_085
    {a b c d e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : a + 6 * b < 4 * d)
    (h5 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_086
    {a b d e f g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : a + 6 * b < 4 * d)
    (h4 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_087
    {a b c d e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : a + 6 * b < 4 * d)
    (h5 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_088
    {a d e f g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_089
    {a b c : ℕ}
    (h0 : 2 * c = a + 2 * b)
    : 2 * c ≤ a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_090
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_091
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_092
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_093
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 4 * f = 5 * a + 6 * b)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_094
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_095
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_096
    {a b c f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_097
    {a b c e : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_098
    {a b c e g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_099
    {a b c e f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_100
    {a b c e f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_101
    {a b c e f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : 3 * a + 6 * b < 4 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_102
    {a b c e f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_103
    {a b c d : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 6 * b < 4 * d)
    : 3 * c < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_104
    {a b c d g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 2 * d < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_105
    {a b c d f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_106
    {a b c d f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_107
    {a b c d f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_108
    {a b c d e : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 6 * b < 4 * d)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_109
    {a b c d e g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + e < g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_110
    {a b c d e f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 6 * b < 4 * d)
    (h4 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_111
    {a b c d e f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : a + 6 * b < 4 * d)
    (h5 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_112
    {a b c d e f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : a + 6 * b < 4 * d)
    (h5 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_113
    {a c g : ℕ}
    (h0 : 2 * g < 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_114
    {a b c : ℕ}
    (h0 : a + 2 * b < 2 * c)
    : a + 2 * b ≤ 2 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_115
    {a c d : ℕ}
    (h0 : a + 2 * d < 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_116
    {c e : ℕ}
    (h0 : 2 * e < 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_117
    {a c f : ℕ}
    (h0 : 2 * f < a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_118
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_119
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_120
    {a b c g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * b < 2 * c)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_121
    {a c g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_122
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d < 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_123
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e < 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_124
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f < a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_125
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_126
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_127
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f = a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_128
    {a b c f : ℕ}
    (h0 : a + 2 * b < 2 * c)
    (h1 : a + 3 * c < 2 * f)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_129
    {a c f : ℕ}
    (h0 : a + 3 * c < 2 * f)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_130
    {a c d f : ℕ}
    (h0 : a + 2 * d < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_131
    {a c e f : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_132
    {a b c f g : ℕ}
    (h0 : a + 2 * b < 2 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_133
    {a c f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 3 * c < 2 * f)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_134
    {a c d f g : ℕ}
    (h0 : a + 2 * d < 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_135
    {a c e f g : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_136
    {c e : ℕ}
    (h0 : 2 * e = 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_137
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e = 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_138
    {a c e f : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_139
    {a c e f g : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_140
    {a b c e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_141
    {a c d e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_142
    {a b c e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_143
    {a c e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_144
    {a c d e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_145
    {a b c e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_146
    {a c e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_147
    {a c d e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_148
    {a b c e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < 2 * e)
    (h2 : a + 2 * b < 2 * c)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_149
    {a c e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_150
    {a b c e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_151
    {a c e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_152
    {a c d e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_153
    {a c d : ℕ}
    (h0 : a + 2 * d = 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_154
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d = 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_155
    {a c d f : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_156
    {a c d f g : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_157
    {a c d e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_158
    {a c d e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_159
    {a c d e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_160
    {a c d e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_161
    {a b c d : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    : a + 6 * b < 4 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_162
    {a b c d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_163
    {a c d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : 3 * c < a + 2 * d)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_164
    {a b c d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : a + d < f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_165
    {a c d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_166
    {a b c d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_167
    {a c d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_168
    {a b c d f g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * f < 2 * g)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_169
    {a c d f g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_170
    {a b c d e : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * d < 2 * e)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_171
    {a c d e : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_172
    {a b c d e g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + e < g)
    (h4 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_173
    {a c d e g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_174
    {a b c d e f : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_175
    {a c d e f : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_176
    {a b c d e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : a + 2 * d < 2 * e)
    (h4 : a + 2 * e < 2 * f)
    (h5 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_177
    {a c d e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_178
    {a b c d e f g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : a + 2 * f < 2 * g)
    (h5 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith105_179
    {a c d e f g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
                  Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
                  Or.inr hBDlt, Or.inr hBElt, Or.inr hmBFlt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
                  Or.inr hBDlt, Or.inr hBElt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
                  Or.inr hBClt, Or.inr hBDlt, Or.inr hBElt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties B
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_005 hBGeq hAG), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_005 hBGeq hAG), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks B
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_007 hBGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_008 hBClt hBGgt hAG), Or.inr (by exact sigmaSpeedTArith105_009 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith105_010 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith105_011 hBFlt hBGgt)⟩
        · -- F ties B
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_012 hAB hBFeq), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BF
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_014 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_007 hBGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_008 hBClt hBGgt hAG), Or.inr (by exact sigmaSpeedTArith105_009 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith105_010 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith105_015 hBFeq hBGgt)⟩
        · -- F strictly outranks B
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_016 hAB hBFgt),
              Or.inr (by exact sigmaSpeedTArith105_017 hBClt hBFgt hAC), Or.inr (by exact sigmaSpeedTArith105_018 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith105_019 hBElt hBFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_020 hFGeq hBFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_021 hBClt hFGeq hBFgt hAG), Or.inr (by exact sigmaSpeedTArith105_018 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith105_019 hBElt hBFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_022 hBFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_023 hBClt hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_024 hBDlt hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_025 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
      · -- E ties B
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
                  Or.inr hBDlt, Or.inr hmBFlt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
                  Or.inr hBClt, Or.inr hBDlt, Or.inr hmBFlt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
                  Or.inr hBClt, Or.inr hBDlt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBEFG ⟨hA, hBne, hEne, hFne, hGne, hBEeq,
                  hmBFeq, hmBGeq, Or.inr hBClt, Or.inr hBDlt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BE
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_027 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_027 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BE
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_007 hBGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_008 hBClt hBGgt hAG), Or.inr (by exact sigmaSpeedTArith105_009 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith105_028 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_011 hBFlt hBGgt)⟩
        · -- F ties BE
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_029 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BEF
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_029 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BEF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_007 hBGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_008 hBClt hBGgt hAG), Or.inr (by exact sigmaSpeedTArith105_009 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith105_028 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_015 hBFeq hBGgt)⟩
        · -- F strictly outranks BE
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_030 hBEeq hBFgt hAE),
              Or.inr (by exact sigmaSpeedTArith105_031 hBClt hBEeq hBFgt hAE), Or.inr (by exact sigmaSpeedTArith105_018 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith105_032 hBEeq hBFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_020 hFGeq hBFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_021 hBClt hFGeq hBFgt hAG), Or.inr (by exact sigmaSpeedTArith105_018 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith105_032 hBEeq hBFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_022 hBFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_023 hBClt hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_024 hBDlt hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_033 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
      · -- E strictly outranks B
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith105_034 hBClt hBEgt),
              Or.inr (by exact sigmaSpeedTArith105_035 hBEgt hBDlt), Or.inr hEFlt, Or.inr hEGlt⟩
          · -- G ties E
            exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
              Or.inr (by exact sigmaSpeedTArith105_034 hBClt hBEgt), Or.inr (by exact sigmaSpeedTArith105_035 hBEgt hBDlt), Or.inr hEFlt⟩
          · -- G strictly outranks E
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_036 hBEgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_037 hBClt hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_038 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_039 hEFlt hEGgt)⟩
        · -- F ties E
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
              Or.inr (by exact sigmaSpeedTArith105_034 hBClt hBEgt), Or.inr (by exact sigmaSpeedTArith105_035 hBEgt hBDlt), Or.inr hEGlt⟩
          · -- G ties EF
            exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
              Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith105_034 hBClt hBEgt), Or.inr (by exact sigmaSpeedTArith105_035 hBEgt hBDlt)⟩
          · -- G strictly outranks EF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_036 hBEgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_037 hBClt hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_038 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_040 hEFeq hEGgt)⟩
        · -- F strictly outranks E
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_041 hBEgt hEFgt hAE),
              Or.inr (by exact sigmaSpeedTArith105_042 hBClt hBEgt hEFgt hAE), Or.inr (by exact sigmaSpeedTArith105_043 hBEgt hBDlt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_044 hFGeq hBEgt hEFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_045 hBClt hFGeq hBEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith105_043 hBEgt hBDlt hEFgt), Or.inr hEFgt⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_046 hBEgt hEFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_047 hBClt hBEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_048 hBEgt hBDlt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_049 hEFgt hFGgt), Or.inr hFGgt⟩
    · -- D ties B
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
                  Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
                  Or.inr hBClt, Or.inr hBElt, Or.inr hmBFlt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
                  Or.inr hBClt, Or.inr hBElt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBDFG ⟨hA, hBne, hDne, hFne, hGne, hBDeq,
                  hmBFeq, hmBGeq, Or.inr hBClt, Or.inr hBElt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BD
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_005 hBGeq hAG), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_005 hBGeq hAG), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BD
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_007 hBGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_008 hBClt hBGgt hAG), Or.inr (by exact sigmaSpeedTArith105_051 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_010 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith105_011 hBFlt hBGgt)⟩
        · -- F ties BD
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_012 hAB hBFeq), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BDF
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_014 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BDF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_007 hBGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_008 hBClt hBGgt hAG), Or.inr (by exact sigmaSpeedTArith105_051 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_010 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith105_015 hBFeq hBGgt)⟩
        · -- F strictly outranks BD
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_016 hAB hBFgt),
              Or.inr (by exact sigmaSpeedTArith105_017 hBClt hBFgt hAC), Or.inr (by exact sigmaSpeedTArith105_052 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith105_019 hBElt hBFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_020 hFGeq hBFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_021 hBClt hFGeq hBFgt hAG), Or.inr (by exact sigmaSpeedTArith105_052 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith105_019 hBElt hBFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_022 hBFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_023 hBClt hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_053 hBDeq hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_025 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
      · -- E ties BD
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
                  Or.inr hBClt, Or.inr hmBFlt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBDEG ⟨hA, hBne, hDne, hEne, hGne, hBDeq,
                  hBEeq, hmBGeq, Or.inr hBClt, Or.inr hmBFlt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBDEF ⟨hA, hBne, hDne, hEne, hFne, hBDeq,
                  hBEeq, hmBFeq, Or.inr hBClt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBDEFG ⟨hA, hBne, hDne, hEne, hFne, hGne,
                  hBDeq, hBEeq, hmBFeq, hmBGeq, Or.inr hBClt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BDE
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_027 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_027 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BDE
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_007 hBGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_008 hBClt hBGgt hAG), Or.inr (by exact sigmaSpeedTArith105_051 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_028 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_011 hBFlt hBGgt)⟩
        · -- F ties BDE
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_029 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BDEF
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_029 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_001 hBClt), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BDEF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_007 hBGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_008 hBClt hBGgt hAG), Or.inr (by exact sigmaSpeedTArith105_051 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_028 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_015 hBFeq hBGgt)⟩
        · -- F strictly outranks BDE
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_030 hBEeq hBFgt hAE),
              Or.inr (by exact sigmaSpeedTArith105_031 hBClt hBEeq hBFgt hAE), Or.inr (by exact sigmaSpeedTArith105_052 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith105_032 hBEeq hBFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_020 hFGeq hBFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_021 hBClt hFGeq hBFgt hAG), Or.inr (by exact sigmaSpeedTArith105_052 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith105_032 hBEeq hBFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_022 hBFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_023 hBClt hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_053 hBDeq hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_033 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
      · -- E strictly outranks BD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith105_034 hBClt hBEgt),
              Or.inr (by exact sigmaSpeedTArith105_054 hBEgt hBDeq), Or.inr hEFlt, Or.inr hEGlt⟩
          · -- G ties E
            exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
              Or.inr (by exact sigmaSpeedTArith105_034 hBClt hBEgt), Or.inr (by exact sigmaSpeedTArith105_054 hBEgt hBDeq), Or.inr hEFlt⟩
          · -- G strictly outranks E
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_036 hBEgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_037 hBClt hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_055 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_039 hEFlt hEGgt)⟩
        · -- F ties E
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
              Or.inr (by exact sigmaSpeedTArith105_034 hBClt hBEgt), Or.inr (by exact sigmaSpeedTArith105_054 hBEgt hBDeq), Or.inr hEGlt⟩
          · -- G ties EF
            exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
              Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith105_034 hBClt hBEgt), Or.inr (by exact sigmaSpeedTArith105_054 hBEgt hBDeq)⟩
          · -- G strictly outranks EF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_036 hBEgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_037 hBClt hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_055 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_040 hEFeq hEGgt)⟩
        · -- F strictly outranks E
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_041 hBEgt hEFgt hAE),
              Or.inr (by exact sigmaSpeedTArith105_042 hBClt hBEgt hEFgt hAE), Or.inr (by exact sigmaSpeedTArith105_056 hBEgt hBDeq hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_044 hFGeq hBEgt hEFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_045 hBClt hFGeq hBEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith105_056 hBEgt hBDeq hEFgt), Or.inr hEFgt⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_046 hBEgt hEFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_047 hBClt hBEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_057 hBEgt hBDeq hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_049 hEFgt hFGgt), Or.inr hFGgt⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith105_058 hBClt hBDgt),
              Or.inr hDElt, Or.inr hDFlt, Or.inr hDGlt⟩
          · -- G ties D
            exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
              Or.inr (by exact sigmaSpeedTArith105_058 hBClt hBDgt), Or.inr hDElt, Or.inr hDFlt⟩
          · -- G strictly outranks D
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_059 hDGgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_060 hBClt hDGgt hBDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_061 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith105_062 hDGgt hDFlt)⟩
        · -- F ties D
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
              Or.inr (by exact sigmaSpeedTArith105_058 hBClt hBDgt), Or.inr hDElt, Or.inr hDGlt⟩
          · -- G ties DF
            exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
              Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith105_058 hBClt hBDgt), Or.inr hDElt⟩
          · -- G strictly outranks DF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_059 hDGgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_060 hBClt hDGgt hBDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_061 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith105_063 hDGgt hDFeq)⟩
        · -- F strictly outranks D
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_064 hAF hBDgt hDFgt),
              Or.inr (by exact sigmaSpeedTArith105_065 hBClt hAF hBDgt hDFgt), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_066 hDElt hDFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_067 hFGeq hBDgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_068 hBClt hFGeq hBDgt hDFgt hAG), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_066 hDElt hDFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_069 hFGgt hBDgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_070 hBClt hFGgt hBDgt hDFgt hAG), Or.inr (by exact sigmaSpeedTArith105_071 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith105_072 hDElt hFGgt hDFgt), Or.inr hFGgt⟩
      · -- E ties D
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
              Or.inr (by exact sigmaSpeedTArith105_058 hBClt hBDgt), Or.inr hDFlt, Or.inr hDGlt⟩
          · -- G ties DE
            exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
              Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith105_058 hBClt hBDgt), Or.inr hDFlt⟩
          · -- G strictly outranks DE
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_059 hDGgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_060 hBClt hDGgt hBDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_073 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith105_062 hDGgt hDFlt)⟩
        · -- F ties DE
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
              Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith105_058 hBClt hBDgt), Or.inr hDGlt⟩
          · -- G ties DEF
            exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
              hDGeq, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith105_058 hBClt hBDgt)⟩
          · -- G strictly outranks DEF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_059 hDGgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_060 hBClt hDGgt hBDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_073 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith105_063 hDGgt hDFeq)⟩
        · -- F strictly outranks DE
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_064 hAF hBDgt hDFgt),
              Or.inr (by exact sigmaSpeedTArith105_065 hBClt hAF hBDgt hDFgt), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_074 hDEeq hDFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_067 hFGeq hBDgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_068 hBClt hFGeq hBDgt hDFgt hAG), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_074 hDEeq hDFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_069 hFGgt hBDgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_070 hBClt hFGgt hBDgt hDFgt hAG), Or.inr (by exact sigmaSpeedTArith105_071 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith105_075 hDEeq hFGgt hDFgt), Or.inr hFGgt⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith105_076 hDEgt hBDgt),
              Or.inr (by exact sigmaSpeedTArith105_077 hBClt hDEgt hBDgt), Or.inr hDEgt, Or.inr hEFlt, Or.inr hEGlt⟩
          · -- G ties E
            exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith105_076 hDEgt hBDgt),
              Or.inr (by exact sigmaSpeedTArith105_077 hBClt hDEgt hBDgt), Or.inr hDEgt, Or.inr hEFlt⟩
          · -- G strictly outranks E
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_078 hDEgt hBDgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_079 hBClt hDEgt hBDgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_080 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_039 hEFlt hEGgt)⟩
        · -- F ties E
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith105_076 hDEgt hBDgt),
              Or.inr (by exact sigmaSpeedTArith105_077 hBClt hDEgt hBDgt), Or.inr hDEgt, Or.inr hEGlt⟩
          · -- G ties EF
            exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
              Or.inr (by exact sigmaSpeedTArith105_076 hDEgt hBDgt), Or.inr (by exact sigmaSpeedTArith105_077 hBClt hDEgt hBDgt), Or.inr hDEgt⟩
          · -- G strictly outranks EF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_078 hDEgt hBDgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_079 hBClt hDEgt hBDgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_080 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_040 hEFeq hEGgt)⟩
        · -- F strictly outranks E
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_081 hDEgt hEFgt hBDgt hAE),
              Or.inr (by exact sigmaSpeedTArith105_082 hBClt hDEgt hEFgt hBDgt hAE), Or.inr (by exact sigmaSpeedTArith105_083 hDEgt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_084 hFGeq hDEgt hEFgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_085 hBClt hFGeq hDEgt hEFgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith105_083 hDEgt hEFgt), Or.inr hEFgt⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_086 hDEgt hEFgt hFGgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_087 hBClt hDEgt hEFgt hFGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith105_088 hDEgt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_049 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
                  Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
                  Or.inr hBDlt, Or.inr hBElt, Or.inr hmBFlt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
                  Or.inr hBDlt, Or.inr hBElt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCFG ⟨hA, hBne, hCne, hFne, hGne, hBCeq,
                  hmBFeq, hmBGeq, Or.inr hBDlt, Or.inr hBElt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BC
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_090 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_090 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BC
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_091 hBCeq hBGgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_092 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith105_009 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith105_010 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith105_011 hBFlt hBGgt)⟩
        · -- F ties BC
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_093 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BCF
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_093 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BCF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_091 hBCeq hBGgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_092 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith105_009 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith105_010 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith105_015 hBFeq hBGgt)⟩
        · -- F strictly outranks BC
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_094 hBCeq hBFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_095 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith105_018 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith105_019 hBElt hBFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_094 hBCeq hBFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_095 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith105_018 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith105_019 hBElt hBFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_022 hBFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_096 hBCeq hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_024 hBDlt hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_025 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
      · -- E ties BC
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
                  Or.inr hBDlt, Or.inr hmBFlt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCEG ⟨hA, hBne, hCne, hEne, hGne, hBCeq,
                  hBEeq, hmBGeq, Or.inr hBDlt, Or.inr hmBFlt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCEF ⟨hA, hBne, hCne, hEne, hFne, hBCeq,
                  hBEeq, hmBFeq, Or.inr hBDlt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCEFG ⟨hA, hBne, hCne, hEne, hFne, hGne,
                  hBCeq, hBEeq, hmBFeq, hmBGeq, Or.inr hBDlt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BCE
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_090 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_090 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BCE
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_091 hBCeq hBGgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_092 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith105_009 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith105_028 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_011 hBFlt hBGgt)⟩
        · -- F ties BCE
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_093 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BCEF
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_093 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_002 hBDlt), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BCEF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_091 hBCeq hBGgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_092 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith105_009 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith105_028 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_015 hBFeq hBGgt)⟩
        · -- F strictly outranks BCE
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_094 hBCeq hBFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_095 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith105_018 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith105_032 hBEeq hBFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_094 hBCeq hBFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_095 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith105_018 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith105_032 hBEeq hBFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_022 hBFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_096 hBCeq hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_024 hBDlt hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_033 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
      · -- E strictly outranks BC
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith105_097 hBCeq hBEgt),
              Or.inr (by exact sigmaSpeedTArith105_035 hBEgt hBDlt), Or.inr hEFlt, Or.inr hEGlt⟩
          · -- G ties E
            exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
              Or.inr (by exact sigmaSpeedTArith105_097 hBCeq hBEgt), Or.inr (by exact sigmaSpeedTArith105_035 hBEgt hBDlt), Or.inr hEFlt⟩
          · -- G strictly outranks E
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_036 hBEgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_098 hBCeq hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_038 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_039 hEFlt hEGgt)⟩
        · -- F ties E
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
              Or.inr (by exact sigmaSpeedTArith105_097 hBCeq hBEgt), Or.inr (by exact sigmaSpeedTArith105_035 hBEgt hBDlt), Or.inr hEGlt⟩
          · -- G ties EF
            exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
              Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith105_097 hBCeq hBEgt), Or.inr (by exact sigmaSpeedTArith105_035 hBEgt hBDlt)⟩
          · -- G strictly outranks EF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_036 hBEgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_098 hBCeq hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_038 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_040 hEFeq hEGgt)⟩
        · -- F strictly outranks E
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_099 hBCeq hBEgt hEFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_100 hBCeq hBEgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith105_043 hBEgt hBDlt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_044 hFGeq hBEgt hEFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_101 hBCeq hFGeq hBEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith105_043 hBEgt hBDlt hEFgt), Or.inr hEFgt⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_046 hBEgt hEFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_102 hBCeq hBEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_048 hBEgt hBDlt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_049 hEFgt hFGgt), Or.inr hFGgt⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
                  Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCDG ⟨hA, hBne, hCne, hDne, hGne, hBCeq,
                  hBDeq, hmBGeq, Or.inr hBElt, Or.inr hmBFlt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCDF ⟨hA, hBne, hCne, hDne, hFne, hBCeq,
                  hBDeq, hmBFeq, Or.inr hBElt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCDFG ⟨hA, hBne, hCne, hDne, hFne, hGne,
                  hBCeq, hBDeq, hmBFeq, hmBGeq, Or.inr hBElt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BCD
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_090 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_090 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BCD
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_091 hBCeq hBGgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_092 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith105_051 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_010 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith105_011 hBFlt hBGgt)⟩
        · -- F ties BCD
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_093 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BCDF
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_093 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_003 hBElt), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BCDF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_091 hBCeq hBGgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_092 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith105_051 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_010 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith105_015 hBFeq hBGgt)⟩
        · -- F strictly outranks BCD
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_094 hBCeq hBFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_095 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith105_052 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith105_019 hBElt hBFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_094 hBCeq hBFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_095 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith105_052 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith105_019 hBElt hBFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_022 hBFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_096 hBCeq hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_053 hBDeq hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_025 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
      · -- E ties BCD
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCDE ⟨hA, hBne, hCne, hDne, hEne, hBCeq,
                  hBDeq, hBEeq, Or.inr hmBFlt, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCDEG ⟨hA, hBne, hCne, hDne, hEne, hGne,
                  hBCeq, hBDeq, hBEeq, hmBGeq, Or.inr hmBFlt⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
              · -- B³ beats the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCDEF ⟨hA, hBne, hCne, hDne, hEne, hFne,
                  hBCeq, hBDeq, hBEeq, hmBFeq, Or.inr hmBGlt⟩
              · -- G ties B on the mixed monomial BG
                exact QuarticSigmaSupportCone810.sigmaBCDEFG ⟨hA, hBne, hCne, hDne, hEne, hFne,
                  hGne, hBCeq, hBDeq, hBEeq, hmBFeq, hmBGeq⟩
              · -- the mixed monomial BG strictly beats B³ : residual cone
                exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith105_000 hBGlt),
                  Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BCDE
            rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
            · -- B³ beats the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_090 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- F ties B on the mixed monomial BF
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith105_090 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith105_006 hBGeq),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_004 hBFlt)⟩
            · -- the mixed monomial BF strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith105_004 hBFlt),
                Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BCDE
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_091 hBCeq hBGgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_092 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith105_051 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_028 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_011 hBFlt hBGgt)⟩
        · -- F ties BCDE
          rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
          · -- B strictly outranks G
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_093 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_000 hBGlt)⟩
          · -- G ties BCDEF
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith105_093 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith105_013 hBFeq),
              Or.inr (by exact sigmaSpeedTArith105_089 hBCeq), Or.inr (by exact sigmaSpeedTArith105_050 hBDeq), Or.inr (by exact sigmaSpeedTArith105_026 hBEeq), Or.inr (by exact sigmaSpeedTArith105_006 hBGeq)⟩
          · -- G strictly outranks BCDEF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_091 hBCeq hBGgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_092 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith105_051 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_028 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith105_015 hBFeq hBGgt)⟩
        · -- F strictly outranks BCDE
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_094 hBCeq hBFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_095 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith105_052 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith105_032 hBEeq hBFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_094 hBCeq hBFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_095 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith105_052 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith105_032 hBEeq hBFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_022 hBFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_096 hBCeq hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_053 hBDeq hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_033 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
      · -- E strictly outranks BCD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith105_097 hBCeq hBEgt),
              Or.inr (by exact sigmaSpeedTArith105_054 hBEgt hBDeq), Or.inr hEFlt, Or.inr hEGlt⟩
          · -- G ties E
            exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
              Or.inr (by exact sigmaSpeedTArith105_097 hBCeq hBEgt), Or.inr (by exact sigmaSpeedTArith105_054 hBEgt hBDeq), Or.inr hEFlt⟩
          · -- G strictly outranks E
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_036 hBEgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_098 hBCeq hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_055 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_039 hEFlt hEGgt)⟩
        · -- F ties E
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
              Or.inr (by exact sigmaSpeedTArith105_097 hBCeq hBEgt), Or.inr (by exact sigmaSpeedTArith105_054 hBEgt hBDeq), Or.inr hEGlt⟩
          · -- G ties EF
            exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
              Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith105_097 hBCeq hBEgt), Or.inr (by exact sigmaSpeedTArith105_054 hBEgt hBDeq)⟩
          · -- G strictly outranks EF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_036 hBEgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_098 hBCeq hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_055 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_040 hEFeq hEGgt)⟩
        · -- F strictly outranks E
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_099 hBCeq hBEgt hEFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_100 hBCeq hBEgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith105_056 hBEgt hBDeq hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_044 hFGeq hBEgt hEFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_101 hBCeq hFGeq hBEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith105_056 hBEgt hBDeq hEFgt), Or.inr hEFgt⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_046 hBEgt hEFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_102 hBCeq hBEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_057 hBEgt hBDeq hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_049 hEFgt hFGgt), Or.inr hFGgt⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith105_103 hBCeq hBDgt),
              Or.inr hDElt, Or.inr hDFlt, Or.inr hDGlt⟩
          · -- G ties D
            exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
              Or.inr (by exact sigmaSpeedTArith105_103 hBCeq hBDgt), Or.inr hDElt, Or.inr hDFlt⟩
          · -- G strictly outranks D
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_059 hDGgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_104 hBCeq hDGgt hBDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_061 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith105_062 hDGgt hDFlt)⟩
        · -- F ties D
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
              Or.inr (by exact sigmaSpeedTArith105_103 hBCeq hBDgt), Or.inr hDElt, Or.inr hDGlt⟩
          · -- G ties DF
            exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
              Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith105_103 hBCeq hBDgt), Or.inr hDElt⟩
          · -- G strictly outranks DF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_059 hDGgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_104 hBCeq hDGgt hBDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_061 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith105_063 hDGgt hDFeq)⟩
        · -- F strictly outranks D
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_064 hAF hBDgt hDFgt),
              Or.inr (by exact sigmaSpeedTArith105_105 hBCeq hAF hBDgt hDFgt), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_066 hDElt hDFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_067 hFGeq hBDgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_106 hBCeq hFGeq hBDgt hDFgt hAG), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_066 hDElt hDFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_069 hFGgt hBDgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_107 hBCeq hFGgt hBDgt hDFgt hAG), Or.inr (by exact sigmaSpeedTArith105_071 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith105_072 hDElt hFGgt hDFgt), Or.inr hFGgt⟩
      · -- E ties D
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
              Or.inr (by exact sigmaSpeedTArith105_103 hBCeq hBDgt), Or.inr hDFlt, Or.inr hDGlt⟩
          · -- G ties DE
            exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
              Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith105_103 hBCeq hBDgt), Or.inr hDFlt⟩
          · -- G strictly outranks DE
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_059 hDGgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_104 hBCeq hDGgt hBDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_073 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith105_062 hDGgt hDFlt)⟩
        · -- F ties DE
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
              Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith105_103 hBCeq hBDgt), Or.inr hDGlt⟩
          · -- G ties DEF
            exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
              hDGeq, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith105_103 hBCeq hBDgt)⟩
          · -- G strictly outranks DEF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_059 hDGgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_104 hBCeq hDGgt hBDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_073 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith105_063 hDGgt hDFeq)⟩
        · -- F strictly outranks DE
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_064 hAF hBDgt hDFgt),
              Or.inr (by exact sigmaSpeedTArith105_105 hBCeq hAF hBDgt hDFgt), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_074 hDEeq hDFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_067 hFGeq hBDgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_106 hBCeq hFGeq hBDgt hDFgt hAG), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_074 hDEeq hDFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_069 hFGgt hBDgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_107 hBCeq hFGgt hBDgt hDFgt hAG), Or.inr (by exact sigmaSpeedTArith105_071 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith105_075 hDEeq hFGgt hDFgt), Or.inr hFGgt⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith105_076 hDEgt hBDgt),
              Or.inr (by exact sigmaSpeedTArith105_108 hBCeq hDEgt hBDgt), Or.inr hDEgt, Or.inr hEFlt, Or.inr hEGlt⟩
          · -- G ties E
            exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith105_076 hDEgt hBDgt),
              Or.inr (by exact sigmaSpeedTArith105_108 hBCeq hDEgt hBDgt), Or.inr hDEgt, Or.inr hEFlt⟩
          · -- G strictly outranks E
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_078 hDEgt hBDgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_109 hBCeq hDEgt hBDgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_080 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_039 hEFlt hEGgt)⟩
        · -- F ties E
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith105_076 hDEgt hBDgt),
              Or.inr (by exact sigmaSpeedTArith105_108 hBCeq hDEgt hBDgt), Or.inr hDEgt, Or.inr hEGlt⟩
          · -- G ties EF
            exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
              Or.inr (by exact sigmaSpeedTArith105_076 hDEgt hBDgt), Or.inr (by exact sigmaSpeedTArith105_108 hBCeq hDEgt hBDgt), Or.inr hDEgt⟩
          · -- G strictly outranks EF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_078 hDEgt hBDgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_109 hBCeq hDEgt hBDgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_080 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_040 hEFeq hEGgt)⟩
        · -- F strictly outranks E
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_081 hDEgt hEFgt hBDgt hAE),
              Or.inr (by exact sigmaSpeedTArith105_110 hBCeq hDEgt hEFgt hBDgt hAE), Or.inr (by exact sigmaSpeedTArith105_083 hDEgt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_084 hFGeq hDEgt hEFgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_111 hBCeq hFGeq hDEgt hEFgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith105_083 hDEgt hEFgt), Or.inr hEFgt⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_086 hDEgt hEFgt hFGgt hBDgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_112 hBCeq hDEgt hEFgt hFGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith105_088 hDEgt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_049 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
          · -- C strictly outranks G
            rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
            · -- C³ beats the mixed monomial CF
              rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
              · -- C³ beats the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
                  Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
              · -- G ties C on the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
                  Or.inr hCDlt, Or.inr hCElt, Or.inr hmCFlt⟩
              · -- the mixed monomial CG strictly beats C³ : residual cone
                exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith105_113 hCGlt),
                  Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- F ties C on the mixed monomial CF
              rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
              · -- C³ beats the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
                  Or.inr hCDlt, Or.inr hCElt, Or.inr hmCGlt⟩
              · -- G ties C on the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
                  Or.inr hBCgt, Or.inr hCDlt, Or.inr hCElt⟩
              · -- the mixed monomial CG strictly beats C³ : residual cone
                exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith105_113 hCGlt),
                  Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- the mixed monomial CF strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith105_117 hCFlt),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_113 hCGlt)⟩
          · -- G ties C
            rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
            · -- C³ beats the mixed monomial CF
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith105_118 hCGeq hAC), (by exact sigmaSpeedTArith105_119 hCGeq),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- F ties C on the mixed monomial CF
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith105_118 hCGeq hAC), (by exact sigmaSpeedTArith105_119 hCGeq),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- the mixed monomial CF strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith105_117 hCFlt),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_119 hCGeq)⟩
          · -- G strictly outranks C
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_120 hCGgt hBCgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_121 hCGgt hAC), Or.inr (by exact sigmaSpeedTArith105_122 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith105_123 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith105_124 hCGgt hCFlt)⟩
        · -- F ties C
          rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
          · -- C strictly outranks G
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith105_125 hCFeq hAC), (by exact sigmaSpeedTArith105_126 hCFeq),
              Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_113 hCGlt)⟩
          · -- G ties CF
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith105_125 hCFeq hAC), (by exact sigmaSpeedTArith105_126 hCFeq),
              Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_119 hCGeq)⟩
          · -- G strictly outranks CF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_120 hCGgt hBCgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_121 hCGgt hAC), Or.inr (by exact sigmaSpeedTArith105_122 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith105_123 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith105_127 hCGgt hCFeq)⟩
        · -- F strictly outranks C
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_128 hBCgt hCFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_129 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith105_130 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith105_131 hCElt hCFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_128 hBCgt hCFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_129 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith105_130 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith105_131 hCElt hCFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_132 hBCgt hFGgt hCFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_133 hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith105_134 hCDlt hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith105_135 hCElt hFGgt hCFgt), Or.inr hFGgt⟩
      · -- E ties C
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
          · -- C strictly outranks G
            rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
            · -- C³ beats the mixed monomial CF
              rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
              · -- C³ beats the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
                  Or.inr hCDlt, Or.inr hmCFlt, Or.inr hmCGlt⟩
              · -- G ties C on the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
                  Or.inr hBCgt, Or.inr hCDlt, Or.inr hmCFlt⟩
              · -- the mixed monomial CG strictly beats C³ : residual cone
                exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith105_113 hCGlt),
                  Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- F ties C on the mixed monomial CF
              rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
              · -- C³ beats the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
                  Or.inr hBCgt, Or.inr hCDlt, Or.inr hmCGlt⟩
              · -- G ties C on the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCEFG ⟨hA, hCne, hEne, hFne, hGne, hCEeq,
                  hmCFeq, hmCGeq, Or.inr hBCgt, Or.inr hCDlt⟩
              · -- the mixed monomial CG strictly beats C³ : residual cone
                exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith105_113 hCGlt),
                  Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- the mixed monomial CF strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith105_117 hCFlt),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_113 hCGlt)⟩
          · -- G ties CE
            rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
            · -- C³ beats the mixed monomial CF
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith105_118 hCGeq hAC), (by exact sigmaSpeedTArith105_119 hCGeq),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- F ties C on the mixed monomial CF
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith105_118 hCGeq hAC), (by exact sigmaSpeedTArith105_119 hCGeq),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- the mixed monomial CF strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith105_117 hCFlt),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_119 hCGeq)⟩
          · -- G strictly outranks CE
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_120 hCGgt hBCgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_121 hCGgt hAC), Or.inr (by exact sigmaSpeedTArith105_122 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith105_137 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith105_124 hCGgt hCFlt)⟩
        · -- F ties CE
          rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
          · -- C strictly outranks G
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith105_125 hCFeq hAC), (by exact sigmaSpeedTArith105_126 hCFeq),
              Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_113 hCGlt)⟩
          · -- G ties CEF
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith105_125 hCFeq hAC), (by exact sigmaSpeedTArith105_126 hCFeq),
              Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_115 hCDlt), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_119 hCGeq)⟩
          · -- G strictly outranks CEF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_120 hCGgt hBCgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_121 hCGgt hAC), Or.inr (by exact sigmaSpeedTArith105_122 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith105_137 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith105_127 hCGgt hCFeq)⟩
        · -- F strictly outranks CE
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_128 hBCgt hCFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_129 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith105_130 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith105_138 hCEeq hCFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_128 hBCgt hCFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_129 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith105_130 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith105_138 hCEeq hCFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_132 hBCgt hFGgt hCFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_133 hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith105_134 hCDlt hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith105_139 hCEeq hFGgt hCFgt), Or.inr hFGgt⟩
      · -- E strictly outranks C
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith105_140 hCEgt hBCgt), Or.inr hCEgt,
              Or.inr (by exact sigmaSpeedTArith105_141 hCEgt hCDlt), Or.inr hEFlt, Or.inr hEGlt⟩
          · -- G ties E
            exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith105_140 hCEgt hBCgt),
              Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith105_141 hCEgt hCDlt), Or.inr hEFlt⟩
          · -- G strictly outranks E
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_142 hCEgt hBCgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_143 hCEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_144 hCEgt hCDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_039 hEFlt hEGgt)⟩
        · -- F ties E
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith105_140 hCEgt hBCgt),
              Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith105_141 hCEgt hCDlt), Or.inr hEGlt⟩
          · -- G ties EF
            exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
              Or.inr (by exact sigmaSpeedTArith105_140 hCEgt hBCgt), Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith105_141 hCEgt hCDlt)⟩
          · -- G strictly outranks EF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_142 hCEgt hBCgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_143 hCEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_144 hCEgt hCDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_040 hEFeq hEGgt)⟩
        · -- F strictly outranks E
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_145 hCEgt hBCgt hEFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_146 hCEgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith105_147 hCEgt hCDlt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_148 hFGeq hCEgt hBCgt hEFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_149 hFGeq hCEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith105_147 hCEgt hCDlt hEFgt), Or.inr hEFgt⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_150 hCEgt hBCgt hEFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_151 hCEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_152 hCEgt hCDlt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_049 hEFgt hFGgt), Or.inr hFGgt⟩
    · -- D ties C
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
          · -- C strictly outranks G
            rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
            · -- C³ beats the mixed monomial CF
              rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
              · -- C³ beats the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
                  Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
              · -- G ties C on the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
                  Or.inr hBCgt, Or.inr hCElt, Or.inr hmCFlt⟩
              · -- the mixed monomial CG strictly beats C³ : residual cone
                exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith105_113 hCGlt),
                  Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- F ties C on the mixed monomial CF
              rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
              · -- C³ beats the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
                  Or.inr hBCgt, Or.inr hCElt, Or.inr hmCGlt⟩
              · -- G ties C on the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCDFG ⟨hA, hCne, hDne, hFne, hGne, hCDeq,
                  hmCFeq, hmCGeq, Or.inr hBCgt, Or.inr hCElt⟩
              · -- the mixed monomial CG strictly beats C³ : residual cone
                exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith105_113 hCGlt),
                  Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- the mixed monomial CF strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith105_117 hCFlt),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_113 hCGlt)⟩
          · -- G ties CD
            rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
            · -- C³ beats the mixed monomial CF
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith105_118 hCGeq hAC), (by exact sigmaSpeedTArith105_119 hCGeq),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- F ties C on the mixed monomial CF
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith105_118 hCGeq hAC), (by exact sigmaSpeedTArith105_119 hCGeq),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- the mixed monomial CF strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith105_117 hCFlt),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_119 hCGeq)⟩
          · -- G strictly outranks CD
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_120 hCGgt hBCgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_121 hCGgt hAC), Or.inr (by exact sigmaSpeedTArith105_154 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith105_123 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith105_124 hCGgt hCFlt)⟩
        · -- F ties CD
          rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
          · -- C strictly outranks G
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith105_125 hCFeq hAC), (by exact sigmaSpeedTArith105_126 hCFeq),
              Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_113 hCGlt)⟩
          · -- G ties CDF
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith105_125 hCFeq hAC), (by exact sigmaSpeedTArith105_126 hCFeq),
              Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_116 hCElt), Or.inr (by exact sigmaSpeedTArith105_119 hCGeq)⟩
          · -- G strictly outranks CDF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_120 hCGgt hBCgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_121 hCGgt hAC), Or.inr (by exact sigmaSpeedTArith105_154 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith105_123 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith105_127 hCGgt hCFeq)⟩
        · -- F strictly outranks CD
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_128 hBCgt hCFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_129 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith105_155 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith105_131 hCElt hCFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_128 hBCgt hCFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_129 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith105_155 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith105_131 hCElt hCFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_132 hBCgt hFGgt hCFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_133 hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith105_156 hCDeq hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith105_135 hCElt hFGgt hCFgt), Or.inr hFGgt⟩
      · -- E ties CD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
          · -- C strictly outranks G
            rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
            · -- C³ beats the mixed monomial CF
              rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
              · -- C³ beats the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
                  Or.inr hBCgt, Or.inr hmCFlt, Or.inr hmCGlt⟩
              · -- G ties C on the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCDEG ⟨hA, hCne, hDne, hEne, hGne, hCDeq,
                  hCEeq, hmCGeq, Or.inr hBCgt, Or.inr hmCFlt⟩
              · -- the mixed monomial CG strictly beats C³ : residual cone
                exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith105_113 hCGlt),
                  Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- F ties C on the mixed monomial CF
              rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
              · -- C³ beats the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCDEF ⟨hA, hCne, hDne, hEne, hFne, hCDeq,
                  hCEeq, hmCFeq, Or.inr hBCgt, Or.inr hmCGlt⟩
              · -- G ties C on the mixed monomial CG
                exact QuarticSigmaSupportCone810.sigmaCDEFG ⟨hA, hCne, hDne, hEne, hFne, hGne,
                  hCDeq, hCEeq, hmCFeq, hmCGeq, Or.inr hBCgt⟩
              · -- the mixed monomial CG strictly beats C³ : residual cone
                exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith105_113 hCGlt),
                  Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- the mixed monomial CF strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith105_117 hCFlt),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_113 hCGlt)⟩
          · -- G ties CDE
            rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
            · -- C³ beats the mixed monomial CF
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith105_118 hCGeq hAC), (by exact sigmaSpeedTArith105_119 hCGeq),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- F ties C on the mixed monomial CF
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith105_118 hCGeq hAC), (by exact sigmaSpeedTArith105_119 hCGeq),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_117 hCFlt)⟩
            · -- the mixed monomial CF strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith105_117 hCFlt),
                Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_119 hCGeq)⟩
          · -- G strictly outranks CDE
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_120 hCGgt hBCgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_121 hCGgt hAC), Or.inr (by exact sigmaSpeedTArith105_154 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith105_137 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith105_124 hCGgt hCFlt)⟩
        · -- F ties CDE
          rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
          · -- C strictly outranks G
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith105_125 hCFeq hAC), (by exact sigmaSpeedTArith105_126 hCFeq),
              Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_113 hCGlt)⟩
          · -- G ties CDEF
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith105_125 hCFeq hAC), (by exact sigmaSpeedTArith105_126 hCFeq),
              Or.inr (by exact sigmaSpeedTArith105_114 hBCgt), Or.inr (by exact sigmaSpeedTArith105_153 hCDeq), Or.inr (by exact sigmaSpeedTArith105_136 hCEeq), Or.inr (by exact sigmaSpeedTArith105_119 hCGeq)⟩
          · -- G strictly outranks CDEF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_120 hCGgt hBCgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_121 hCGgt hAC), Or.inr (by exact sigmaSpeedTArith105_154 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith105_137 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith105_127 hCGgt hCFeq)⟩
        · -- F strictly outranks CDE
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_128 hBCgt hCFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_129 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith105_155 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith105_138 hCEeq hCFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_128 hBCgt hCFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_129 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith105_155 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith105_138 hCEeq hCFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_132 hBCgt hFGgt hCFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_133 hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith105_156 hCDeq hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith105_139 hCEeq hFGgt hCFgt), Or.inr hFGgt⟩
      · -- E strictly outranks CD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith105_140 hCEgt hBCgt), Or.inr hCEgt,
              Or.inr (by exact sigmaSpeedTArith105_157 hCEgt hCDeq), Or.inr hEFlt, Or.inr hEGlt⟩
          · -- G ties E
            exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith105_140 hCEgt hBCgt),
              Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith105_157 hCEgt hCDeq), Or.inr hEFlt⟩
          · -- G strictly outranks E
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_142 hCEgt hBCgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_143 hCEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_158 hCEgt hCDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_039 hEFlt hEGgt)⟩
        · -- F ties E
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith105_140 hCEgt hBCgt),
              Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith105_157 hCEgt hCDeq), Or.inr hEGlt⟩
          · -- G ties EF
            exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
              Or.inr (by exact sigmaSpeedTArith105_140 hCEgt hBCgt), Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith105_157 hCEgt hCDeq)⟩
          · -- G strictly outranks EF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_142 hCEgt hBCgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_143 hCEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_158 hCEgt hCDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_040 hEFeq hEGgt)⟩
        · -- F strictly outranks E
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_145 hCEgt hBCgt hEFgt hAC),
              Or.inr (by exact sigmaSpeedTArith105_146 hCEgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith105_159 hCEgt hCDeq hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_148 hFGeq hCEgt hBCgt hEFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_149 hFGeq hCEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith105_159 hCEgt hCDeq hEFgt), Or.inr hEFgt⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_150 hCEgt hBCgt hEFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_151 hCEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_160 hCEgt hCDeq hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_049 hEFgt hFGgt), Or.inr hFGgt⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith105_161 hCDgt hBCgt), Or.inr hCDgt,
              Or.inr hDElt, Or.inr hDFlt, Or.inr hDGlt⟩
          · -- G ties D
            exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr (by exact sigmaSpeedTArith105_161 hCDgt hBCgt),
              Or.inr hCDgt, Or.inr hDElt, Or.inr hDFlt⟩
          · -- G strictly outranks D
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_162 hDGgt hCDgt hBCgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_163 hDGgt hCDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_061 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith105_062 hDGgt hDFlt)⟩
        · -- F ties D
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr (by exact sigmaSpeedTArith105_161 hCDgt hBCgt),
              Or.inr hCDgt, Or.inr hDElt, Or.inr hDGlt⟩
          · -- G ties DF
            exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
              Or.inr (by exact sigmaSpeedTArith105_161 hCDgt hBCgt), Or.inr hCDgt, Or.inr hDElt⟩
          · -- G strictly outranks DF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_162 hDGgt hCDgt hBCgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_163 hDGgt hCDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_061 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith105_063 hDGgt hDFeq)⟩
        · -- F strictly outranks D
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_164 hAF hCDgt hBCgt hDFgt),
              Or.inr (by exact sigmaSpeedTArith105_165 hAF hCDgt hDFgt), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_066 hDElt hDFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_166 hFGeq hCDgt hBCgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_167 hFGeq hCDgt hDFgt hAG), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_066 hDElt hDFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_168 hCDgt hBCgt hFGgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_169 hCDgt hFGgt hDFgt hAG), Or.inr (by exact sigmaSpeedTArith105_071 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith105_072 hDElt hFGgt hDFgt), Or.inr hFGgt⟩
      · -- E ties D
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr (by exact sigmaSpeedTArith105_161 hCDgt hBCgt),
              Or.inr hCDgt, Or.inr hDFlt, Or.inr hDGlt⟩
          · -- G ties DE
            exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
              Or.inr (by exact sigmaSpeedTArith105_161 hCDgt hBCgt), Or.inr hCDgt, Or.inr hDFlt⟩
          · -- G strictly outranks DE
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_162 hDGgt hCDgt hBCgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_163 hDGgt hCDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_073 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith105_062 hDGgt hDFlt)⟩
        · -- F ties DE
          rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
          · -- D strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
              Or.inr (by exact sigmaSpeedTArith105_161 hCDgt hBCgt), Or.inr hCDgt, Or.inr hDGlt⟩
          · -- G ties DEF
            exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
              hDGeq, Or.inr (by exact sigmaSpeedTArith105_161 hCDgt hBCgt), Or.inr hCDgt⟩
          · -- G strictly outranks DEF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_162 hDGgt hCDgt hBCgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_163 hDGgt hCDgt hAG), Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith105_073 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith105_063 hDGgt hDFeq)⟩
        · -- F strictly outranks DE
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_164 hAF hCDgt hBCgt hDFgt),
              Or.inr (by exact sigmaSpeedTArith105_165 hAF hCDgt hDFgt), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_074 hDEeq hDFgt), Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_166 hFGeq hCDgt hBCgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_167 hFGeq hCDgt hDFgt hAG), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith105_074 hDEeq hDFgt)⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_168 hCDgt hBCgt hFGgt hDFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_169 hCDgt hFGgt hDFgt hAG), Or.inr (by exact sigmaSpeedTArith105_071 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith105_075 hDEeq hFGgt hDFgt), Or.inr hFGgt⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith105_170 hCDgt hBCgt hDEgt),
              Or.inr (by exact sigmaSpeedTArith105_171 hCDgt hDEgt), Or.inr hDEgt, Or.inr hEFlt, Or.inr hEGlt⟩
          · -- G ties E
            exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith105_170 hCDgt hBCgt hDEgt),
              Or.inr (by exact sigmaSpeedTArith105_171 hCDgt hDEgt), Or.inr hDEgt, Or.inr hEFlt⟩
          · -- G strictly outranks E
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_172 hCDgt hBCgt hDEgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_173 hCDgt hDEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_080 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_039 hEFlt hEGgt)⟩
        · -- F ties E
          rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
          · -- E strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith105_170 hCDgt hBCgt hDEgt),
              Or.inr (by exact sigmaSpeedTArith105_171 hCDgt hDEgt), Or.inr hDEgt, Or.inr hEGlt⟩
          · -- G ties EF
            exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
              Or.inr (by exact sigmaSpeedTArith105_170 hCDgt hBCgt hDEgt), Or.inr (by exact sigmaSpeedTArith105_171 hCDgt hDEgt), Or.inr hDEgt⟩
          · -- G strictly outranks EF
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_172 hCDgt hBCgt hDEgt hEGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_173 hCDgt hDEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith105_080 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith105_040 hEFeq hEGgt)⟩
        · -- F strictly outranks E
          rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
          · -- F strictly outranks G
            exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith105_174 hCDgt hBCgt hDEgt hEFgt hAE),
              Or.inr (by exact sigmaSpeedTArith105_175 hCDgt hDEgt hEFgt hAE), Or.inr (by exact sigmaSpeedTArith105_083 hDEgt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
          · -- G ties F
            exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith105_176 hFGeq hCDgt hBCgt hDEgt hEFgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_177 hFGeq hCDgt hDEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith105_083 hDEgt hEFgt), Or.inr hEFgt⟩
          · -- G strictly outranks F
            exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith105_178 hCDgt hBCgt hDEgt hEFgt hFGgt hAG),
              Or.inr (by exact sigmaSpeedTArith105_179 hCDgt hDEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith105_088 hDEgt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith105_049 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  by_cases hBz : B = 0
  · -- B vanishes
    by_cases hCz : C = 0
    · -- C vanishes
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact (quarticSigmaSupportCone810_of_allZero A B C D E F G hA l beta gamma delta epsilon zeta eta theta hjdiv hder hBz hCz hDz hEz hFz hGz).elim
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_G A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_F A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_FG A B C D E F G hA hBz hCz hDz hEz hFz hGz
        · -- E lives
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_E A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_EG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_EF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_EFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_D A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_DG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_DF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_DFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
        · -- E lives
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_DE A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_DEG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_DEF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_DEFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
    · -- C lives
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_C A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_CG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_CF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_CFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
        · -- E lives
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_CE A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_CEG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_CEF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_CEFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_CD A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_CDG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_CDF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_CDFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
        · -- E lives
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_CDE A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_CDEG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_CDEF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_CDEFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
  · -- B lives
    by_cases hCz : C = 0
    · -- C vanishes
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_B A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
        · -- E lives
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BE A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BEG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BEF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BEFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BD A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BDG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BDF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BDFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
        · -- E lives
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BDE A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BDEG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BDEF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BDEFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
    · -- C lives
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BC A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BCG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BCF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BCFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
        · -- E lives
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BCE A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BCEG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BCEF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BCEFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BCD A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BCDG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BCDF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BCDFG A B C D E F G hA hBz hCz hDz hEz hFz hGz
        · -- E lives
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BCDE A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BCDEG A B C D E F G hA hBz hCz hDz hEz hFz hGz
          · -- F lives
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticSigmaSupportCone810_of_live_BCDEF A B C D E F G hA hBz hCz hDz hEz hFz hGz
            · -- G lives
              exact quarticSigmaSupportCone810_of_live_BCDEFG A B C D E F G hA hBz hCz hDz hEz hFz hGz


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 93 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

section QuarticSigmaBands810


set_option maxHeartbeats 64000000 in
theorem quarticSigma_l_band_disjunction
    {l : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaLoadTopL810 A B C D E F G → l = 0) :
    l = 0 ∨
      5 * A.natDegree ≤ 4 * B.natDegree ∨
      7 * A.natDegree ≤ 4 * C.natDegree ∨
      9 * A.natDegree ≤ 4 * D.natDegree ∨
      11 * A.natDegree ≤ 4 * E.natDegree ∨
      13 * A.natDegree ≤ 4 * F.natDegree ∨
      15 * A.natDegree ≤ 4 * G.natDegree := by
  by_cases hB : 4 * B.natDegree < 5 * A.natDegree
  · by_cases hC : 4 * C.natDegree < 7 * A.natDegree
    · by_cases hD : 4 * D.natDegree < 9 * A.natDegree
      · by_cases hE : 4 * E.natDegree < 11 * A.natDegree
        · by_cases hF : 4 * F.natDegree < 13 * A.natDegree
          · by_cases hG : 4 * G.natDegree < 15 * A.natDegree
            · exact Or.inl (hkill ⟨hA, Or.inr hB, Or.inr hC, Or.inr hD,
                Or.inr hE, Or.inr hF, Or.inr hG⟩)
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega


set_option maxHeartbeats 64000000 in
theorem quarticSigma_beta_band_disjunction
    {beta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaLoadTopBeta810 A B C D E F G → beta = 0) :
    beta = 0 ∨
      3 * A.natDegree ≤ 4 * B.natDegree ∨
      5 * A.natDegree ≤ 4 * C.natDegree ∨
      7 * A.natDegree ≤ 4 * D.natDegree ∨
      9 * A.natDegree ≤ 4 * E.natDegree ∨
      11 * A.natDegree ≤ 4 * F.natDegree ∨
      13 * A.natDegree ≤ 4 * G.natDegree := by
  by_cases hB : 4 * B.natDegree < 3 * A.natDegree
  · by_cases hC : 4 * C.natDegree < 5 * A.natDegree
    · by_cases hD : 4 * D.natDegree < 7 * A.natDegree
      · by_cases hE : 4 * E.natDegree < 9 * A.natDegree
        · by_cases hF : 4 * F.natDegree < 11 * A.natDegree
          · by_cases hG : 4 * G.natDegree < 13 * A.natDegree
            · exact Or.inl (hkill ⟨hA, Or.inr hB, Or.inr hC, Or.inr hD,
                Or.inr hE, Or.inr hF, Or.inr hG⟩)
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega


end QuarticSigmaBands810
end Max11DegreeRoutes
end
/-! Part 51 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

section QuarticKappaLadder810


set_option maxHeartbeats 64000000 in
theorem quarticSigma_l_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticKappaLoadTopL810 A B C D E F G)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree = 0) :
    l = 0 := by
  by_contra hl
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG, hBt, hCt, hDt, hEt, hFt, hGt⟩ :=
    quarticKappaLoadTopL810_bounds htop
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (63 / 262144 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead : (kappaQuarticLFace810 l A).natDegree = 5 * A.natDegree := by
    simp only [kappaQuarticLFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroKappaQuarticNoL810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  rw [degreeZeroKappaQuartic810_eq_l_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hkap
  omega


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `l` on the k=3 cone `B`: `7s ≥ 2 a`. -/
def QuarticN2LoadTopL_B810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeB810' A B C D E F G ∧ 14 * B.natDegree ≤ 19 * A.natDegree


end QuarticKappaLadder810
end Max11DegreeRoutes
end
/-! Part 94 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

section QuarticSigmaBands810


set_option maxHeartbeats 64000000 in
theorem quarticSigma_delta_band_disjunction
    {delta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaLoadTopDelta810 A B C D E F G → delta = 0) :
    delta = 0 ∨
      A.natDegree ≤ 4 * B.natDegree ∨
      3 * A.natDegree ≤ 4 * C.natDegree ∨
      5 * A.natDegree ≤ 4 * D.natDegree ∨
      7 * A.natDegree ≤ 4 * E.natDegree ∨
      9 * A.natDegree ≤ 4 * F.natDegree ∨
      11 * A.natDegree ≤ 4 * G.natDegree := by
  by_cases hB : 4 * B.natDegree < A.natDegree
  · by_cases hC : 4 * C.natDegree < 3 * A.natDegree
    · by_cases hD : 4 * D.natDegree < 5 * A.natDegree
      · by_cases hE : 4 * E.natDegree < 7 * A.natDegree
        · by_cases hF : 4 * F.natDegree < 9 * A.natDegree
          · by_cases hG : 4 * G.natDegree < 11 * A.natDegree
            · exact Or.inl (hkill ⟨hA, Or.inr hB, Or.inr hC, Or.inr hD,
                Or.inr hE, Or.inr hF, Or.inr hG⟩)
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega


set_option maxHeartbeats 64000000 in
theorem quarticSigma_zeta_band_disjunction
    {zeta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaLoadTopZeta810 A B C D E F G → zeta = 0) :
    zeta = 0 ∨
      A.natDegree + 4 * B.natDegree ≥ 0 ∨
      A.natDegree ≤ 4 * C.natDegree ∨
      3 * A.natDegree ≤ 4 * D.natDegree ∨
      5 * A.natDegree ≤ 4 * E.natDegree ∨
      7 * A.natDegree ≤ 4 * F.natDegree ∨
      9 * A.natDegree ≤ 4 * G.natDegree := by
  by_cases hB : B = 0
  · by_cases hC : 4 * C.natDegree < A.natDegree
    · by_cases hD : 4 * D.natDegree < 3 * A.natDegree
      · by_cases hE : 4 * E.natDegree < 5 * A.natDegree
        · by_cases hF : 4 * F.natDegree < 7 * A.natDegree
          · by_cases hG : 4 * G.natDegree < 9 * A.natDegree
            · exact Or.inl (hkill ⟨hA, hB, Or.inr hC, Or.inr hD, Or.inr hE,
                Or.inr hF, Or.inr hG⟩)
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    exact Nat.zero_le _


end QuarticSigmaBands810
end Max11DegreeRoutes
end
/-! Part 95 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

section QuarticSigmaLadderAssembly810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]


set_option maxHeartbeats 64000000 in
/-- Honest leftover after File A of the σ-defect ladder.

Closed relative to `quarticConeA810_residual`: the 67-way
`QuarticSigmaSupportCone810` (all-zero leaf killed by
`quarticADominant_allLettersZero_impossible`), the kappa `l`
column implication `QuarticKappaLoadTopL810 → l = 0`, and the
`l` band disjunction of §2.2.  The 63 σ-cones and the four mixed
residual cones `QuarticMixedSigmaCone{BF,BG,CF,CG}810` are not
killed (Files B/C).  Corner H is not closed.  Named unclosable
sub-chamber: `B = 0 ∧ s ≥ 4a ∧ S ⊆ {C,D,E} ∧ γ ≠ 0`.
Next unused row: kappa rest bounds for `β/δ/ζ` and `N₂` kills
on the three k=3 cones, then per-cone letter-face rest bounds.
No finite-root shortcut. -/
theorem normalized810ScaleZero_quarticSigmaResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          QuarticSigmaSupportCone810 A B C D E F G ∧
          (QuarticKappaLoadTopL810 A B C D E F G → l = 0) ∧
          (l = 0 ∨
      5 * A.natDegree ≤ 4 * B.natDegree ∨
      7 * A.natDegree ≤ 4 * C.natDegree ∨
      9 * A.natDegree ≤ 4 * D.natDegree ∨
      11 * A.natDegree ≤ 4 * E.natDegree ∨
      13 * A.natDegree ≤ 4 * F.natDegree ∨
      15 * A.natDegree ≤ 4 * G.natDegree) ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0) ∨
            ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
                E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0)) ∧
          ¬ (B = 0 ∧ D = 0 ∧ F = 0 ∧ 0 < C.natDegree ∧
              2 * E.natDegree < 3 * C.natDegree ∧
              G.natDegree < 2 * C.natDegree) ∧
          ¬ (B = 0 ∧ D = 0 ∧ F = 0 ∧ 0 < E.natDegree ∧
              3 * C.natDegree < 2 * E.natDegree ∧
              3 * G.natDegree < 2 * E.natDegree)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    quarticConeA810_residual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · rcases hA with ⟨hconeA, hconst, hevenC, hevenE⟩
    refine Or.inl ⟨hconeA, ?hexh, ?hl, ?hlB, hconst, hevenC, hevenE⟩
    · exact quarticSigmaSupportCone810_of l beta gamma delta epsilon zeta
        eta theta A B C D E F G hconeA hjdiv hder
    · intro htop
      exact quarticSigma_l_eq_zero l beta gamma delta epsilon zeta eta
        theta A B C D E F G htop hkapDeg
    · exact quarticSigma_l_band_disjunction (l := l) A B C D E F G hconeA
        (fun htop => quarticSigma_l_eq_zero l beta gamma delta epsilon
          zeta eta theta A B C D E F G htop hkapDeg)
  · exact Or.inr hABCDEFG


end QuarticSigmaLadderAssembly810
end Max11DegreeRoutes
end
