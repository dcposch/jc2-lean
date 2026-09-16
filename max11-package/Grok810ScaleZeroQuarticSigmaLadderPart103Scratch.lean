import Grok810ScaleZeroQuarticSigmaLadderPart101Scratch

/-! Part 84 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
private theorem sigmaSpeedTArith103_000
    {a b g : ℕ}
    (h0 : 4 * g < 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_001
    {a b d : ℕ}
    (h0 : 4 * d < a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_002
    {a b e : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_003
    {a b f : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_004
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_005
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_006
    {a b g : ℕ}
    (h0 : 7 * a + 6 * b < 4 * g)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_007
    {a b d g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_008
    {a b e g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_009
    {a b f g : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_010
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 4 * f = 5 * a + 6 * b)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_011
    {a b f : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_012
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_013
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_014
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_015
    {a b d f : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_016
    {a b e f : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_017
    {a b f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_018
    {a b f g : ℕ}
    (h0 : 5 * a + 6 * b < 4 * f)
    (h1 : a + 2 * f < 2 * g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_019
    {a b d f g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_020
    {a b e f g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_021
    {a b e : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_022
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_023
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_024
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * f = 5 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_025
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_026
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_027
    {a b e f g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_028
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_029
    {a b e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_030
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_031
    {a e f g : ℕ}
    (h0 : 2 * f < a + 2 * e)
    (h1 : a + e < g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_032
    {a e f g : ℕ}
    (h0 : 2 * f = a + 2 * e)
    (h1 : a + e < g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_033
    {a b e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_034
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_035
    {a b e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_036
    {a b e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_037
    {a b d e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_038
    {a e f g : ℕ}
    (h0 : a + 2 * e < 2 * f)
    (h1 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_039
    {a b d : ℕ}
    (h0 : 4 * d = a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_040
    {a b d g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_041
    {a b d f : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_042
    {a b d f g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_043
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_044
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_045
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_046
    {a b d e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_047
    {a b d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_048
    {a d e g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_049
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f < a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_050
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f = a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_051
    {a b d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_052
    {a d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_053
    {a b d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_054
    {a b d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_055
    {a d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + d < f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_056
    {a d e f g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_057
    {a d e g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_058
    {a d e f : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_059
    {a d e f g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_060
    {a b d e : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_061
    {a b d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_062
    {a d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_063
    {a b d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 6 * b < 4 * d)
    (h3 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_064
    {a d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_065
    {a b d e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 6 * b < 4 * d)
    (h4 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_066
    {a b d e f g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : a + 6 * b < 4 * d)
    (h4 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_067
    {a d e f g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_068
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : 2 * c ≤ a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_069
    {a b c g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_070
    {a b c : ℕ}
    (h0 : 2 * c = a + 2 * b)
    : 2 * c ≤ a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_071
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_072
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_073
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_074
    {a c g : ℕ}
    (h0 : 2 * g < 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_075
    {a b c : ℕ}
    (h0 : a + 2 * b < 2 * c)
    : a + 2 * b ≤ 2 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_076
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_077
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_078
    {a b c g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * b < 2 * c)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_079
    {a c g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_080
    {a b c f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_081
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 4 * f = 5 * a + 6 * b)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_082
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_083
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_084
    {a c f : ℕ}
    (h0 : 2 * f < a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_085
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_086
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_087
    {a b c f : ℕ}
    (h0 : a + 2 * b < 2 * c)
    (h1 : a + 3 * c < 2 * f)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_088
    {a c f : ℕ}
    (h0 : a + 3 * c < 2 * f)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_089
    {a b c f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : 5 * a + 6 * b < 4 * f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_090
    {a b c f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_091
    {a b c f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_092
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f < a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_093
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f = a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_094
    {a b c f g : ℕ}
    (h0 : a + 2 * b < 2 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_095
    {a c f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 3 * c < 2 * f)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_096
    {a b c e : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_097
    {a b c e : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_098
    {a b c e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_099
    {a b c e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_100
    {a b c e g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_101
    {c e : ℕ}
    (h0 : 2 * e < 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_102
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e < 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_103
    {c e : ℕ}
    (h0 : 2 * e = 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_104
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e = 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_105
    {a b c e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_106
    {a c e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_107
    {a b c e f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a + 6 * b < 4 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_108
    {a b c e f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_109
    {a b c e f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_110
    {a b c e f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_111
    {a c e f : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_112
    {a c e f : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_113
    {a b c e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_114
    {a c e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_115
    {a b c e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : 3 * a + 6 * b < 4 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_116
    {a b c e f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_117
    {a b c e f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : 3 * a + 6 * b < 4 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_118
    {a b c e f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_119
    {a c e f g : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_120
    {a c e f g : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_121
    {a b c e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < 2 * e)
    (h2 : a + 2 * b < 2 * c)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_122
    {a c e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_123
    {a b c e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_124
    {a c e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_125
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 6 * b < 4 * d)
    : 3 * c < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_126
    {a b c d : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 6 * b < 4 * d)
    : 3 * c < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_127
    {a b c d : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    : a + 6 * b < 4 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_128
    {a b c d g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 2 * d < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_129
    {a b c d g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 2 * d < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_130
    {a c d : ℕ}
    (h0 : a + 2 * d < 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_131
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d < 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_132
    {a c d : ℕ}
    (h0 : a + 2 * d = 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_133
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d = 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_134
    {a b c d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_135
    {a c d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : 3 * c < a + 2 * d)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_136
    {a b c d f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_137
    {a b c d f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_138
    {a c d f : ℕ}
    (h0 : a + 2 * d < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_139
    {a c d f : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_140
    {a b c d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : a + d < f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith103_141
    {a c d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
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
              exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt,
                Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz,
                Or.inr hBDlt, Or.inr hBElt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz,
                Or.inr hBDlt, Or.inr hBElt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
                Or.inl hCz, Or.inr hBDlt, Or.inr hBElt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties B
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties B
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_012 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks B
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_019 hBDlt hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_020 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz,
                Or.inr hBDlt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
                Or.inl hCz, Or.inr hBDlt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
                Or.inl hCz, Or.inr hBDlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEFG ⟨hA, hBne, hEne, hFne, hGne, hBEeq,
                hmBFeq, hmBGeq, Or.inl hCz, Or.inr hBDlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BE
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BE
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BEF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_025 hBEeq hBFgt hAE), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_019 hBDlt hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_027 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_028 hBEgt hBDlt), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_028 hBEgt hBDlt), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_030 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_028 hBEgt hBDlt), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr hBEgt, Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_028 hBEgt hBDlt)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_030 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_033 hBEgt hEFgt hAE), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_034 hBEgt hBDlt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_035 hFGeq hBEgt hEFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_034 hBEgt hBDlt hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_036 hBEgt hEFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_037 hBEgt hBDlt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩
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
              exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz,
                Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
                Or.inl hCz, Or.inr hBElt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
                Or.inl hCz, Or.inr hBElt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDFG ⟨hA, hBne, hDne, hFne, hGne, hBDeq,
                hmBFeq, hmBGeq, Or.inl hCz, Or.inr hBElt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BD
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BDF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_012 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_042 hBDeq hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_020 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
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
                Or.inl hCz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDEG ⟨hA, hBne, hDne, hEne, hGne, hBDeq, hBEeq,
                hmBGeq, Or.inl hCz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDEF ⟨hA, hBne, hDne, hEne, hFne, hBDeq, hBEeq,
                hmBFeq, Or.inl hCz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDEFG ⟨hA, hBne, hDne, hEne, hFne, hGne, hBDeq,
                hBEeq, hmBFeq, hmBGeq, Or.inl hCz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BDE
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BDE
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BDEF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BDEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BDE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_025 hBEeq hBFgt hAE), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_042 hBDeq hBFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_027 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E strictly outranks BD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_043 hBEgt hBDeq), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_043 hBEgt hBDeq), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_044 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_043 hBEgt hBDeq), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr hBEgt, Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_043 hBEgt hBDeq)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_044 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_033 hBEgt hEFgt hAE), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_045 hBEgt hBDeq hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_035 hFGeq hBEgt hEFgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_045 hBEgt hBDeq hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_036 hBEgt hEFgt hFGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_046 hBEgt hBDeq hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz,
            Or.inr hDElt, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inl hCz, Or.inr hDElt, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith103_048 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith103_049 hDGgt hDFlt)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inl hCz, Or.inr hDElt, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inr hBDgt, Or.inl hCz, Or.inr hDElt⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith103_048 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith103_050 hDGgt hDFeq)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_051 hAF hBDgt hDFgt), Or.inl hCz,
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith103_052 hDElt hDFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_053 hFGeq hBDgt hDFgt hAG),
            Or.inl hCz, Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith103_052 hDElt hDFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_054 hFGgt hBDgt hDFgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_055 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith103_056 hDElt hFGgt hDFgt), Or.inr hFGgt⟩
    · -- E ties D
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inl hCz, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inr hBDgt, Or.inl hCz, Or.inr hDFlt⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith103_057 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith103_049 hDGgt hDFlt)⟩
      · -- F ties DE
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inr hBDgt, Or.inl hCz, Or.inr hDGlt⟩
        · -- G ties DEF
          exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
            hDGeq, Or.inr hBDgt, Or.inl hCz⟩
        · -- G strictly outranks DEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith103_057 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith103_050 hDGgt hDFeq)⟩
      · -- F strictly outranks DE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_051 hAF hBDgt hDFgt), Or.inl hCz,
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith103_058 hDEeq hDFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_053 hFGeq hBDgt hDFgt hAG),
            Or.inl hCz, Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith103_058 hDEeq hDFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_054 hFGgt hBDgt hDFgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_055 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith103_059 hDEeq hFGgt hDFgt), Or.inr hFGgt⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith103_060 hDEgt hBDgt), Or.inl hCz,
            Or.inr hDEgt, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith103_060 hDEgt hBDgt),
            Or.inl hCz, Or.inr hDEgt, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_061 hDEgt hBDgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_062 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith103_060 hDEgt hBDgt),
            Or.inl hCz, Or.inr hDEgt, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr (by exact sigmaSpeedTArith103_060 hDEgt hBDgt), Or.inl hCz, Or.inr hDEgt⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_061 hDEgt hBDgt hEGgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_062 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_063 hDEgt hEFgt hBDgt hAE), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_064 hDEgt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_065 hFGeq hDEgt hEFgt hBDgt hAG),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith103_064 hDEgt hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_066 hDEgt hEFgt hFGgt hBDgt hAG), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith103_067 hDEgt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BC
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- C ties B
    exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- C strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 85 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BCG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz, Or.inl hEz,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt, Or.inl hDz,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G ties B
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
        Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz, Or.inl hEz,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq, Or.inl hDz,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G ties BC
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
        Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks BC
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz, Or.inl hEz,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt, Or.inl hDz,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G ties C
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
        Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz, Or.inl hEz,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt, Or.inl hDz,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F ties B
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
        Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz, Or.inl hEz,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq, Or.inl hDz,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F ties BC
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
        Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks BC
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz, Or.inl hEz,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt, Or.inl hDz,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F ties C
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
        Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 86 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BCFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz,
              Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
              Or.inl hDz, Or.inl hEz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
              Or.inl hDz, Or.inl hEz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
              Or.inr hBClt, Or.inl hDz, Or.inl hEz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
      · -- G ties B
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
    · -- F ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
      · -- G ties BF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_012 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
      · -- G strictly outranks BF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
    · -- F strictly outranks B
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
          Or.inr (by exact sigmaSpeedTArith103_089 hBClt hFGeq hBFgt hAG), Or.inl hDz, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_090 hBClt hBFgt hFGgt hAG),
          Or.inl hDz, Or.inl hEz, Or.inr hFGgt⟩
  · -- C ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz,
              Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
              Or.inl hDz, Or.inl hEz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
              Or.inl hDz, Or.inl hEz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCFG ⟨hA, hBne, hCne, hFne, hGne, hBCeq, hmBFeq,
              hmBGeq, Or.inl hDz, Or.inl hEz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
      · -- G ties BC
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
      · -- G strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
    · -- F ties BC
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
      · -- G ties BCF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
      · -- G strictly outranks BCF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
    · -- F strictly outranks BC
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC), Or.inl hDz, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_091 hBCeq hBFgt hFGgt hAG),
          Or.inl hDz, Or.inl hEz, Or.inr hFGgt⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz,
              Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
              Or.inl hDz, Or.inl hEz, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
              Or.inl hDz, Or.inl hEz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
              Or.inr hBCgt, Or.inl hDz, Or.inl hEz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
      · -- G ties C
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_092 hCGgt hCFlt)⟩
    · -- F ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
      · -- G ties CF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
      · -- G strictly outranks CF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith103_093 hCGgt hCFeq)⟩
    · -- F strictly outranks C
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
          Or.inl hDz, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC), Or.inl hDz, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_094 hBCgt hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith103_095 hFGgt hCFgt hAG),
          Or.inl hDz, Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz, Or.inr hBElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties B
      exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt, Or.inl hDz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt),
        Or.inl hDz, Or.inl hFz, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz, Or.inr hBElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties BC
      exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq, Or.inl hDz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks BC
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt),
        Or.inl hDz, Or.inl hFz, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz, Or.inr hCElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties C
      exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt, Or.inl hDz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt), Or.inr hCEgt,
        Or.inl hDz, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 87 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BCEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz,
            Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
            Or.inl hDz, Or.inr hBElt, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hFz⟩
      · -- G ties B
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hFz⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inl hFz⟩
    · -- E ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
            Or.inl hDz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
            Or.inr hBClt, Or.inl hDz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hFz⟩
      · -- G ties BE
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hFz⟩
      · -- G strictly outranks BE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inl hFz⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt),
          Or.inl hDz, Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
          Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt), Or.inl hDz, Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_099 hBClt hBEgt hEGgt hAG),
          Or.inl hDz, Or.inr hEGgt, Or.inl hFz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz,
            Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
            Or.inl hDz, Or.inr hBElt, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hFz⟩
      · -- G ties BC
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hFz⟩
      · -- G strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inl hFz⟩
    · -- E ties BC
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
            Or.inl hDz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCEG ⟨hA, hBne, hCne, hEne, hGne, hBCeq, hBEeq,
            hmBGeq, Or.inl hDz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hFz⟩
      · -- G ties BCE
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hFz⟩
      · -- G strictly outranks BCE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inl hFz⟩
    · -- E strictly outranks BC
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt),
          Or.inl hDz, Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
          Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt), Or.inl hDz, Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_100 hBCeq hBEgt hEGgt hAG),
          Or.inl hDz, Or.inr hEGgt, Or.inl hFz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz,
            Or.inr hCElt, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
            Or.inl hDz, Or.inr hCElt, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inl hFz⟩
      · -- G ties C
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inl hFz⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_102 hCGgt hCElt), Or.inl hFz⟩
    · -- E ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
            Or.inl hDz, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
            Or.inr hBCgt, Or.inl hDz, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inl hFz⟩
      · -- G ties CE
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inl hFz⟩
      · -- G strictly outranks CE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_104 hCGgt hCEeq), Or.inl hFz⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt), Or.inr hCEgt,
          Or.inl hDz, Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt),
          Or.inr hCEgt, Or.inl hDz, Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_105 hCEgt hBCgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_106 hCEgt hEGgt hAG),
          Or.inl hDz, Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz,
            Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
            Or.inl hDz, Or.inr hBElt, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hGz⟩
      · -- F ties B
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hGz⟩
      · -- F strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inl hGz⟩
    · -- E ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
            Or.inl hDz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
            Or.inr hBClt, Or.inl hDz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hGz⟩
      · -- F ties BE
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hGz⟩
      · -- F strictly outranks BE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_025 hBEeq hBFgt hAE), Or.inr (by exact sigmaSpeedTArith103_107 hBClt hBEeq hBFgt hAE),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inl hGz⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt),
          Or.inl hDz, Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
          Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt), Or.inl hDz, Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_033 hBEgt hEFgt hAE), Or.inr (by exact sigmaSpeedTArith103_108 hBClt hBEgt hEFgt hAE),
          Or.inl hDz, Or.inr hEFgt, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz,
            Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
            Or.inl hDz, Or.inr hBElt, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hGz⟩
      · -- F ties BC
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inl hGz⟩
      · -- F strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inl hGz⟩
    · -- E ties BC
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
            Or.inl hDz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCEF ⟨hA, hBne, hCne, hEne, hFne, hBCeq, hBEeq,
            hmBFeq, Or.inl hDz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hGz⟩
      · -- F ties BCE
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inl hGz⟩
      · -- F strictly outranks BCE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inl hGz⟩
    · -- E strictly outranks BC
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt),
          Or.inl hDz, Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
          Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt), Or.inl hDz, Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_109 hBCeq hBEgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith103_110 hBCeq hBEgt hEFgt hAC),
          Or.inl hDz, Or.inr hEFgt, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz,
            Or.inr hCElt, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
            Or.inl hDz, Or.inr hCElt, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inl hGz⟩
      · -- F ties C
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inl hGz⟩
      · -- F strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_111 hCElt hCFgt), Or.inl hGz⟩
    · -- E ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
            Or.inl hDz, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
            Or.inr hBCgt, Or.inl hDz, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inl hGz⟩
      · -- F ties CE
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inl hGz⟩
      · -- F strictly outranks CE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_112 hCEeq hCFgt), Or.inl hGz⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt), Or.inr hCEgt,
          Or.inl hDz, Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt),
          Or.inr hCEgt, Or.inl hDz, Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_113 hCEgt hBCgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith103_114 hCEgt hEFgt hAC),
          Or.inl hDz, Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 88 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BCEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
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
              exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz,
                Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
                Or.inl hDz, Or.inr hBElt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
                Or.inl hDz, Or.inr hBElt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
                Or.inr hBClt, Or.inl hDz, Or.inr hBElt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties B
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties B
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_012 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks B
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inr (by exact sigmaSpeedTArith103_089 hBClt hFGeq hBFgt hAG), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_090 hBClt hBFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_020 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
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
                Or.inl hDz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
                Or.inr hBClt, Or.inl hDz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
                Or.inr hBClt, Or.inl hDz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEFG ⟨hA, hBne, hEne, hFne, hGne, hBEeq,
                hmBFeq, hmBGeq, Or.inr hBClt, Or.inl hDz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BE
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_022 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BE
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BEF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_024 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_025 hBEeq hBFgt hAE), Or.inr (by exact sigmaSpeedTArith103_107 hBClt hBEeq hBFgt hAE),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_017 hFGeq hBFgt hAG),
            Or.inr (by exact sigmaSpeedTArith103_089 hBClt hFGeq hBFgt hAG), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_090 hBClt hBFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_027 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt),
            Or.inl hDz, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt), Or.inl hDz, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_099 hBClt hBEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt), Or.inl hDz, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_096 hBClt hBEgt), Or.inl hDz⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_099 hBClt hBEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_033 hBEgt hEFgt hAE), Or.inr (by exact sigmaSpeedTArith103_108 hBClt hBEgt hEFgt hAE),
            Or.inl hDz, Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_035 hFGeq hBEgt hEFgt hAG),
            Or.inr (by exact sigmaSpeedTArith103_115 hBClt hFGeq hBEgt hEFgt hAG), Or.inl hDz, Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_036 hBEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_116 hBClt hBEgt hEFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- C ties B
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
              exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz,
                Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
                Or.inl hDz, Or.inr hBElt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
                Or.inl hDz, Or.inr hBElt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCFG ⟨hA, hBne, hCne, hFne, hGne, hBCeq,
                hmBFeq, hmBGeq, Or.inl hDz, Or.inr hBElt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BC
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BC
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BC
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BCF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_002 hBElt), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BCF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_008 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BC
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_016 hBElt hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_091 hBCeq hBFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_020 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
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
                Or.inl hDz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCEG ⟨hA, hBne, hCne, hEne, hGne, hBCeq, hBEeq,
                hmBGeq, Or.inl hDz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCEF ⟨hA, hBne, hCne, hEne, hFne, hBCeq, hBEeq,
                hmBFeq, Or.inl hDz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCEFG ⟨hA, hBne, hCne, hEne, hFne, hGne, hBCeq,
                hBEeq, hmBFeq, hmBGeq, Or.inl hDz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BCE
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BCE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_009 hBFlt hBGgt)⟩
      · -- F ties BCE
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_000 hBGlt)⟩
        · -- G ties BCEF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_021 hBEeq), Or.inr (by exact sigmaSpeedTArith103_005 hBGeq)⟩
        · -- G strictly outranks BCEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_023 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith103_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BCE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_026 hBEeq hBFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_018 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_091 hBCeq hBFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_027 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
    · -- E strictly outranks BC
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt),
            Or.inl hDz, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt), Or.inl hDz, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_100 hBCeq hBEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt), Or.inl hDz, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith103_097 hBCeq hBEgt), Or.inl hDz⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_029 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_100 hBCeq hBEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_109 hBCeq hBEgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith103_110 hBCeq hBEgt hEFgt hAC),
            Or.inl hDz, Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_035 hFGeq hBEgt hEFgt hAG),
            Or.inr (by exact sigmaSpeedTArith103_117 hBCeq hFGeq hBEgt hEFgt hAG), Or.inl hDz, Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_036 hBEgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_118 hBCeq hBEgt hEFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- C strictly outranks B
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
              exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz,
                Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
                Or.inl hDz, Or.inr hCElt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
                Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
                Or.inl hDz, Or.inr hCElt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
                Or.inr hBCgt, Or.inl hDz, Or.inr hCElt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
                Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
        · -- G ties C
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
        · -- G strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_102 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith103_092 hCGgt hCFlt)⟩
      · -- F ties C
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
        · -- G ties CF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_101 hCElt), Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
        · -- G strictly outranks CF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_102 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith103_093 hCGgt hCFeq)⟩
      · -- F strictly outranks C
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_111 hCElt hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_111 hCElt hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_094 hBCgt hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith103_095 hFGgt hCFgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_119 hCElt hFGgt hCFgt), Or.inr hFGgt⟩
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
                Or.inl hDz, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
                Or.inr hBCgt, Or.inl hDz, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
                Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
                Or.inr hBCgt, Or.inl hDz, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEFG ⟨hA, hCne, hEne, hFne, hGne, hCEeq,
                hmCFeq, hmCGeq, Or.inr hBCgt, Or.inl hDz⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
                Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
        · -- G ties CE
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_084 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
              Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
        · -- G strictly outranks CE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_104 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith103_092 hCGgt hCFlt)⟩
      · -- F ties CE
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_074 hCGlt)⟩
        · -- G ties CEF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_103 hCEeq), Or.inr (by exact sigmaSpeedTArith103_077 hCGeq)⟩
        · -- G strictly outranks CEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_104 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith103_093 hCGgt hCFeq)⟩
      · -- F strictly outranks CE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_112 hCEeq hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_112 hCEeq hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_094 hBCgt hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith103_095 hFGgt hCFgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_120 hCEeq hFGgt hCFgt), Or.inr hFGgt⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt), Or.inr hCEgt,
            Or.inl hDz, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt),
            Or.inr hCEgt, Or.inl hDz, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_105 hCEgt hBCgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_106 hCEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_031 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt),
            Or.inr hCEgt, Or.inl hDz, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr (by exact sigmaSpeedTArith103_098 hCEgt hBCgt), Or.inr hCEgt, Or.inl hDz⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_105 hCEgt hBCgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith103_106 hCEgt hEGgt hAG),
            Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith103_032 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_113 hCEgt hBCgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith103_114 hCEgt hEFgt hAC),
            Or.inl hDz, Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith103_121 hFGeq hCEgt hBCgt hEFgt hAG),
            Or.inr (by exact sigmaSpeedTArith103_122 hFGeq hCEgt hEFgt hAG), Or.inl hDz, Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_123 hCEgt hBCgt hEFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith103_124 hCEgt hEFgt hFGgt hAG),
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith103_038 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCD
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D ties B
      exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_125 hBClt hBDgt),
        Or.inl hEz, Or.inl hFz, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D ties BC
      exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks BC
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_126 hBCeq hBDgt),
        Or.inl hEz, Or.inl hFz, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D ties C
      exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt, Or.inl hEz,
        Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith103_127 hCDgt hBCgt), Or.inr hCDgt,
        Or.inl hEz, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 89 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BCDG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
            Or.inl hEz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
            Or.inr hBDlt, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G ties B
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inl hEz, Or.inl hFz⟩
    · -- D ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
            Or.inl hEz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
            Or.inr hBClt, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G ties BD
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_004 hBGeq hAG), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith103_069 hBClt hBGgt hAG),
          Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inl hEz, Or.inl hFz⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_125 hBClt hBDgt),
          Or.inl hEz, Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
          Or.inr (by exact sigmaSpeedTArith103_125 hBClt hBDgt), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith103_128 hBClt hDGgt hBDgt hAG),
          Or.inr hDGgt, Or.inl hEz, Or.inl hFz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
            Or.inl hEz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
            Or.inr hBDlt, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G ties BC
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_007 hBDlt hBGgt), Or.inl hEz, Or.inl hFz⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
            Or.inl hEz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBCDG ⟨hA, hBne, hCne, hDne, hGne, hBCeq, hBDeq,
            hmBGeq, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith103_000 hBGlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G ties BCD
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith103_071 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith103_005 hBGeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks BCD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_072 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith103_073 hBCeq hBGgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_040 hBDeq hBGgt), Or.inl hEz, Or.inl hFz⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_126 hBCeq hBDgt),
          Or.inl hEz, Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
          Or.inr (by exact sigmaSpeedTArith103_126 hBCeq hBDgt), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_047 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith103_129 hBCeq hDGgt hBDgt hAG),
          Or.inr hDGgt, Or.inl hEz, Or.inl hFz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
            Or.inl hEz, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
            Or.inr hCDlt, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_130 hCDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G ties C
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_130 hCDlt), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_131 hCGgt hCDlt), Or.inl hEz, Or.inl hFz⟩
    · -- D ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
            Or.inl hEz, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
            Or.inr hBCgt, Or.inl hEz, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith103_074 hCGlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_132 hCDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G ties CD
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith103_076 hCGeq hAC), (by exact sigmaSpeedTArith103_077 hCGeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_132 hCDeq), Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_078 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith103_079 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_133 hCGgt hCDeq), Or.inl hEz, Or.inl hFz⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith103_127 hCDgt hBCgt), Or.inr hCDgt,
          Or.inl hEz, Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr (by exact sigmaSpeedTArith103_127 hCDgt hBCgt),
          Or.inr hCDgt, Or.inl hEz, Or.inl hFz⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith103_134 hDGgt hCDgt hBCgt hAG), Or.inr (by exact sigmaSpeedTArith103_135 hDGgt hCDgt hAG),
          Or.inr hDGgt, Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCDF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
            Or.inl hEz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
            Or.inr hBDlt, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F ties B
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
            Or.inl hEz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
            Or.inr hBClt, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F ties BD
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_010 hAB hBFeq), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_068 hBClt), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith103_080 hBClt hBFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_125 hBClt hBDgt),
          Or.inl hEz, Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties D
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
          Or.inr (by exact sigmaSpeedTArith103_125 hBClt hBDgt), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_051 hAF hBDgt hDFgt), Or.inr (by exact sigmaSpeedTArith103_136 hBClt hAF hBDgt hDFgt),
          Or.inr hDFgt, Or.inl hEz, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
            Or.inl hEz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
            Or.inr hBDlt, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F ties BC
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_001 hBDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_015 hBDlt hBFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
            Or.inl hEz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBCDF ⟨hA, hBne, hCne, hDne, hFne, hBCeq, hBDeq,
            hmBFeq, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith103_003 hBFlt),
            Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F ties BCD
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith103_081 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith103_011 hBFeq),
          Or.inr (by exact sigmaSpeedTArith103_070 hBCeq), Or.inr (by exact sigmaSpeedTArith103_039 hBDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks BCD
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_082 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith103_083 hBCeq hBFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_041 hBDeq hBFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith103_126 hBCeq hBDgt),
          Or.inl hEz, Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties D
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
          Or.inr (by exact sigmaSpeedTArith103_126 hBCeq hBDgt), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_051 hAF hBDgt hDFgt), Or.inr (by exact sigmaSpeedTArith103_137 hBCeq hAF hBDgt hDFgt),
          Or.inr hDFgt, Or.inl hEz, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
            Or.inl hEz, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
            Or.inr hCDlt, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_130 hCDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F ties C
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_130 hCDlt), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_138 hCDlt hCFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
            Or.inl hEz, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
            Or.inr hBCgt, Or.inl hEz, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith103_084 hCFlt),
            Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_132 hCDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F ties CD
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith103_085 hCFeq hAC), (by exact sigmaSpeedTArith103_086 hCFeq),
          Or.inr (by exact sigmaSpeedTArith103_075 hBCgt), Or.inr (by exact sigmaSpeedTArith103_132 hCDeq), Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_087 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith103_088 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith103_139 hCDeq hCFgt), Or.inl hEz, Or.inl hGz⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith103_127 hCDgt hBCgt), Or.inr hCDgt,
          Or.inl hEz, Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties D
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr (by exact sigmaSpeedTArith103_127 hCDgt hBCgt),
          Or.inr hCDgt, Or.inl hEz, Or.inl hGz⟩
      · -- F strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith103_140 hAF hCDgt hBCgt hDFgt), Or.inr (by exact sigmaSpeedTArith103_141 hAF hCDgt hDFgt),
          Or.inr hDFgt, Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
