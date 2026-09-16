import Grok810ScaleZeroQuarticSigmaLadderPart101Scratch

/-! Part 47 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
private theorem sigmaSpeedTArith102_000
    {a e f g : ℕ}
    (h0 : 2 * f < a + 2 * e)
    (h1 : a + e < g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_001
    {a e f g : ℕ}
    (h0 : 2 * f = a + 2 * e)
    (h1 : a + e < g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_002
    {a e f g : ℕ}
    (h0 : a + 2 * e < 2 * f)
    (h1 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_003
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f < a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_004
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f = a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_005
    {a d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + d < f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_006
    {a d e g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_007
    {a d e g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_008
    {a d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_009
    {a d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_010
    {a d e f : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_011
    {a d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_012
    {a d e f g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_013
    {a d e f g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_014
    {a d e f g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_015
    {a c g : ℕ}
    (h0 : 2 * g < 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_016
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_017
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_018
    {a c g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_019
    {a c f : ℕ}
    (h0 : 2 * f < a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_020
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_021
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_022
    {a c f : ℕ}
    (h0 : a + 3 * c < 2 * f)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_023
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f < a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_024
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f = a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_025
    {a c f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 3 * c < 2 * f)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_026
    {c e : ℕ}
    (h0 : 2 * e < 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_027
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e < 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_028
    {c e : ℕ}
    (h0 : 2 * e = 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_029
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e = 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_030
    {a c e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_031
    {a c e f : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_032
    {a c e f : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_033
    {a c e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_034
    {a c e f g : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_035
    {a c e f g : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_036
    {a c e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_037
    {a c e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_038
    {a c d : ℕ}
    (h0 : a + 2 * d < 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_039
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d < 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_040
    {a c d : ℕ}
    (h0 : a + 2 * d = 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_041
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d = 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_042
    {a c d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : 3 * c < a + 2 * d)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_043
    {a c d f : ℕ}
    (h0 : a + 2 * d < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_044
    {a c d f : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_045
    {a c d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_046
    {a c d f g : ℕ}
    (h0 : a + 2 * d < 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_047
    {a c d f g : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_048
    {a c d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_049
    {a c d f g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_050
    {a c d e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_051
    {a c d e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_052
    {a c d e : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_053
    {a c d e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_054
    {a c d e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_055
    {a c d e g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_056
    {a c d e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_057
    {a c d e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_058
    {a c d e f : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_059
    {a c d e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_060
    {a c d e f g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_061
    {a c d e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_062
    {a c d e f g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 2 * f < 2 * g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_063
    {a b g : ℕ}
    (h0 : 4 * g < 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_064
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_065
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_066
    {a b g : ℕ}
    (h0 : 7 * a + 6 * b < 4 * g)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_067
    {a b f : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_068
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 4 * f = 5 * a + 6 * b)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_069
    {a b f : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_070
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_071
    {a b f g : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_072
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_073
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_074
    {a b f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_075
    {a b f g : ℕ}
    (h0 : 5 * a + 6 * b < 4 * f)
    (h1 : a + 2 * f < 2 * g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_076
    {a b e : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_077
    {a b e g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_078
    {a b e : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_079
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_080
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_081
    {a b e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_082
    {a b e f : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_083
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * f = 5 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_084
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_085
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_086
    {a b e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_087
    {a b e f g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_088
    {a b e f g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_089
    {a b e f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_090
    {a b e f g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_091
    {a b d : ℕ}
    (h0 : 4 * d < a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_092
    {a b d g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_093
    {a b d : ℕ}
    (h0 : 4 * d = a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_094
    {a b d g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_095
    {a b d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_096
    {a b d f : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_097
    {a b d f : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_098
    {a b d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_099
    {a b d f g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_100
    {a b d f g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_101
    {a b d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_102
    {a b d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_103
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_104
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_105
    {a b d e : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_106
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_107
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_108
    {a b d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_109
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_110
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith102_111
    {a b d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 6 * b < 4 * d)
    (h3 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoL3810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL3810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * A.natDegree := by
  have hreflection :
      degreeZeroKappaQuarticNoL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [(7 / 1024 * beta : k),
      (7 / 64 * beta : k),
      -((7 / 64 * beta : k)),
      -((7 / 128 * beta : k)),
      (7 / 8 * beta : k),
      -((3 / 16 * gamma : k)),
      (3 / 4 * gamma : k),
      (5 / 1024 * delta : k),
      (5 / 64 * delta : k)]
      [[1, 2, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 0, 0]] := by
    unfold Max11ReflectDeg.polyOf
    rw [List.sum_eq_foldl]
    dsimp only [List.zipWith, List.foldl]
    simp only [degreeZeroKappaQuarticNoL3810, Max11ReflectDeg.mono_cons,
      Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
      pow_zero, pow_one, mul_one, one_mul, zero_add, add_zero, mul_assoc,
      sub_eq_add_neg, neg_smul]
  rw [hreflection]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoL4810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL4810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * A.natDegree := by
  have hreflection :
      degreeZeroKappaQuarticNoL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [(-(15 / 128 * delta : k)),
      (5 / 8 * delta : k),
      (1 / 2 * epsilon : k),
      (3 / 128 * zeta : k),
      (3 / 8 * zeta : k),
      (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [[0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0],
      [2, 0, 0, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 0]] := by
    unfold Max11ReflectDeg.polyOf
    rw [List.sum_eq_foldl]
    dsimp only [List.zipWith, List.foldl]
    simp only [degreeZeroKappaQuarticNoL4810, Max11ReflectDeg.mono_cons,
      Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
      pow_zero, pow_one, mul_one, one_mul, zero_add, add_zero, mul_assoc,
      sub_eq_add_neg, neg_smul]
  rw [hreflection]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  repeat' apply And.intro
  all_goals omega


end QuarticKappaLadder810
end Max11DegreeRoutes
end
/-! Part 52 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2Kills810


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `beta` on the k=3 cone `B`: `7s ≥ 6 a`. -/
def QuarticN2LoadTopBeta_B810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeB810' A B C D E F G ∧ 14 * B.natDegree ≤ 15 * A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `delta` on the k=3 cone `B`: `7s ≥ 10 a`. -/
def QuarticN2LoadTopDelta_B810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeB810' A B C D E F G ∧ 14 * B.natDegree ≤ 11 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 53 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2Kills810


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `zeta` on the k=3 cone `B`: `7s ≥ 14 a`. -/
def QuarticN2LoadTopZeta_B810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeB810' A B C D E F G ∧ 2 * B.natDegree ≤ A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `theta` on the k=3 cone `B`: `7s ≥ 18 a`. -/
def QuarticN2LoadTopTheta_B810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeB810' A B C D E F G ∧ 14 * B.natDegree ≤ 3 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 54 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2Kills810


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `l` on the k=3 cone `C`: `7s ≥ 2 a`. -/
def QuarticN2LoadTopL_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ 7 * C.natDegree ≤ 13 * A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `beta` on the k=3 cone `C`: `7s ≥ 6 a`. -/
def QuarticN2LoadTopBeta_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ 7 * C.natDegree ≤ 11 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 55 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2Kills810


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `delta` on the k=3 cone `C`: `7s ≥ 10 a`. -/
def QuarticN2LoadTopDelta_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ 7 * C.natDegree ≤ 9 * A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `zeta` on the k=3 cone `C`: `7s ≥ 14 a`. -/
def QuarticN2LoadTopZeta_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ C.natDegree ≤ A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 56 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2Kills810


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `theta` on the k=3 cone `C`: `7s ≥ 18 a`. -/
def QuarticN2LoadTopTheta_C810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeC810' A B C D E F G ∧ 7 * C.natDegree ≤ 5 * A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `l` on the k=3 cone `BC`: `7s ≥ 2 a`. -/
def QuarticN2LoadTopL_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 19 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 57 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2Kills810


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `beta` on the k=3 cone `BC`: `7s ≥ 6 a`. -/
def QuarticN2LoadTopBeta_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 15 * A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `delta` on the k=3 cone `BC`: `7s ≥ 10 a`. -/
def QuarticN2LoadTopDelta_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 11 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 58 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2Kills810


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `zeta` on the k=3 cone `BC`: `7s ≥ 14 a`. -/
def QuarticN2LoadTopZeta_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 2 * B.natDegree ≤ A.natDegree


set_option maxHeartbeats 64000000 in
/-- `N₂` kills `theta` on the k=3 cone `BC`: `7s ≥ 18 a`. -/
def QuarticN2LoadTopTheta_BC810 (A B C D E F G : k[X]) : Prop :=
  QuarticSigmaConeBC810' A B C D E F G ∧ 14 * B.natDegree ≤ 3 * A.natDegree


end QuarticN2Kills810
end Max11DegreeRoutes
end
/-! Part 60 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticParityCorner810


set_option maxHeartbeats 64000000 in
theorem quarticParityCorner_BDF_zero_impossible {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hB : B = 0) (hD : D = 0) (hF : F = 0) (hl : l = 0)
    (hbeta : beta = 0) (hdelta : delta = 0) (hzeta : zeta = 0)
    (htheta : theta = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) : False := by
  subst hB; subst hD; subst hF; subst hl; subst hbeta; subst hdelta
  subst hzeta; subst htheta
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810,
    rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810,
    rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    sub_zero, neg_zero, sub_self, derivative_zero] at hder
  exact hjdiv (by simpa using (Polynomial.C_eq_zero.mp hder.symm))


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_allZero
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t))
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    False := by
  rcases hA with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  exact quarticADominant_allLettersZero_impossible (j := j) (t := t)
    l beta gamma delta epsilon zeta eta theta A B C D E F G
    hApos hBz hCz hDz hEz hFz hGz hjdiv hder


end QuarticParityCorner810
end Max11DegreeRoutes
end
/-! Part 48 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem degreeZeroKappaQuarticNoL810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL810 l beta gamma delta epsilon zeta eta
        theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  have h1 :=
    degreeZeroKappaQuarticNoL1810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h2 :=
    degreeZeroKappaQuarticNoL2810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h3 :=
    degreeZeroKappaQuarticNoL3810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h4 :=
    degreeZeroKappaQuarticNoL4810_natDegree_lt_of_lTop l beta gamma delta
      epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt
      hEt hFt hGt
  have h12 := natDegree_add_lt810 h1 h2
  have h123 := natDegree_add_lt810 h12 h3
  have h1234 := natDegree_add_lt810 h123 h4
  simp only [degreeZeroKappaQuarticNoL810]
  exact h1234


set_option maxHeartbeats 64000000 in
/-- κ kills `l` when `2s > 1 a`, expanded per letter. -/
def QuarticKappaLoadTopL810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    (B = 0 ∨ 4 * B.natDegree < 5 * A.natDegree) ∧
    (C = 0 ∨ 4 * C.natDegree < 7 * A.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < 9 * A.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 11 * A.natDegree) ∧
    (F = 0 ∨ 4 * F.natDegree < 13 * A.natDegree) ∧
    (G = 0 ∨ 4 * G.natDegree < 15 * A.natDegree)


end QuarticKappaLadder810
end Max11DegreeRoutes
end
/-! Part 61 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_G
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
    Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_F
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
    Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 62 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_FG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
  · -- F strictly outranks G
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inl hEz, Or.inr hFGlt⟩
  · -- G ties F
    exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
      Or.inl hDz, Or.inl hEz⟩
  · -- G strictly outranks F
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_E
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
    Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 63 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_EG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
  · -- E strictly outranks G
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inl hFz, Or.inr hEGlt⟩
  · -- G ties E
    exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inl hCz,
      Or.inl hDz, Or.inl hFz⟩
  · -- G strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_EF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
  · -- E strictly outranks F
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inr hEFlt, Or.inl hGz⟩
  · -- F ties E
    exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inl hCz,
      Or.inl hDz, Or.inl hGz⟩
  · -- F strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 64 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_EFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
  · -- E strictly outranks F
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
        Or.inr hEFlt, Or.inr hEGlt⟩
    · -- G ties E
      exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inl hCz,
        Or.inl hDz, Or.inr hEFlt⟩
    · -- G strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
        Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
  · -- F ties E
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inl hCz,
        Or.inl hDz, Or.inr hEGlt⟩
    · -- G ties EF
      exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq, Or.inl hBz,
        Or.inl hCz, Or.inl hDz⟩
    · -- G strictly outranks EF
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
        Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
  · -- F strictly outranks E
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
    · -- F strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
        Or.inr hEFgt, Or.inr hFGlt⟩
    · -- G ties F
      exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
        Or.inl hDz, Or.inr hEFgt⟩
    · -- G strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_D
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inl hEz,
    Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 65 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_DG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
  · -- D strictly outranks G
    exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inl hEz,
      Or.inl hFz, Or.inr hDGlt⟩
  · -- G ties D
    exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inl hCz,
      Or.inl hEz, Or.inl hFz⟩
  · -- G strictly outranks D
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
      Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_DF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
  · -- D strictly outranks F
    exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inl hEz,
      Or.inr hDFlt, Or.inl hGz⟩
  · -- F ties D
    exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inl hCz,
      Or.inl hEz, Or.inl hGz⟩
  · -- F strictly outranks D
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
      Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 66 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_DFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
  · -- D strictly outranks F
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inl hEz,
        Or.inr hDFlt, Or.inr hDGlt⟩
    · -- G ties D
      exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inl hCz,
        Or.inl hEz, Or.inr hDFlt⟩
    · -- G strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
  · -- F ties D
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inl hCz,
        Or.inl hEz, Or.inr hDGlt⟩
    · -- G ties DF
      exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq, Or.inl hBz,
        Or.inl hCz, Or.inl hEz⟩
    · -- G strictly outranks DF
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
  · -- F strictly outranks D
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
    · -- F strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
        Or.inl hEz, Or.inr hFGlt⟩
    · -- G ties F
      exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDFgt, Or.inl hEz⟩
    · -- G strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt),
        Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_DE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
  · -- D strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inr hDElt,
      Or.inl hFz, Or.inl hGz⟩
  · -- E ties D
    exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inl hCz,
      Or.inl hFz, Or.inl hGz⟩
  · -- E strictly outranks D
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inr hDEgt,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 67 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_DEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
  · -- D strictly outranks E
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inr hDElt,
        Or.inl hFz, Or.inr hDGlt⟩
    · -- G ties D
      exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDElt, Or.inl hFz⟩
    · -- G strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
        Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inl hFz⟩
  · -- E ties D
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inl hCz,
        Or.inl hFz, Or.inr hDGlt⟩
    · -- G ties DE
      exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq, Or.inl hBz,
        Or.inl hCz, Or.inl hFz⟩
    · -- G strictly outranks DE
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
        Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inl hFz⟩
  · -- E strictly outranks D
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inr hDEgt,
        Or.inl hFz, Or.inr hEGlt⟩
    · -- G ties E
      exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDEgt, Or.inl hFz⟩
    · -- G strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt),
        Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_DEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
  · -- D strictly outranks E
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inr hDElt,
        Or.inr hDFlt, Or.inl hGz⟩
    · -- F ties D
      exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDElt, Or.inl hGz⟩
    · -- F strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
        Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt), Or.inl hGz⟩
  · -- E ties D
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDFlt, Or.inl hGz⟩
    · -- F ties DE
      exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq, Or.inl hBz,
        Or.inl hCz, Or.inl hGz⟩
    · -- F strictly outranks DE
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
        Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt), Or.inl hGz⟩
  · -- E strictly outranks D
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inr hDEgt,
        Or.inr hEFlt, Or.inl hGz⟩
    · -- F ties E
      exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inl hCz,
        Or.inr hDEgt, Or.inl hGz⟩
    · -- F strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt),
        Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 68 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_DEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
  · -- D strictly outranks E
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inl hCz, Or.inr hDElt,
          Or.inr hDFlt, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDElt, Or.inr hDFlt⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
          Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
    · -- F ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDElt, Or.inr hDGlt⟩
      · -- G ties DF
        exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq, Or.inl hBz,
          Or.inl hCz, Or.inr hDElt⟩
      · -- G strictly outranks DF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
          Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
    · -- F strictly outranks D
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
          Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith102_012 hDElt hFGgt hDFgt), Or.inr hFGgt⟩
  · -- E ties D
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDFlt, Or.inr hDGlt⟩
      · -- G ties DE
        exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq, Or.inl hBz,
          Or.inl hCz, Or.inr hDFlt⟩
      · -- G strictly outranks DE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
          Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
    · -- F ties DE
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq, Or.inl hBz,
          Or.inl hCz, Or.inr hDGlt⟩
      · -- G ties DEF
        exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
          hDGeq, Or.inl hBz, Or.inl hCz⟩
      · -- G strictly outranks DEF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inr hDGgt,
          Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
    · -- F strictly outranks DE
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inr hDFgt,
          Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith102_013 hDEeq hFGgt hDFgt), Or.inr hFGgt⟩
  · -- E strictly outranks D
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inr hDEgt,
          Or.inr hEFlt, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDEgt, Or.inr hEFlt⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
    · -- F ties E
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inl hCz,
          Or.inr hDEgt, Or.inr hEGlt⟩
      · -- G ties EF
        exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq, Or.inl hBz,
          Or.inl hCz, Or.inr hDEgt⟩
      · -- G strictly outranks EF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
    · -- F strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_014 hDEgt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_C
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inl hEz,
    Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 69 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
  · -- C strictly outranks G
    rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
    · -- C³ beats the mixed monomial CG
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inl hEz,
        Or.inl hFz, Or.inr hmCGlt⟩
    · -- G ties C on the mixed monomial CG
      exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz, Or.inl hDz,
        Or.inl hEz, Or.inl hFz⟩
    · -- the mixed monomial CG strictly beats C³ : residual cone
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- G ties C
    exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq), Or.inl hBz,
      Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- G strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC), Or.inl hDz,
      Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
  · -- C strictly outranks F
    rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
    · -- C³ beats the mixed monomial CF
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inl hEz,
        Or.inr hmCFlt, Or.inl hGz⟩
    · -- F ties C on the mixed monomial CF
      exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz, Or.inl hDz,
        Or.inl hEz, Or.inl hGz⟩
    · -- the mixed monomial CF strictly beats C³ : residual cone
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- F ties C
    exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
      Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- F strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz,
      Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 70 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
  · -- C strictly outranks F
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inl hEz,
            Or.inr hmCFlt, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz, Or.inl hDz,
            Or.inl hEz, Or.inr hmCFlt⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
      · -- F ties C on the mixed monomial CF
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz, Or.inl hDz,
            Or.inl hEz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
            Or.inl hBz, Or.inl hDz, Or.inl hEz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
    · -- G ties C
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
    · -- G strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC), Or.inl hDz,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
  · -- F ties C
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
    · -- G ties CF
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
    · -- G strictly outranks CF
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC), Or.inl hDz,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
  · -- F strictly outranks C
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
    · -- F strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz,
        Or.inl hEz, Or.inr hFGlt⟩
    · -- G ties F
      exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
        Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz, Or.inl hEz⟩
    · -- G strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG), Or.inl hDz,
        Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
  · -- C strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inr hCElt,
      Or.inl hFz, Or.inl hGz⟩
  · -- E ties C
    exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inl hDz,
      Or.inl hFz, Or.inl hGz⟩
  · -- E strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt, Or.inl hDz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 71 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
  · -- C strictly outranks E
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inr hCElt,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz, Or.inl hDz,
          Or.inr hCElt, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
    · -- G ties C
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq), Or.inl hBz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
    · -- G strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC), Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inl hFz⟩
  · -- E ties C
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inl hDz,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq, Or.inl hBz,
          Or.inl hDz, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
    · -- G ties CE
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq), Or.inl hBz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
    · -- G strictly outranks CE
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC), Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inl hFz⟩
  · -- E strictly outranks C
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt, Or.inl hDz,
        Or.inl hFz, Or.inr hEGlt⟩
    · -- G ties E
      exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inr hCEgt,
        Or.inl hDz, Or.inl hFz⟩
    · -- G strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG), Or.inl hDz,
        Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
  · -- C strictly outranks E
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inr hCElt,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz, Or.inl hDz,
          Or.inr hCElt, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
    · -- F ties C
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
    · -- F strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inl hGz⟩
  · -- E ties C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inl hDz,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq, Or.inl hBz,
          Or.inl hDz, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
    · -- F ties CE
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
    · -- F strictly outranks CE
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inl hGz⟩
  · -- E strictly outranks C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt, Or.inl hDz,
        Or.inr hEFlt, Or.inl hGz⟩
    · -- F ties E
      exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inr hCEgt,
        Or.inl hDz, Or.inl hGz⟩
    · -- F strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC), Or.inl hDz,
        Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 72 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
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
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz,
              Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz,
              Or.inl hDz, Or.inr hCElt, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz,
              Or.inl hDz, Or.inr hCElt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
              Or.inl hBz, Or.inl hDz, Or.inr hCElt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties C
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
    · -- F ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
    · -- F strictly outranks C
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_034 hCElt hFGgt hCFgt), Or.inr hFGgt⟩
  · -- E ties C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz,
              Or.inl hDz, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
              Or.inl hBz, Or.inl hDz, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
              Or.inl hBz, Or.inl hDz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCEFG ⟨hA, hCne, hEne, hFne, hGne, hCEeq, hmCFeq,
              hmCGeq, Or.inl hBz, Or.inl hDz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CE
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
    · -- F ties CE
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CEF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CEF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
    · -- F strictly outranks CE
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_035 hCEeq hFGgt hCFgt), Or.inr hFGgt⟩
  · -- E strictly outranks C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt, Or.inl hDz,
          Or.inr hEFlt, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inr hCEgt,
          Or.inl hDz, Or.inr hEFlt⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
          Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
    · -- F ties E
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inr hCEgt,
          Or.inl hDz, Or.inr hEGlt⟩
      · -- G ties EF
        exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq, Or.inl hBz,
          Or.inr hCEgt, Or.inl hDz⟩
      · -- G strictly outranks EF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
          Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
    · -- F strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC),
          Or.inl hDz, Or.inr hEFgt, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_036 hFGeq hCEgt hEFgt hAG), Or.inl hDz, Or.inr hEFgt⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_037 hCEgt hEFgt hFGgt hAG),
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CD
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- D ties C
    exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- D strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 73 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CDG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt, Or.inl hEz,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz, Or.inr hCDlt,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inl hFz⟩
    · -- G ties C
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq), Or.inl hBz,
        Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
        Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inl hEz, Or.inl hFz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz, Or.inl hEz,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq, Or.inl hBz,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inl hFz⟩
    · -- G ties CD
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq), Or.inl hBz,
        Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks CD
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
        Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inl hEz, Or.inl hFz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inl hEz,
        Or.inl hFz, Or.inr hDGlt⟩
    · -- G ties D
      exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inr hCDgt,
        Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
        Or.inr hDGgt, Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt, Or.inl hEz,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz, Or.inr hCDlt,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inl hGz⟩
    · -- F ties C
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
        Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inl hEz, Or.inl hGz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz, Or.inl hEz,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq, Or.inl hBz,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inl hGz⟩
    · -- F ties CD
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq), Or.inl hBz,
        Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks CD
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
        Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inl hEz, Or.inl hGz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inl hEz,
        Or.inr hDFlt, Or.inl hGz⟩
    · -- F ties D
      exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inr hCDgt,
        Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
        Or.inr hDFgt, Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 74 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt,
              Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz,
              Or.inr hCDlt, Or.inl hEz, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz,
              Or.inr hCDlt, Or.inl hEz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
              Or.inl hBz, Or.inr hCDlt, Or.inl hEz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties C
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
    · -- F ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
    · -- F strictly outranks C
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_046 hCDlt hFGgt hCFgt), Or.inl hEz, Or.inr hFGgt⟩
  · -- D ties C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz,
              Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
              Or.inl hBz, Or.inl hEz, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
              Or.inl hBz, Or.inl hEz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDFG ⟨hA, hCne, hDne, hFne, hGne, hCDeq, hmCFeq,
              hmCGeq, Or.inl hBz, Or.inl hEz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CD
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
    · -- F ties CD
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
      · -- G ties CDF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
      · -- G strictly outranks CDF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
    · -- F strictly outranks CD
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_047 hCDeq hFGgt hCFgt), Or.inl hEz, Or.inr hFGgt⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inl hEz,
          Or.inr hDFlt, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inr hCDgt,
          Or.inl hEz, Or.inr hDFlt⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
          Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
    · -- F ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inr hCDgt,
          Or.inl hEz, Or.inr hDGlt⟩
      · -- G ties DF
        exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq, Or.inl hBz,
          Or.inr hCDgt, Or.inl hEz⟩
      · -- G strictly outranks DF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
          Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
    · -- F strictly outranks D
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
          Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_048 hFGeq hCDgt hDFgt hAG), Or.inr hDFgt, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_049 hCDgt hFGgt hDFgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt, Or.inr hCElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties C
      exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inr hCDlt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
        Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inl hFz, Or.inl hGz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz, Or.inr hCElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties CD
      exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq, Or.inl hBz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks CD
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
        Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inl hFz, Or.inl hGz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inr hDElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties D
      exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inr hCDgt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt),
        Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 75 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt,
            Or.inr hCElt, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz,
            Or.inr hCDlt, Or.inr hCElt, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
      · -- G ties C
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inl hFz⟩
    · -- E ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz,
            Or.inr hCDlt, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
            Or.inl hBz, Or.inr hCDlt, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
      · -- G ties CE
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
      · -- G strictly outranks CE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inl hFz⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_053 hCEgt hCDlt hEGgt), Or.inr hEGgt, Or.inl hFz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz,
            Or.inr hCElt, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
            Or.inl hBz, Or.inr hCElt, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
      · -- G ties CD
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hFz⟩
      · -- G strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inl hFz⟩
    · -- E ties CD
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
        · -- C³ beats the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
            Or.inl hBz, Or.inl hFz, Or.inr hmCGlt⟩
        · -- G ties C on the mixed monomial CG
          exact QuarticSigmaSupportCone810.sigmaCDEG ⟨hA, hCne, hDne, hEne, hGne, hCDeq, hCEeq,
            hmCGeq, Or.inl hBz, Or.inl hFz⟩
        · -- the mixed monomial CG strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
      · -- G ties CDE
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hFz⟩
      · -- G strictly outranks CDE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inl hFz⟩
    · -- E strictly outranks CD
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_054 hCEgt hCDeq hEGgt), Or.inr hEGgt, Or.inl hFz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inr hDElt,
          Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inr hCDgt,
          Or.inr hDElt, Or.inl hFz⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
          Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inl hFz⟩
    · -- E ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inr hCDgt,
          Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties DE
        exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq, Or.inl hBz,
          Or.inr hCDgt, Or.inl hFz⟩
      · -- G strictly outranks DE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
          Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inl hFz⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt),
          Or.inr hDEgt, Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt), Or.inr hDEgt, Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_055 hCDgt hDEgt hEGgt hAG),
          Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt,
            Or.inr hCElt, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz,
            Or.inr hCDlt, Or.inr hCElt, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
      · -- F ties C
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
      · -- F strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inl hGz⟩
    · -- E ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz,
            Or.inr hCDlt, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
            Or.inl hBz, Or.inr hCDlt, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
      · -- F ties CE
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
      · -- F strictly outranks CE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inl hGz⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_056 hCEgt hCDlt hEFgt), Or.inr hEFgt, Or.inl hGz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz,
            Or.inr hCElt, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
            Or.inl hBz, Or.inr hCElt, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
      · -- F ties CD
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inl hGz⟩
      · -- F strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inl hGz⟩
    · -- E ties CD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
            Or.inl hBz, Or.inr hmCFlt, Or.inl hGz⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.sigmaCDEF ⟨hA, hCne, hDne, hEne, hFne, hCDeq, hCEeq,
            hmCFeq, Or.inl hBz, Or.inl hGz⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt), Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
      · -- F ties CDE
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
          Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inl hGz⟩
      · -- F strictly outranks CDE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inl hGz⟩
    · -- E strictly outranks CD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC),
          Or.inr (by exact sigmaSpeedTArith102_057 hCEgt hCDeq hEFgt), Or.inr hEFgt, Or.inl hGz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inr hDElt,
          Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties D
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inr hCDgt,
          Or.inr hDElt, Or.inl hGz⟩
      · -- F strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt), Or.inl hGz⟩
    · -- E ties D
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inr hCDgt,
          Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties DE
        exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq, Or.inl hBz,
          Or.inr hCDgt, Or.inl hGz⟩
      · -- F strictly outranks DE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt), Or.inl hGz⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt),
          Or.inr hDEgt, Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
          Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt), Or.inr hDEgt, Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_058 hCDgt hDEgt hEFgt hAE),
          Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 76 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
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
              exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt,
                Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz,
                Or.inr hCDlt, Or.inr hCElt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz,
                Or.inr hCDlt, Or.inr hCElt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
                Or.inl hBz, Or.inr hCDlt, Or.inr hCElt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties C
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
      · -- F ties C
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
      · -- F strictly outranks C
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_046 hCDlt hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith102_034 hCElt hFGgt hCFgt), Or.inr hFGgt⟩
    · -- E ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz,
                Or.inr hCDlt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
                Or.inl hBz, Or.inr hCDlt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
                Or.inl hBz, Or.inr hCDlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEFG ⟨hA, hCne, hEne, hFne, hGne, hCEeq,
                hmCFeq, hmCGeq, Or.inl hBz, Or.inr hCDlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CE
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
      · -- F ties CE
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CEF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_038 hCDlt), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_039 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
      · -- F strictly outranks CE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_043 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_046 hCDlt hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith102_035 hCEeq hFGgt hCFgt), Or.inr hFGgt⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
            Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_053 hCEgt hCDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inl hBz, Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_050 hCEgt hCDlt)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_053 hCEgt hCDlt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_056 hCEgt hCDlt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_036 hFGeq hCEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith102_056 hCEgt hCDlt hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_037 hCEgt hEFgt hFGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_059 hCEgt hCDlt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩
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
              exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz,
                Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
                Or.inl hBz, Or.inr hCElt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
                Or.inl hBz, Or.inr hCElt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDFG ⟨hA, hCne, hDne, hFne, hGne, hCDeq,
                hmCFeq, hmCGeq, Or.inl hBz, Or.inr hCElt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CD
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
      · -- F ties CD
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CDF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_026 hCElt), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_027 hCGgt hCElt), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
      · -- F strictly outranks CD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_031 hCElt hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_047 hCDeq hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith102_034 hCElt hFGgt hCFgt), Or.inr hFGgt⟩
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
                Or.inl hBz, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDEG ⟨hA, hCne, hDne, hEne, hGne, hCDeq, hCEeq,
                hmCGeq, Or.inl hBz, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDEF ⟨hA, hCne, hDne, hEne, hFne, hCDeq, hCEeq,
                hmCFeq, Or.inl hBz, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDEFG ⟨hA, hCne, hDne, hEne, hFne, hGne, hCDeq,
                hCEeq, hmCFeq, hmCGeq, Or.inl hBz⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith102_015 hCGlt),
                Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CDE
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith102_016 hCGeq hAC), (by exact sigmaSpeedTArith102_017 hCGeq),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_019 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith102_019 hCFlt),
              Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_023 hCGgt hCFlt)⟩
      · -- F ties CDE
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_015 hCGlt)⟩
        · -- G ties CDEF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith102_020 hCFeq hAC), (by exact sigmaSpeedTArith102_021 hCFeq),
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_040 hCDeq), Or.inr (by exact sigmaSpeedTArith102_028 hCEeq), Or.inr (by exact sigmaSpeedTArith102_017 hCGeq)⟩
        · -- G strictly outranks CDEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_018 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_041 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith102_029 hCGgt hCEeq), Or.inr (by exact sigmaSpeedTArith102_024 hCGgt hCFeq)⟩
      · -- F strictly outranks CDE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_022 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith102_044 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith102_032 hCEeq hCFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_025 hFGgt hCFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_047 hCDeq hFGgt hCFgt), Or.inr (by exact sigmaSpeedTArith102_035 hCEeq hFGgt hCFgt), Or.inr hFGgt⟩
    · -- E strictly outranks CD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
            Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_054 hCEgt hCDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inl hBz, Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith102_051 hCEgt hCDeq)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_030 hCEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_054 hCEgt hCDeq hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_033 hCEgt hEFgt hAC),
            Or.inr (by exact sigmaSpeedTArith102_057 hCEgt hCDeq hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_036 hFGeq hCEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith102_057 hCEgt hCDeq hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_037 hCEgt hEFgt hFGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_060 hCEgt hCDeq hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt,
            Or.inr hDElt, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz,
            Or.inr hCDgt, Or.inr hDElt, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz,
            Or.inr hCDgt, Or.inr hDElt, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inl hBz, Or.inr hCDgt, Or.inr hDElt⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_048 hFGeq hCDgt hDFgt hAG), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_049 hCDgt hFGgt hDFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith102_012 hDElt hFGgt hDFgt), Or.inr hFGgt⟩
    · -- E ties D
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz,
            Or.inr hCDgt, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inl hBz, Or.inr hCDgt, Or.inr hDFlt⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
      · -- F ties DE
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inl hBz, Or.inr hCDgt, Or.inr hDGlt⟩
        · -- G ties DEF
          exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
            hDGeq, Or.inl hBz, Or.inr hCDgt⟩
        · -- G strictly outranks DEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_042 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
      · -- F strictly outranks DE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_045 hAF hCDgt hDFgt),
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_048 hFGeq hCDgt hDFgt hAG), Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_049 hCDgt hFGgt hDFgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inr (by exact sigmaSpeedTArith102_013 hDEeq hFGgt hDFgt), Or.inr hFGgt⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt),
            Or.inr hDEgt, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt), Or.inr hDEgt, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_055 hCDgt hDEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt), Or.inr hDEgt, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_052 hCDgt hDEgt), Or.inr hDEgt⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_055 hCDgt hDEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_058 hCDgt hDEgt hEFgt hAE),
            Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by exact sigmaSpeedTArith102_061 hFGeq hCDgt hDEgt hEFgt hAG), Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by exact sigmaSpeedTArith102_062 hCDgt hDEgt hEFgt hFGgt hAG),
            Or.inr (by exact sigmaSpeedTArith102_014 hDEgt hEFgt hFGgt), Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_B
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
    Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 77 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
  · -- B strictly outranks G
    rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
    · -- B³ beats the mixed monomial BG
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
        Or.inl hFz, Or.inr hmBGlt⟩
    · -- G ties B on the mixed monomial BG
      exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inl hFz⟩
    · -- the mixed monomial BG strictly beats B³ : residual cone
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- G ties B
    exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq), Or.inl hCz,
      Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- G strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz, Or.inl hDz,
      Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
  · -- B strictly outranks F
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
    · -- B³ beats the mixed monomial BF
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
        Or.inr hmBFlt, Or.inl hGz⟩
    · -- F ties B on the mixed monomial BF
      exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inl hGz⟩
    · -- the mixed monomial BF strictly beats B³ : residual cone
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- F ties B
    exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
      Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- F strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz, Or.inl hDz,
      Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 78 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
  · -- B strictly outranks F
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
            Or.inr hmBFlt, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz, Or.inl hDz,
            Or.inl hEz, Or.inr hmBFlt⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
      · -- F ties B on the mixed monomial BF
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz, Or.inl hDz,
            Or.inl hEz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
            Or.inl hCz, Or.inl hDz, Or.inl hEz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
    · -- G ties B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
    · -- G strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_071 hBFlt hBGgt)⟩
  · -- F ties B
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
    · -- G ties BF
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_072 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inl hDz, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
    · -- G strictly outranks BF
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_073 hBFeq hBGgt)⟩
  · -- F strictly outranks B
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
    · -- F strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inr hFGlt⟩
    · -- G ties F
      exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_074 hFGeq hBFgt hAG),
        Or.inl hCz, Or.inl hDz, Or.inl hEz⟩
    · -- G strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_075 hBFgt hFGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
  · -- B strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inr hBElt,
      Or.inl hFz, Or.inl hGz⟩
  · -- E ties B
    exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz, Or.inl hDz,
      Or.inl hFz, Or.inl hGz⟩
  · -- E strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz, Or.inl hDz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 79 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
  · -- B strictly outranks E
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inr hBElt,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz, Or.inl hDz,
          Or.inr hBElt, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
    · -- G ties B
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq), Or.inl hCz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
    · -- G strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_077 hBElt hBGgt), Or.inl hFz⟩
  · -- E ties B
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz, Or.inl hDz,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq, Or.inl hCz,
          Or.inl hDz, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
    · -- G ties BE
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_079 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith102_065 hBGeq), Or.inl hCz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
    · -- G strictly outranks BE
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_080 hBEeq hBGgt), Or.inl hFz⟩
  · -- E strictly outranks B
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz, Or.inl hDz,
        Or.inl hFz, Or.inr hEGlt⟩
    · -- G ties E
      exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt, Or.inl hCz,
        Or.inl hDz, Or.inl hFz⟩
    · -- G strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_081 hBEgt hEGgt hAG), Or.inl hCz, Or.inl hDz,
        Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
  · -- B strictly outranks E
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inr hBElt,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz, Or.inl hDz,
          Or.inr hBElt, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
    · -- F ties B
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
    · -- F strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz, Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_082 hBElt hBFgt), Or.inl hGz⟩
  · -- E ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz, Or.inl hDz,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq, Or.inl hCz,
          Or.inl hDz, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
    · -- F ties BE
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_083 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
    · -- F strictly outranks BE
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_084 hBEeq hBFgt hAE), Or.inl hCz, Or.inl hDz,
        Or.inr (by exact sigmaSpeedTArith102_085 hBEeq hBFgt), Or.inl hGz⟩
  · -- E strictly outranks B
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz, Or.inl hDz,
        Or.inr hEFlt, Or.inl hGz⟩
    · -- F ties E
      exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt, Or.inl hCz,
        Or.inl hDz, Or.inl hGz⟩
    · -- F strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_086 hBEgt hEFgt hAE), Or.inl hCz, Or.inl hDz,
        Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 80 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
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
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz,
              Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz,
              Or.inl hDz, Or.inr hBElt, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz,
              Or.inl hDz, Or.inr hBElt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
              Or.inl hCz, Or.inl hDz, Or.inr hBElt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties B
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_077 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith102_071 hBFlt hBGgt)⟩
    · -- F ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_072 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_077 hBElt hBGgt), Or.inr (by exact sigmaSpeedTArith102_073 hBFeq hBGgt)⟩
    · -- F strictly outranks B
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_082 hBElt hBFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_074 hFGeq hBFgt hAG),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_082 hBElt hBFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_075 hBFgt hFGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_087 hBElt hBFgt hFGgt), Or.inr hFGgt⟩
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
              Or.inl hDz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
              Or.inl hCz, Or.inl hDz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
              Or.inl hCz, Or.inl hDz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBEFG ⟨hA, hBne, hEne, hFne, hGne, hBEeq, hmBFeq,
              hmBGeq, Or.inl hCz, Or.inl hDz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BE
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_079 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_079 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_080 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith102_071 hBFlt hBGgt)⟩
    · -- F ties BE
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_083 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BEF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_083 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BEF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_080 hBEeq hBGgt), Or.inr (by exact sigmaSpeedTArith102_073 hBFeq hBGgt)⟩
    · -- F strictly outranks BE
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_084 hBEeq hBFgt hAE), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_085 hBEeq hBFgt), Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_074 hFGeq hBFgt hAG),
          Or.inl hCz, Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_085 hBEeq hBFgt)⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_075 hBFgt hFGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_088 hBEeq hBFgt hFGgt), Or.inr hFGgt⟩
  · -- E strictly outranks B
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz, Or.inl hDz,
          Or.inr hEFlt, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt, Or.inl hCz,
          Or.inl hDz, Or.inr hEFlt⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_081 hBEgt hEGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_000 hEFlt hEGgt)⟩
    · -- F ties E
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt, Or.inl hCz,
          Or.inl hDz, Or.inr hEGlt⟩
      · -- G ties EF
        exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
          Or.inr hBEgt, Or.inl hCz, Or.inl hDz⟩
      · -- G strictly outranks EF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_081 hBEgt hEGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr hEGgt, Or.inr (by exact sigmaSpeedTArith102_001 hEFeq hEGgt)⟩
    · -- F strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_086 hBEgt hEFgt hAE), Or.inl hCz,
          Or.inl hDz, Or.inr hEFgt, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_089 hFGeq hBEgt hEFgt hAG),
          Or.inl hCz, Or.inl hDz, Or.inr hEFgt⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_090 hBEgt hEFgt hFGgt hAG), Or.inl hCz,
          Or.inl hDz, Or.inr (by exact sigmaSpeedTArith102_002 hEFgt hFGgt), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BD
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- D ties B
    exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- D strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 81 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BDG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt, Or.inl hEz,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz, Or.inr hBDlt,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inl hFz⟩
    · -- G ties B
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_092 hBDlt hBGgt), Or.inl hEz, Or.inl hFz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
    · -- B strictly outranks G
      rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
      · -- B³ beats the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz, Or.inl hEz,
          Or.inl hFz, Or.inr hmBGlt⟩
      · -- G ties B on the mixed monomial BG
        exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq, Or.inl hCz,
          Or.inl hEz, Or.inl hFz⟩
      · -- the mixed monomial BG strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inl hFz⟩
    · -- G ties BD
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks BD
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_094 hBDeq hBGgt), Or.inl hEz, Or.inl hFz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
    · -- D strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inl hEz,
        Or.inl hFz, Or.inr hDGlt⟩
    · -- G ties D
      exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt, Or.inl hCz,
        Or.inl hEz, Or.inl hFz⟩
    · -- G strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_095 hDGgt hBDgt hAG), Or.inl hCz,
        Or.inr hDGgt, Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt, Or.inl hEz,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz, Or.inr hBDlt,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inl hGz⟩
    · -- F ties B
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_096 hBDlt hBFgt), Or.inl hEz, Or.inl hGz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
      · -- B³ beats the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz, Or.inl hEz,
          Or.inr hmBFlt, Or.inl hGz⟩
      · -- F ties B on the mixed monomial BF
        exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq, Or.inl hCz,
          Or.inl hEz, Or.inl hGz⟩
      · -- the mixed monomial BF strictly beats B³ : residual cone
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inl hGz⟩
    · -- F ties BD
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks BD
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_097 hBDeq hBFgt), Or.inl hEz, Or.inl hGz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inl hEz,
        Or.inr hDFlt, Or.inl hGz⟩
    · -- F ties D
      exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt, Or.inl hCz,
        Or.inl hEz, Or.inl hGz⟩
    · -- F strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_098 hAF hBDgt hDFgt), Or.inl hCz,
        Or.inr hDFgt, Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 82 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt,
              Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz,
              Or.inr hBDlt, Or.inl hEz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz,
              Or.inr hBDlt, Or.inl hEz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
              Or.inl hCz, Or.inr hBDlt, Or.inl hEz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties B
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_092 hBDlt hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_071 hBFlt hBGgt)⟩
    · -- F ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_072 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_092 hBDlt hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_073 hBFeq hBGgt)⟩
    · -- F strictly outranks B
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_096 hBDlt hBFgt), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_074 hFGeq hBFgt hAG),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_096 hBDlt hBFgt), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_075 hBFgt hFGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_099 hBDlt hBFgt hFGgt), Or.inl hEz, Or.inr hFGgt⟩
  · -- D ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz,
              Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
              Or.inl hCz, Or.inl hEz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
              Or.inl hCz, Or.inl hEz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDFG ⟨hA, hBne, hDne, hFne, hGne, hBDeq, hmBFeq,
              hmBGeq, Or.inl hCz, Or.inl hEz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt),
              Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
            Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_067 hBFlt)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_094 hBDeq hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_071 hBFlt hBGgt)⟩
    · -- F ties BD
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_063 hBGlt)⟩
      · -- G ties BDF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_072 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_065 hBGeq)⟩
      · -- G strictly outranks BDF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_094 hBDeq hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_073 hBFeq hBGgt)⟩
    · -- F strictly outranks BD
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_097 hBDeq hBFgt), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_074 hFGeq hBFgt hAG),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_097 hBDeq hBFgt), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_075 hBFgt hFGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_100 hBDeq hBFgt hFGgt), Or.inl hEz, Or.inr hFGgt⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inl hEz,
          Or.inr hDFlt, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt, Or.inl hCz,
          Or.inl hEz, Or.inr hDFlt⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_095 hDGgt hBDgt hAG), Or.inl hCz,
          Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_003 hDGgt hDFlt)⟩
    · -- F ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt, Or.inl hCz,
          Or.inl hEz, Or.inr hDGlt⟩
      · -- G ties DF
        exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
          Or.inr hBDgt, Or.inl hCz, Or.inl hEz⟩
      · -- G strictly outranks DF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_095 hDGgt hBDgt hAG), Or.inl hCz,
          Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith102_004 hDGgt hDFeq)⟩
    · -- F strictly outranks D
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_098 hAF hBDgt hDFgt), Or.inl hCz,
          Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith102_101 hFGeq hBDgt hDFgt hAG),
          Or.inl hCz, Or.inr hDFgt, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_102 hFGgt hBDgt hDFgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_005 hFGgt hDFgt), Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt, Or.inr hBElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties B
      exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz, Or.inr hBDlt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_103 hBEgt hBDlt), Or.inl hFz, Or.inl hGz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz, Or.inr hBElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties BD
      exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq, Or.inl hCz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks BD
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
        Or.inr (by exact sigmaSpeedTArith102_104 hBEgt hBDeq), Or.inl hFz, Or.inl hGz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inr hDElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties D
      exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt, Or.inl hCz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith102_105 hDEgt hBDgt), Or.inl hCz,
        Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 83 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt,
            Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz,
            Or.inr hBDlt, Or.inr hBElt, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
      · -- G ties B
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_092 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith102_077 hBElt hBGgt), Or.inl hFz⟩
    · -- E ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz,
            Or.inr hBDlt, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
            Or.inl hCz, Or.inr hBDlt, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
      · -- G ties BE
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_079 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
      · -- G strictly outranks BE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_092 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith102_080 hBEeq hBGgt), Or.inl hFz⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_103 hBEgt hBDlt), Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_103 hBEgt hBDlt), Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_081 hBEgt hEGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_106 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inl hFz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz,
            Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
            Or.inl hCz, Or.inr hBElt, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
      · -- G ties BD
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_064 hBGeq hAG), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hFz⟩
      · -- G strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_094 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith102_077 hBElt hBGgt), Or.inl hFz⟩
    · -- E ties BD
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
        · -- B³ beats the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
            Or.inl hCz, Or.inl hFz, Or.inr hmBGlt⟩
        · -- G ties B on the mixed monomial BG
          exact QuarticSigmaSupportCone810.sigmaBDEG ⟨hA, hBne, hDne, hEne, hGne, hBDeq, hBEeq,
            hmBGeq, Or.inl hCz, Or.inl hFz⟩
        · -- the mixed monomial BG strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith102_063 hBGlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
      · -- G ties BDE
        exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith102_079 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith102_065 hBGeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hFz⟩
      · -- G strictly outranks BDE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_066 hBGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_094 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith102_080 hBEeq hBGgt), Or.inl hFz⟩
    · -- E strictly outranks BD
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_104 hBEgt hBDeq), Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_104 hBEgt hBDeq), Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_081 hBEgt hEGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_107 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inl hFz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inr hDElt,
          Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt, Or.inl hCz,
          Or.inr hDElt, Or.inl hFz⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_095 hDGgt hBDgt hAG), Or.inl hCz,
          Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_006 hDElt hDGgt), Or.inl hFz⟩
    · -- E ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt, Or.inl hCz,
          Or.inl hFz, Or.inr hDGlt⟩
      · -- G ties DE
        exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
          Or.inr hBDgt, Or.inl hCz, Or.inl hFz⟩
      · -- G strictly outranks DE
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_095 hDGgt hBDgt hAG), Or.inl hCz,
          Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith102_007 hDEeq hDGgt), Or.inl hFz⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
      · -- E strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith102_105 hDEgt hBDgt), Or.inl hCz,
          Or.inr hDEgt, Or.inl hFz, Or.inr hEGlt⟩
      · -- G ties E
        exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith102_105 hDEgt hBDgt),
          Or.inl hCz, Or.inr hDEgt, Or.inl hFz⟩
      · -- G strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith102_108 hDEgt hBDgt hEGgt hAG), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_008 hDEgt hEGgt), Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt,
            Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz,
            Or.inr hBDlt, Or.inr hBElt, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
      · -- F ties B
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
      · -- F strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_096 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith102_082 hBElt hBFgt), Or.inl hGz⟩
    · -- E ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz,
            Or.inr hBDlt, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
            Or.inl hCz, Or.inr hBDlt, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
      · -- F ties BE
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_083 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_091 hBDlt), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
      · -- F strictly outranks BE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_084 hBEeq hBFgt hAE), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_096 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith102_085 hBEeq hBFgt), Or.inl hGz⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_103 hBEgt hBDlt), Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_103 hBEgt hBDlt), Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_086 hBEgt hEFgt hAE), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_109 hBEgt hBDlt hEFgt), Or.inr hEFgt, Or.inl hGz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz,
            Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
            Or.inl hCz, Or.inr hBElt, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
      · -- F ties BD
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_068 hAB hBFeq), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_076 hBElt), Or.inl hGz⟩
      · -- F strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_070 hAB hBFgt), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_097 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith102_082 hBElt hBFgt), Or.inl hGz⟩
    · -- E ties BD
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
            Or.inl hCz, Or.inr hmBFlt, Or.inl hGz⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.sigmaBDEF ⟨hA, hBne, hDne, hEne, hFne, hBDeq, hBEeq,
            hmBFeq, Or.inl hCz, Or.inl hGz⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith102_067 hBFlt), Or.inl hCz,
            Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
      · -- F ties BDE
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith102_083 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith102_069 hBFeq),
          Or.inl hCz, Or.inr (by exact sigmaSpeedTArith102_093 hBDeq), Or.inr (by exact sigmaSpeedTArith102_078 hBEeq), Or.inl hGz⟩
      · -- F strictly outranks BDE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_084 hBEeq hBFgt hAE), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_097 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith102_085 hBEeq hBFgt), Or.inl hGz⟩
    · -- E strictly outranks BD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_104 hBEgt hBDeq), Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt, Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_104 hBEgt hBDeq), Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_086 hBEgt hEFgt hAE), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_110 hBEgt hBDeq hEFgt), Or.inr hEFgt, Or.inl hGz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inr hDElt,
          Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties D
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt, Or.inl hCz,
          Or.inr hDElt, Or.inl hGz⟩
      · -- F strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_098 hAF hBDgt hDFgt), Or.inl hCz,
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_009 hDElt hDFgt), Or.inl hGz⟩
    · -- E ties D
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt, Or.inl hCz,
          Or.inr hDFlt, Or.inl hGz⟩
      · -- F ties DE
        exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
          Or.inr hBDgt, Or.inl hCz, Or.inl hGz⟩
      · -- F strictly outranks DE
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_098 hAF hBDgt hDFgt), Or.inl hCz,
          Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith102_010 hDEeq hDFgt), Or.inl hGz⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith102_105 hDEgt hBDgt), Or.inl hCz,
          Or.inr hDEgt, Or.inr hEFlt, Or.inl hGz⟩
      · -- F ties E
        exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith102_105 hDEgt hBDgt),
          Or.inl hCz, Or.inr hDEgt, Or.inl hGz⟩
      · -- F strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith102_111 hDEgt hEFgt hBDgt hAE), Or.inl hCz,
          Or.inr (by exact sigmaSpeedTArith102_011 hDEgt hEFgt), Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
