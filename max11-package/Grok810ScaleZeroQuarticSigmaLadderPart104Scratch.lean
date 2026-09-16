import Grok810ScaleZeroQuarticSigmaLadderPart101Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart102Scratch

/-! Part 90 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
private theorem sigmaSpeedTArith104_000
    {a b g : ℕ}
    (h0 : 4 * g < 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_001
    {a b c : ℕ}
    (h0 : 2 * c < a + 2 * b)
    : 2 * c ≤ a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_002
    {a b d : ℕ}
    (h0 : 4 * d < a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_003
    {a b f : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_004
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_005
    {a b g : ℕ}
    (h0 : 4 * g = 7 * a + 6 * b)
    : 4 * g ≤ 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_006
    {a b g : ℕ}
    (h0 : 7 * a + 6 * b < 4 * g)
    (h1 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_007
    {a b c g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_008
    {a b d g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_009
    {a b f g : ℕ}
    (h0 : 4 * f < 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_010
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 4 * f = 5 * a + 6 * b)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_011
    {a b f : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    : 4 * f ≤ 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_012
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_013
    {a b f g : ℕ}
    (h0 : 4 * f = 5 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_014
    {a b f : ℕ}
    (h0 : 2 * b < 3 * a)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_015
    {a b c f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_016
    {a b d f : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_017
    {a b f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_018
    {a b c f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : 5 * a + 6 * b < 4 * f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_019
    {a b f g : ℕ}
    (h0 : 5 * a + 6 * b < 4 * f)
    (h1 : a + 2 * f < 2 * g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_020
    {a b c f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_021
    {a b d f g : ℕ}
    (h0 : 4 * d < a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_022
    {a b d : ℕ}
    (h0 : 4 * d = a + 6 * b)
    : 4 * d ≤ a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_023
    {a b d g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_024
    {a b d f : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_025
    {a b d f g : ℕ}
    (h0 : 4 * d = a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_026
    {a b c d : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 6 * b < 4 * d)
    : 3 * c < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_027
    {a b d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_028
    {a b c d g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 2 * d < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_029
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f < a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_030
    {a d f g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : f = a + d)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_031
    {a b d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_032
    {a b c d f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_033
    {a b d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_034
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_035
    {a b d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_036
    {a b c d f g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_037
    {a d f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + d < f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_038
    {a b c : ℕ}
    (h0 : 2 * c = a + 2 * b)
    : 2 * c ≤ a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_039
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_040
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_041
    {a b c g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    (h2 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_042
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 4 * f = 5 * a + 6 * b)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_043
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_044
    {a b c f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_045
    {a b c f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : a + 2 * f < 2 * g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_046
    {a b c d : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 6 * b < 4 * d)
    : 3 * c < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_047
    {a b c d g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 2 * d < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_048
    {a b c d f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 2 * f < 7 * a)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_049
    {a b c d f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 2 * g = a + 2 * f)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_050
    {a b c d f g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_051
    {a c g : ℕ}
    (h0 : 2 * g < 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_052
    {a b c : ℕ}
    (h0 : a + 2 * b < 2 * c)
    : a + 2 * b ≤ 2 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_053
    {a c d : ℕ}
    (h0 : a + 2 * d < 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_054
    {a c f : ℕ}
    (h0 : 2 * f < a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_055
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_056
    {a c g : ℕ}
    (h0 : 2 * g = 2 * a + 3 * c)
    : 2 * g ≤ 2 * a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_057
    {a b c g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * b < 2 * c)
    (h2 : c < 2 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_058
    {a c g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : c < 2 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_059
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d < 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_060
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f < a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_061
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_062
    {a c f : ℕ}
    (h0 : 2 * f = a + 3 * c)
    : 2 * f ≤ a + 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_063
    {a c f g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * f = a + 3 * c)
    : a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_064
    {a b c f : ℕ}
    (h0 : a + 2 * b < 2 * c)
    (h1 : a + 3 * c < 2 * f)
    (h2 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_065
    {a c f : ℕ}
    (h0 : a + 3 * c < 2 * f)
    (h1 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_066
    {a c d f : ℕ}
    (h0 : a + 2 * d < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_067
    {a b c f g : ℕ}
    (h0 : a + 2 * b < 2 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_068
    {a c f g : ℕ}
    (h0 : a + 2 * f < 2 * g)
    (h1 : a + 3 * c < 2 * f)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_069
    {a c d f g : ℕ}
    (h0 : a + 2 * d < 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_070
    {a c d : ℕ}
    (h0 : a + 2 * d = 3 * c)
    : a + 2 * d ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_071
    {a c d g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : a + 2 * d = 3 * c)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_072
    {a c d f : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_073
    {a c d f g : ℕ}
    (h0 : a + 2 * d = 3 * c)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + 3 * c < 2 * f)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_074
    {a b c d : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    : a + 6 * b < 4 * d := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_075
    {a b c d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_076
    {a c d g : ℕ}
    (h0 : 3 * a + 2 * d < 2 * g)
    (h1 : 3 * c < a + 2 * d)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_077
    {a b c d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : a + d < f)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_078
    {a c d f : ℕ}
    (h0 : 2 * f < 7 * a)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + d < f)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_079
    {a b c d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + 2 * b < 2 * c)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_080
    {a c d f g : ℕ}
    (h0 : 2 * g = a + 2 * f)
    (h1 : 3 * c < a + 2 * d)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_081
    {a b c d f g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * f < 2 * g)
    (h3 : a + d < f)
    (h4 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_082
    {a c d f g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * f < 2 * g)
    (h2 : a + d < f)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_083
    {a b c e : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_084
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_085
    {a b d e : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_086
    {a b d e : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_087
    {a b c d e : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 6 * b < 4 * d)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_088
    {a b c e : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_089
    {a b c d e : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 6 * b < 4 * d)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_090
    {a b c e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_091
    {a c d e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_092
    {a c d e : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    : a + 2 * d < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_093
    {a b c d e : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * d < 2 * e)
    : 3 * a + 6 * b < 4 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_094
    {a c d e : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    : 3 * c < 2 * e := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_095
    {a b e : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_096
    {a b e g : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_097
    {a b e : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    : 4 * e ≤ 3 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_098
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * g = 7 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_099
    {a b e g : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 7 * a + 6 * b < 4 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_100
    {a b e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_101
    {a b c e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_102
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_103
    {a b d e g : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_104
    {a d e g : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_105
    {a d e g : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : 3 * a + 2 * d < 2 * g)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_106
    {a b d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 6 * b < 4 * d)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_107
    {a b c d e g : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + e < g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_108
    {a d e g : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_109
    {a b c e g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_110
    {a b c d e g : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 6 * b < 4 * d)
    (h3 : a + e < g)
    (h4 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_111
    {c e : ℕ}
    (h0 : 2 * e < 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_112
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e < 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_113
    {c e : ℕ}
    (h0 : 2 * e = 3 * c)
    : 2 * e ≤ 3 * c := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_114
    {a c e g : ℕ}
    (h0 : 2 * a + 3 * c < 2 * g)
    (h1 : 2 * e = 3 * c)
    : a + e < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_115
    {a b c e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_116
    {a c e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + e < g)
    (h2 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_117
    {a c d e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_118
    {a c d e g : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + e < g)
    : 3 * a + 2 * d < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_119
    {a b c d e g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + e < g)
    (h4 : g < 4 * a)
    : a + 2 * b < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_120
    {a c d e g : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + e < g)
    (h3 : g < 4 * a)
    : 2 * c < g := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_121
    {a b e f : ℕ}
    (h0 : 4 * e < 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_122
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 4 * f = 5 * a + 6 * b)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_123
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_124
    {a b c e f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 4 * e = 3 * a + 6 * b)
    (h2 : 5 * a + 6 * b < 4 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_125
    {a b e f : ℕ}
    (h0 : 4 * e = 3 * a + 6 * b)
    (h1 : 5 * a + 6 * b < 4 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_126
    {a b e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_127
    {a b c e f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_128
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d < a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_129
    {a b d e f : ℕ}
    (h0 : 3 * a + 6 * b < 4 * e)
    (h1 : 4 * d = a + 6 * b)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_130
    {a d e f : ℕ}
    (h0 : 2 * e < a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_131
    {a d e f : ℕ}
    (h0 : 2 * e = a + 2 * d)
    (h1 : a + d < f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_132
    {a b d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : a + 6 * b < 4 * d)
    (h3 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_133
    {a b c d e f : ℕ}
    (h0 : 2 * c < a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 6 * b < 4 * d)
    (h4 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_134
    {a d e f : ℕ}
    (h0 : a + 2 * d < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_135
    {a b c e f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_136
    {a b c e f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : 3 * a + 6 * b < 4 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_137
    {a b c d e f : ℕ}
    (h0 : 2 * c = a + 2 * b)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : a + 6 * b < 4 * d)
    (h4 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_138
    {a c e f : ℕ}
    (h0 : 2 * e < 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_139
    {a c e f : ℕ}
    (h0 : 2 * e = 3 * c)
    (h1 : a + 3 * c < 2 * f)
    : a + 2 * e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_140
    {a b c e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * e < 2 * f)
    (h3 : c < 2 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_141
    {a c e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * e < 2 * f)
    (h2 : c < 2 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_142
    {a c d e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d < 3 * c)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_143
    {a c d e f : ℕ}
    (h0 : 3 * c < 2 * e)
    (h1 : a + 2 * d = 3 * c)
    (h2 : a + 2 * e < 2 * f)
    : a + d < f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_144
    {a b c d e f : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * b < 2 * c)
    (h2 : a + 2 * d < 2 * e)
    (h3 : a + 2 * e < 2 * f)
    (h4 : e < 3 * a)
    : a + 4 * b < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
private theorem sigmaSpeedTArith104_145
    {a c d e f : ℕ}
    (h0 : 3 * c < a + 2 * d)
    (h1 : a + 2 * d < 2 * e)
    (h2 : a + 2 * e < 2 * f)
    (h3 : e < 3 * a)
    : 4 * c < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
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
              exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
                Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
                Or.inr hBDlt, Or.inl hEz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
                Or.inr hBDlt, Or.inl hEz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
                Or.inr hBClt, Or.inr hBDlt, Or.inl hEz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_000 hBGlt)⟩
        · -- G ties B
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_004 hBGeq hAG), (by exact sigmaSpeedTArith104_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_004 hBGeq hAG), (by exact sigmaSpeedTArith104_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_005 hBGeq)⟩
        · -- G strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith104_007 hBClt hBGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_008 hBDlt hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_009 hBFlt hBGgt)⟩
      · -- F ties B
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_010 hAB hBFeq), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_000 hBGlt)⟩
        · -- G ties BF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_012 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_005 hBGeq)⟩
        · -- G strictly outranks BF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith104_007 hBClt hBGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_008 hBDlt hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_013 hBFeq hBGgt)⟩
      · -- F strictly outranks B
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith104_015 hBClt hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_016 hBDlt hBFgt), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith104_017 hFGeq hBFgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_018 hBClt hFGeq hBFgt hAG), Or.inr (by exact sigmaSpeedTArith104_016 hBDlt hBFgt), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_019 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith104_020 hBClt hBFgt hFGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_021 hBDlt hBFgt hFGgt), Or.inl hEz, Or.inr hFGgt⟩
    · -- D ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
                Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
                Or.inr hBClt, Or.inl hEz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
                Or.inr hBClt, Or.inl hEz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDFG ⟨hA, hBne, hDne, hFne, hGne, hBDeq,
                hmBFeq, hmBGeq, Or.inr hBClt, Or.inl hEz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_000 hBGlt)⟩
        · -- G ties BD
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_004 hBGeq hAG), (by exact sigmaSpeedTArith104_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_004 hBGeq hAG), (by exact sigmaSpeedTArith104_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_005 hBGeq)⟩
        · -- G strictly outranks BD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith104_007 hBClt hBGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_023 hBDeq hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_009 hBFlt hBGgt)⟩
      · -- F ties BD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_010 hAB hBFeq), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_000 hBGlt)⟩
        · -- G ties BDF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_012 hBFeq hBGeq hAG), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_005 hBGeq)⟩
        · -- G strictly outranks BDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith104_007 hBClt hBGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_023 hBDeq hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith104_015 hBClt hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_024 hBDeq hBFgt), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith104_017 hFGeq hBFgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_018 hBClt hFGeq hBFgt hAG), Or.inr (by exact sigmaSpeedTArith104_024 hBDeq hBFgt), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_019 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith104_020 hBClt hBFgt hFGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_025 hBDeq hBFgt hFGgt), Or.inl hEz, Or.inr hFGgt⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt),
            Or.inl hEz, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt), Or.inl hEz, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_027 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith104_028 hBClt hDGgt hBDgt hAG),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_029 hDGgt hDFlt)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt), Or.inl hEz, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt), Or.inl hEz⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_027 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith104_028 hBClt hDGgt hBDgt hAG),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_030 hDGgt hDFeq)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_031 hAF hBDgt hDFgt), Or.inr (by exact sigmaSpeedTArith104_032 hBClt hAF hBDgt hDFgt),
            Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith104_033 hFGeq hBDgt hDFgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_034 hBClt hFGeq hBDgt hDFgt hAG), Or.inr hDFgt, Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_035 hFGgt hBDgt hDFgt hAG), Or.inr (by exact sigmaSpeedTArith104_036 hBClt hFGgt hBDgt hDFgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_037 hFGgt hDFgt), Or.inl hEz, Or.inr hFGgt⟩
  · -- C ties B
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
              exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
                Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
                Or.inr hBDlt, Or.inl hEz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
                Or.inr hBDlt, Or.inl hEz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCFG ⟨hA, hBne, hCne, hFne, hGne, hBCeq,
                hmBFeq, hmBGeq, Or.inr hBDlt, Or.inl hEz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_000 hBGlt)⟩
        · -- G ties BC
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_039 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith104_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_039 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith104_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_005 hBGeq)⟩
        · -- G strictly outranks BC
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_040 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith104_041 hBCeq hBGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_008 hBDlt hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_009 hBFlt hBGgt)⟩
      · -- F ties BC
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_042 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_000 hBGlt)⟩
        · -- G ties BCF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_042 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_005 hBGeq)⟩
        · -- G strictly outranks BCF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_040 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith104_041 hBCeq hBGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_008 hBDlt hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BC
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_043 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith104_044 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_016 hBDlt hBFgt), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith104_043 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_044 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith104_016 hBDlt hBFgt), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_019 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith104_045 hBCeq hBFgt hFGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_021 hBDlt hBFgt hFGgt), Or.inl hEz, Or.inr hFGgt⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
                Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCDG ⟨hA, hBne, hCne, hDne, hGne, hBCeq, hBDeq,
                hmBGeq, Or.inl hEz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCDF ⟨hA, hBne, hCne, hDne, hFne, hBCeq, hBDeq,
                hmBFeq, Or.inl hEz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCDFG ⟨hA, hBne, hCne, hDne, hFne, hGne, hBCeq,
                hBDeq, hmBFeq, hmBGeq, Or.inl hEz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
                Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_000 hBGlt)⟩
        · -- G ties BCD
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_039 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith104_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_039 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith104_005 hBGeq),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_003 hBFlt)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_005 hBGeq)⟩
        · -- G strictly outranks BCD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_040 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith104_041 hBCeq hBGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_023 hBDeq hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_009 hBFlt hBGgt)⟩
      · -- F ties BCD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_042 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_000 hBGlt)⟩
        · -- G ties BCDF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_042 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_005 hBGeq)⟩
        · -- G strictly outranks BCDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_040 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith104_041 hBCeq hBGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_023 hBDeq hBGgt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_013 hBFeq hBGgt)⟩
      · -- F strictly outranks BCD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_043 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith104_044 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_024 hBDeq hBFgt), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith104_043 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_044 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith104_024 hBDeq hBFgt), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_019 hBFgt hFGgt hAG), Or.inr (by exact sigmaSpeedTArith104_045 hBCeq hBFgt hFGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_025 hBDeq hBFgt hFGgt), Or.inl hEz, Or.inr hFGgt⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt),
            Or.inl hEz, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt), Or.inl hEz, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_027 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith104_047 hBCeq hDGgt hBDgt hAG),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_029 hDGgt hDFlt)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt), Or.inl hEz, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt), Or.inl hEz⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_027 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith104_047 hBCeq hDGgt hBDgt hAG),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_030 hDGgt hDFeq)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_031 hAF hBDgt hDFgt), Or.inr (by exact sigmaSpeedTArith104_048 hBCeq hAF hBDgt hDFgt),
            Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith104_033 hFGeq hBDgt hDFgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_049 hBCeq hFGeq hBDgt hDFgt hAG), Or.inr hDFgt, Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_035 hFGgt hBDgt hDFgt hAG), Or.inr (by exact sigmaSpeedTArith104_050 hBCeq hFGgt hBDgt hDFgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_037 hFGgt hDFgt), Or.inl hEz, Or.inr hFGgt⟩
  · -- C strictly outranks B
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
              exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
                Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
                Or.inr hCDlt, Or.inl hEz, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith104_051 hCGlt),
                Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_054 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
                Or.inr hCDlt, Or.inl hEz, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
                Or.inr hBCgt, Or.inr hCDlt, Or.inl hEz⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith104_051 hCGlt),
                Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_054 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith104_054 hCFlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_051 hCGlt)⟩
        · -- G ties C
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith104_055 hCGeq hAC), (by exact sigmaSpeedTArith104_056 hCGeq),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_054 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith104_055 hCGeq hAC), (by exact sigmaSpeedTArith104_056 hCGeq),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_054 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith104_054 hCFlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_056 hCGeq)⟩
        · -- G strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_057 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith104_058 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_059 hCGgt hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_060 hCGgt hCFlt)⟩
      · -- F ties C
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith104_061 hCFeq hAC), (by exact sigmaSpeedTArith104_062 hCFeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_051 hCGlt)⟩
        · -- G ties CF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith104_061 hCFeq hAC), (by exact sigmaSpeedTArith104_062 hCFeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_056 hCGeq)⟩
        · -- G strictly outranks CF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_057 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith104_058 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_059 hCGgt hCDlt), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_063 hCGgt hCFeq)⟩
      · -- F strictly outranks C
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_064 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith104_065 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_066 hCDlt hCFgt), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith104_064 hBCgt hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_065 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith104_066 hCDlt hCFgt), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_067 hBCgt hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith104_068 hFGgt hCFgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_069 hCDlt hFGgt hCFgt), Or.inl hEz, Or.inr hFGgt⟩
    · -- D ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
                Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
                Or.inr hBCgt, Or.inl hEz, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith104_051 hCGlt),
                Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_054 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
                Or.inr hBCgt, Or.inl hEz, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDFG ⟨hA, hCne, hDne, hFne, hGne, hCDeq,
                hmCFeq, hmCGeq, Or.inr hBCgt, Or.inl hEz⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith104_051 hCGlt),
                Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_054 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith104_054 hCFlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_051 hCGlt)⟩
        · -- G ties CD
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith104_055 hCGeq hAC), (by exact sigmaSpeedTArith104_056 hCGeq),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_054 hCFlt)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith104_055 hCGeq hAC), (by exact sigmaSpeedTArith104_056 hCGeq),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_054 hCFlt)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith104_054 hCFlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_056 hCGeq)⟩
        · -- G strictly outranks CD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_057 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith104_058 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_071 hCGgt hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_060 hCGgt hCFlt)⟩
      · -- F ties CD
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith104_061 hCFeq hAC), (by exact sigmaSpeedTArith104_062 hCFeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_051 hCGlt)⟩
        · -- G ties CDF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith104_061 hCFeq hAC), (by exact sigmaSpeedTArith104_062 hCFeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_056 hCGeq)⟩
        · -- G strictly outranks CDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_057 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith104_058 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_071 hCGgt hCDeq), Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_063 hCGgt hCFeq)⟩
      · -- F strictly outranks CD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_064 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith104_065 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_072 hCDeq hCFgt), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith104_064 hBCgt hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_065 hCFgt hAC), Or.inr (by exact sigmaSpeedTArith104_072 hCDeq hCFgt), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_067 hBCgt hFGgt hCFgt hAG), Or.inr (by exact sigmaSpeedTArith104_068 hFGgt hCFgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_073 hCDeq hFGgt hCFgt), Or.inl hEz, Or.inr hFGgt⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt), Or.inr hCDgt,
            Or.inl hEz, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt),
            Or.inr hCDgt, Or.inl hEz, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_075 hDGgt hCDgt hBCgt hAG), Or.inr (by exact sigmaSpeedTArith104_076 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_029 hDGgt hDFlt)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt),
            Or.inr hCDgt, Or.inl hEz, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt), Or.inr hCDgt, Or.inl hEz⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_075 hDGgt hCDgt hBCgt hAG), Or.inr (by exact sigmaSpeedTArith104_076 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by exact sigmaSpeedTArith104_030 hDGgt hDFeq)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_077 hAF hCDgt hBCgt hDFgt), Or.inr (by exact sigmaSpeedTArith104_078 hAF hCDgt hDFgt),
            Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by exact sigmaSpeedTArith104_079 hFGeq hCDgt hBCgt hDFgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_080 hFGeq hCDgt hDFgt hAG), Or.inr hDFgt, Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_081 hCDgt hBCgt hFGgt hDFgt hAG), Or.inr (by exact sigmaSpeedTArith104_082 hCDgt hFGgt hDFgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_037 hFGgt hDFgt), Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
          Or.inr hBElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties B
        exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
          Or.inr hBDlt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_083 hBClt hBEgt),
          Or.inr (by exact sigmaSpeedTArith104_084 hBEgt hBDlt), Or.inl hFz, Or.inl hGz⟩
    · -- D ties B
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
          Or.inr hBElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties BD
        exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
          Or.inr hBClt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_083 hBClt hBEgt),
          Or.inr (by exact sigmaSpeedTArith104_085 hBEgt hBDeq), Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt),
          Or.inr hDElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties D
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
          Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt), Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_086 hDEgt hBDgt), Or.inr (by exact sigmaSpeedTArith104_087 hBClt hDEgt hBDgt),
          Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
          Or.inr hBElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties BC
        exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
          Or.inr hBDlt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_088 hBCeq hBEgt),
          Or.inr (by exact sigmaSpeedTArith104_084 hBEgt hBDlt), Or.inl hFz, Or.inl hGz⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
          Or.inr hBElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties BCD
        exact QuarticSigmaSupportCone810.sigmaBCDE ⟨hA, hBne, hCne, hDne, hEne, hBCeq, hBDeq,
          hBEeq, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks BCD
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_088 hBCeq hBEgt),
          Or.inr (by exact sigmaSpeedTArith104_085 hBEgt hBDeq), Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt),
          Or.inr hDElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties D
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
          Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt), Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_086 hDEgt hBDgt), Or.inr (by exact sigmaSpeedTArith104_089 hBCeq hDEgt hBDgt),
          Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
          Or.inr hCElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties C
        exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
          Or.inr hCDlt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_090 hCEgt hBCgt), Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith104_091 hCEgt hCDlt), Or.inl hFz, Or.inl hGz⟩
    · -- D ties C
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
          Or.inr hCElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties CD
        exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
          Or.inr hBCgt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_090 hCEgt hBCgt), Or.inr hCEgt,
          Or.inr (by exact sigmaSpeedTArith104_092 hCEgt hCDeq), Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt), Or.inr hCDgt,
          Or.inr hDElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties D
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt),
          Or.inr hCDgt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_093 hCDgt hBCgt hDEgt), Or.inr (by exact sigmaSpeedTArith104_094 hCDgt hDEgt),
          Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 91 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BCDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
              Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
              Or.inr hBDlt, Or.inr hBElt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hFz⟩
        · -- G ties B
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_004 hBGeq hAG), (by exact sigmaSpeedTArith104_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hFz⟩
        · -- G strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith104_007 hBClt hBGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_008 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith104_096 hBElt hBGgt), Or.inl hFz⟩
      · -- E ties B
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
              Or.inr hBDlt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
              Or.inr hBClt, Or.inr hBDlt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hFz⟩
        · -- G ties BE
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_098 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith104_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hFz⟩
        · -- G strictly outranks BE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith104_007 hBClt hBGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_008 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith104_099 hBEeq hBGgt), Or.inl hFz⟩
      · -- E strictly outranks B
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_083 hBClt hBEgt),
            Or.inr (by exact sigmaSpeedTArith104_084 hBEgt hBDlt), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith104_083 hBClt hBEgt), Or.inr (by exact sigmaSpeedTArith104_084 hBEgt hBDlt), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_100 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith104_101 hBClt hBEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_102 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inl hFz⟩
    · -- D ties B
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
              Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
              Or.inr hBClt, Or.inr hBElt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hFz⟩
        · -- G ties BD
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_004 hBGeq hAG), (by exact sigmaSpeedTArith104_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hFz⟩
        · -- G strictly outranks BD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith104_007 hBClt hBGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_023 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith104_096 hBElt hBGgt), Or.inl hFz⟩
      · -- E ties BD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
              Or.inr hBClt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDEG ⟨hA, hBne, hDne, hEne, hGne, hBDeq, hBEeq,
              hmBGeq, Or.inr hBClt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hFz⟩
        · -- G ties BDE
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_098 hBEeq hBGeq hAE), (by exact sigmaSpeedTArith104_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hFz⟩
        · -- G strictly outranks BDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_006 hBGgt hAG), Or.inr (by exact sigmaSpeedTArith104_007 hBClt hBGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_023 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith104_099 hBEeq hBGgt), Or.inl hFz⟩
      · -- E strictly outranks BD
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_083 hBClt hBEgt),
            Or.inr (by exact sigmaSpeedTArith104_085 hBEgt hBDeq), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith104_083 hBClt hBEgt), Or.inr (by exact sigmaSpeedTArith104_085 hBEgt hBDeq), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_100 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith104_101 hBClt hBEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_103 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inl hFz⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt),
            Or.inr hDElt, Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt), Or.inr hDElt, Or.inl hFz⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_027 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith104_028 hBClt hDGgt hBDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith104_104 hDElt hDGgt), Or.inl hFz⟩
      · -- E ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt), Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt), Or.inl hFz⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_027 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith104_028 hBClt hDGgt hBDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith104_105 hDEeq hDGgt), Or.inl hFz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_086 hDEgt hBDgt), Or.inr (by exact sigmaSpeedTArith104_087 hBClt hDEgt hBDgt),
            Or.inr hDEgt, Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith104_086 hDEgt hBDgt),
            Or.inr (by exact sigmaSpeedTArith104_087 hBClt hDEgt hBDgt), Or.inr hDEgt, Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_106 hDEgt hBDgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith104_107 hBClt hDEgt hBDgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_108 hDEgt hEGgt), Or.inr hEGgt, Or.inl hFz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
              Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
              Or.inr hBDlt, Or.inr hBElt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hFz⟩
        · -- G ties BC
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_039 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith104_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hFz⟩
        · -- G strictly outranks BC
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_040 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith104_041 hBCeq hBGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_008 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith104_096 hBElt hBGgt), Or.inl hFz⟩
      · -- E ties BC
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
              Or.inr hBDlt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCEG ⟨hA, hBne, hCne, hEne, hGne, hBCeq, hBEeq,
              hmBGeq, Or.inr hBDlt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hFz⟩
        · -- G ties BCE
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_039 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith104_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hFz⟩
        · -- G strictly outranks BCE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_040 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith104_041 hBCeq hBGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_008 hBDlt hBGgt), Or.inr (by exact sigmaSpeedTArith104_099 hBEeq hBGgt), Or.inl hFz⟩
      · -- E strictly outranks BC
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_088 hBCeq hBEgt),
            Or.inr (by exact sigmaSpeedTArith104_084 hBEgt hBDlt), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith104_088 hBCeq hBEgt), Or.inr (by exact sigmaSpeedTArith104_084 hBEgt hBDlt), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_100 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith104_109 hBCeq hBEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_102 hBEgt hBDlt hEGgt), Or.inr hEGgt, Or.inl hFz⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
              Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCDG ⟨hA, hBne, hCne, hDne, hGne, hBCeq, hBDeq,
              hmBGeq, Or.inr hBElt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hFz⟩
        · -- G ties BCD
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_039 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith104_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hFz⟩
        · -- G strictly outranks BCD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_040 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith104_041 hBCeq hBGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_023 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith104_096 hBElt hBGgt), Or.inl hFz⟩
      · -- E ties BCD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCDE ⟨hA, hBne, hCne, hDne, hEne, hBCeq, hBDeq,
              hBEeq, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCDEG ⟨hA, hBne, hCne, hDne, hEne, hGne, hBCeq,
              hBDeq, hBEeq, hmBGeq, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by exact sigmaSpeedTArith104_000 hBGlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hFz⟩
        · -- G ties BCDE
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by exact sigmaSpeedTArith104_039 hBCeq hBGeq hAC), (by exact sigmaSpeedTArith104_005 hBGeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hFz⟩
        · -- G strictly outranks BCDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_040 hBCeq hBGgt hAC), Or.inr (by exact sigmaSpeedTArith104_041 hBCeq hBGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_023 hBDeq hBGgt), Or.inr (by exact sigmaSpeedTArith104_099 hBEeq hBGgt), Or.inl hFz⟩
      · -- E strictly outranks BCD
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_088 hBCeq hBEgt),
            Or.inr (by exact sigmaSpeedTArith104_085 hBEgt hBDeq), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith104_088 hBCeq hBEgt), Or.inr (by exact sigmaSpeedTArith104_085 hBEgt hBDeq), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_100 hBEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith104_109 hBCeq hBEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_103 hBEgt hBDeq hEGgt), Or.inr hEGgt, Or.inl hFz⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt),
            Or.inr hDElt, Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt), Or.inr hDElt, Or.inl hFz⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_027 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith104_047 hBCeq hDGgt hBDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith104_104 hDElt hDGgt), Or.inl hFz⟩
      · -- E ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt), Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt), Or.inl hFz⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_027 hDGgt hBDgt hAG), Or.inr (by exact sigmaSpeedTArith104_047 hBCeq hDGgt hBDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith104_105 hDEeq hDGgt), Or.inl hFz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_086 hDEgt hBDgt), Or.inr (by exact sigmaSpeedTArith104_089 hBCeq hDEgt hBDgt),
            Or.inr hDEgt, Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith104_086 hDEgt hBDgt),
            Or.inr (by exact sigmaSpeedTArith104_089 hBCeq hDEgt hBDgt), Or.inr hDEgt, Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_106 hDEgt hBDgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith104_110 hBCeq hDEgt hBDgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_108 hDEgt hEGgt), Or.inr hEGgt, Or.inl hFz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
              Or.inr hCElt, Or.inl hFz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
              Or.inr hCDlt, Or.inr hCElt, Or.inl hFz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith104_051 hCGlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inr (by exact sigmaSpeedTArith104_111 hCElt), Or.inl hFz⟩
        · -- G ties C
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith104_055 hCGeq hAC), (by exact sigmaSpeedTArith104_056 hCGeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inr (by exact sigmaSpeedTArith104_111 hCElt), Or.inl hFz⟩
        · -- G strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_057 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith104_058 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_059 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith104_112 hCGgt hCElt), Or.inl hFz⟩
      · -- E ties C
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
              Or.inr hCDlt, Or.inl hFz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
              Or.inr hBCgt, Or.inr hCDlt, Or.inl hFz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith104_051 hCGlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inr (by exact sigmaSpeedTArith104_113 hCEeq), Or.inl hFz⟩
        · -- G ties CE
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith104_055 hCGeq hAC), (by exact sigmaSpeedTArith104_056 hCGeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inr (by exact sigmaSpeedTArith104_113 hCEeq), Or.inl hFz⟩
        · -- G strictly outranks CE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_057 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith104_058 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_059 hCGgt hCDlt), Or.inr (by exact sigmaSpeedTArith104_114 hCGgt hCEeq), Or.inl hFz⟩
      · -- E strictly outranks C
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_090 hCEgt hBCgt), Or.inr hCEgt,
            Or.inr (by exact sigmaSpeedTArith104_091 hCEgt hCDlt), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith104_090 hCEgt hBCgt),
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith104_091 hCEgt hCDlt), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_115 hCEgt hBCgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith104_116 hCEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_117 hCEgt hCDlt hEGgt), Or.inr hEGgt, Or.inl hFz⟩
    · -- D ties C
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
              Or.inr hCElt, Or.inl hFz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
              Or.inr hBCgt, Or.inr hCElt, Or.inl hFz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith104_051 hCGlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inr (by exact sigmaSpeedTArith104_111 hCElt), Or.inl hFz⟩
        · -- G ties CD
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith104_055 hCGeq hAC), (by exact sigmaSpeedTArith104_056 hCGeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inr (by exact sigmaSpeedTArith104_111 hCElt), Or.inl hFz⟩
        · -- G strictly outranks CD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_057 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith104_058 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_071 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith104_112 hCGgt hCElt), Or.inl hFz⟩
      · -- E ties CD
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
              Or.inr hBCgt, Or.inl hFz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDEG ⟨hA, hCne, hDne, hEne, hGne, hCDeq, hCEeq,
              hmCGeq, Or.inr hBCgt, Or.inl hFz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by exact sigmaSpeedTArith104_051 hCGlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inr (by exact sigmaSpeedTArith104_113 hCEeq), Or.inl hFz⟩
        · -- G ties CDE
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by exact sigmaSpeedTArith104_055 hCGeq hAC), (by exact sigmaSpeedTArith104_056 hCGeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inr (by exact sigmaSpeedTArith104_113 hCEeq), Or.inl hFz⟩
        · -- G strictly outranks CDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_057 hCGgt hBCgt hAC), Or.inr (by exact sigmaSpeedTArith104_058 hCGgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_071 hCGgt hCDeq), Or.inr (by exact sigmaSpeedTArith104_114 hCGgt hCEeq), Or.inl hFz⟩
      · -- E strictly outranks CD
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_090 hCEgt hBCgt), Or.inr hCEgt,
            Or.inr (by exact sigmaSpeedTArith104_092 hCEgt hCDeq), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith104_090 hCEgt hBCgt),
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith104_092 hCEgt hCDeq), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_115 hCEgt hBCgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith104_116 hCEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_118 hCEgt hCDeq hEGgt), Or.inr hEGgt, Or.inl hFz⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt), Or.inr hCDgt,
            Or.inr hDElt, Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt),
            Or.inr hCDgt, Or.inr hDElt, Or.inl hFz⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_075 hDGgt hCDgt hBCgt hAG), Or.inr (by exact sigmaSpeedTArith104_076 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith104_104 hDElt hDGgt), Or.inl hFz⟩
      · -- E ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt),
            Or.inr hCDgt, Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt), Or.inr hCDgt, Or.inl hFz⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_075 hDGgt hCDgt hBCgt hAG), Or.inr (by exact sigmaSpeedTArith104_076 hDGgt hCDgt hAG),
            Or.inr hDGgt, Or.inr (by exact sigmaSpeedTArith104_105 hDEeq hDGgt), Or.inl hFz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_093 hCDgt hBCgt hDEgt), Or.inr (by exact sigmaSpeedTArith104_094 hCDgt hDEgt),
            Or.inr hDEgt, Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by exact sigmaSpeedTArith104_093 hCDgt hBCgt hDEgt),
            Or.inr (by exact sigmaSpeedTArith104_094 hCDgt hDEgt), Or.inr hDEgt, Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by exact sigmaSpeedTArith104_119 hCDgt hBCgt hDEgt hEGgt hAG), Or.inr (by exact sigmaSpeedTArith104_120 hCDgt hDEgt hEGgt hAG),
            Or.inr (by exact sigmaSpeedTArith104_108 hDEgt hEGgt), Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
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
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
              Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
              Or.inr hBDlt, Or.inr hBElt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hGz⟩
        · -- F ties B
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_010 hAB hBFeq), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hGz⟩
        · -- F strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith104_015 hBClt hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_016 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith104_121 hBElt hBFgt), Or.inl hGz⟩
      · -- E ties B
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
              Or.inr hBDlt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
              Or.inr hBClt, Or.inr hBDlt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hGz⟩
        · -- F ties BE
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_122 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hGz⟩
        · -- F strictly outranks BE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_123 hBEeq hBFgt hAE), Or.inr (by exact sigmaSpeedTArith104_124 hBClt hBEeq hBFgt hAE),
            Or.inr (by exact sigmaSpeedTArith104_016 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith104_125 hBEeq hBFgt), Or.inl hGz⟩
      · -- E strictly outranks B
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_083 hBClt hBEgt),
            Or.inr (by exact sigmaSpeedTArith104_084 hBEgt hBDlt), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith104_083 hBClt hBEgt), Or.inr (by exact sigmaSpeedTArith104_084 hBEgt hBDlt), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_126 hBEgt hEFgt hAE), Or.inr (by exact sigmaSpeedTArith104_127 hBClt hBEgt hEFgt hAE),
            Or.inr (by exact sigmaSpeedTArith104_128 hBEgt hBDlt hEFgt), Or.inr hEFgt, Or.inl hGz⟩
    · -- D ties B
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
              Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
              Or.inr hBClt, Or.inr hBElt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hGz⟩
        · -- F ties BD
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_010 hAB hBFeq), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hGz⟩
        · -- F strictly outranks BD
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_014 hAB hBFgt), Or.inr (by exact sigmaSpeedTArith104_015 hBClt hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_024 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith104_121 hBElt hBFgt), Or.inl hGz⟩
      · -- E ties BD
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
              Or.inr hBClt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBDEF ⟨hA, hBne, hDne, hEne, hFne, hBDeq, hBEeq,
              hmBFeq, Or.inr hBClt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hGz⟩
        · -- F ties BDE
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_122 hBEeq hBFeq hAE), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_001 hBClt), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hGz⟩
        · -- F strictly outranks BDE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_123 hBEeq hBFgt hAE), Or.inr (by exact sigmaSpeedTArith104_124 hBClt hBEeq hBFgt hAE),
            Or.inr (by exact sigmaSpeedTArith104_024 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith104_125 hBEeq hBFgt), Or.inl hGz⟩
      · -- E strictly outranks BD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_083 hBClt hBEgt),
            Or.inr (by exact sigmaSpeedTArith104_085 hBEgt hBDeq), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith104_083 hBClt hBEgt), Or.inr (by exact sigmaSpeedTArith104_085 hBEgt hBDeq), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_126 hBEgt hEFgt hAE), Or.inr (by exact sigmaSpeedTArith104_127 hBClt hBEgt hEFgt hAE),
            Or.inr (by exact sigmaSpeedTArith104_129 hBEgt hBDeq hEFgt), Or.inr hEFgt, Or.inl hGz⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt),
            Or.inr hDElt, Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties D
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt), Or.inr hDElt, Or.inl hGz⟩
        · -- F strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_031 hAF hBDgt hDFgt), Or.inr (by exact sigmaSpeedTArith104_032 hBClt hAF hBDgt hDFgt),
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith104_130 hDElt hDFgt), Or.inl hGz⟩
      · -- E ties D
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt), Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties DE
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_026 hBClt hBDgt), Or.inl hGz⟩
        · -- F strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_031 hAF hBDgt hDFgt), Or.inr (by exact sigmaSpeedTArith104_032 hBClt hAF hBDgt hDFgt),
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith104_131 hDEeq hDFgt), Or.inl hGz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_086 hDEgt hBDgt), Or.inr (by exact sigmaSpeedTArith104_087 hBClt hDEgt hBDgt),
            Or.inr hDEgt, Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith104_086 hDEgt hBDgt),
            Or.inr (by exact sigmaSpeedTArith104_087 hBClt hDEgt hBDgt), Or.inr hDEgt, Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_132 hDEgt hEFgt hBDgt hAE), Or.inr (by exact sigmaSpeedTArith104_133 hBClt hDEgt hEFgt hBDgt hAE),
            Or.inr (by exact sigmaSpeedTArith104_134 hDEgt hEFgt), Or.inr hEFgt, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
              Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
              Or.inr hBDlt, Or.inr hBElt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hGz⟩
        · -- F ties BC
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_042 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hGz⟩
        · -- F strictly outranks BC
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_043 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith104_044 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_016 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith104_121 hBElt hBFgt), Or.inl hGz⟩
      · -- E ties BC
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
              Or.inr hBDlt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCEF ⟨hA, hBne, hCne, hEne, hFne, hBCeq, hBEeq,
              hmBFeq, Or.inr hBDlt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hGz⟩
        · -- F ties BCE
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_042 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_002 hBDlt), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hGz⟩
        · -- F strictly outranks BCE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_043 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith104_044 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_016 hBDlt hBFgt), Or.inr (by exact sigmaSpeedTArith104_125 hBEeq hBFgt), Or.inl hGz⟩
      · -- E strictly outranks BC
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_088 hBCeq hBEgt),
            Or.inr (by exact sigmaSpeedTArith104_084 hBEgt hBDlt), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith104_088 hBCeq hBEgt), Or.inr (by exact sigmaSpeedTArith104_084 hBEgt hBDlt), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_135 hBCeq hBEgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith104_136 hBCeq hBEgt hEFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_128 hBEgt hBDlt hEFgt), Or.inr hEFgt, Or.inl hGz⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
              Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCDF ⟨hA, hBne, hCne, hDne, hFne, hBCeq, hBDeq,
              hmBFeq, Or.inr hBElt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hGz⟩
        · -- F ties BCD
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_042 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_095 hBElt), Or.inl hGz⟩
        · -- F strictly outranks BCD
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_043 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith104_044 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_024 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith104_121 hBElt hBFgt), Or.inl hGz⟩
      · -- E ties BCD
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCDE ⟨hA, hBne, hCne, hDne, hEne, hBCeq, hBDeq,
              hBEeq, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCDEF ⟨hA, hBne, hCne, hDne, hEne, hFne, hBCeq,
              hBDeq, hBEeq, hmBFeq, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by exact sigmaSpeedTArith104_003 hBFlt),
              Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hGz⟩
        · -- F ties BCDE
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by exact sigmaSpeedTArith104_042 hBCeq hBFeq hAC), (by exact sigmaSpeedTArith104_011 hBFeq),
            Or.inr (by exact sigmaSpeedTArith104_038 hBCeq), Or.inr (by exact sigmaSpeedTArith104_022 hBDeq), Or.inr (by exact sigmaSpeedTArith104_097 hBEeq), Or.inl hGz⟩
        · -- F strictly outranks BCDE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_043 hBCeq hBFgt hAC), Or.inr (by exact sigmaSpeedTArith104_044 hBCeq hBFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_024 hBDeq hBFgt), Or.inr (by exact sigmaSpeedTArith104_125 hBEeq hBFgt), Or.inl hGz⟩
      · -- E strictly outranks BCD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by exact sigmaSpeedTArith104_088 hBCeq hBEgt),
            Or.inr (by exact sigmaSpeedTArith104_085 hBEgt hBDeq), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by exact sigmaSpeedTArith104_088 hBCeq hBEgt), Or.inr (by exact sigmaSpeedTArith104_085 hBEgt hBDeq), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_135 hBCeq hBEgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith104_136 hBCeq hBEgt hEFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_129 hBEgt hBDeq hEFgt), Or.inr hEFgt, Or.inl hGz⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt),
            Or.inr hDElt, Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties D
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt), Or.inr hDElt, Or.inl hGz⟩
        · -- F strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_031 hAF hBDgt hDFgt), Or.inr (by exact sigmaSpeedTArith104_048 hBCeq hAF hBDgt hDFgt),
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith104_130 hDElt hDFgt), Or.inl hGz⟩
      · -- E ties D
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt), Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties DE
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inr hBDgt, Or.inr (by exact sigmaSpeedTArith104_046 hBCeq hBDgt), Or.inl hGz⟩
        · -- F strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_031 hAF hBDgt hDFgt), Or.inr (by exact sigmaSpeedTArith104_048 hBCeq hAF hBDgt hDFgt),
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith104_131 hDEeq hDFgt), Or.inl hGz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_086 hDEgt hBDgt), Or.inr (by exact sigmaSpeedTArith104_089 hBCeq hDEgt hBDgt),
            Or.inr hDEgt, Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith104_086 hDEgt hBDgt),
            Or.inr (by exact sigmaSpeedTArith104_089 hBCeq hDEgt hBDgt), Or.inr hDEgt, Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_132 hDEgt hEFgt hBDgt hAE), Or.inr (by exact sigmaSpeedTArith104_137 hBCeq hDEgt hEFgt hBDgt hAE),
            Or.inr (by exact sigmaSpeedTArith104_134 hDEgt hEFgt), Or.inr hEFgt, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
              Or.inr hCElt, Or.inr hmCFlt, Or.inl hGz⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
              Or.inr hCDlt, Or.inr hCElt, Or.inl hGz⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith104_054 hCFlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inr (by exact sigmaSpeedTArith104_111 hCElt), Or.inl hGz⟩
        · -- F ties C
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith104_061 hCFeq hAC), (by exact sigmaSpeedTArith104_062 hCFeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inr (by exact sigmaSpeedTArith104_111 hCElt), Or.inl hGz⟩
        · -- F strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_064 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith104_065 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_066 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith104_138 hCElt hCFgt), Or.inl hGz⟩
      · -- E ties C
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
              Or.inr hCDlt, Or.inr hmCFlt, Or.inl hGz⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
              Or.inr hBCgt, Or.inr hCDlt, Or.inl hGz⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith104_054 hCFlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inr (by exact sigmaSpeedTArith104_113 hCEeq), Or.inl hGz⟩
        · -- F ties CE
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith104_061 hCFeq hAC), (by exact sigmaSpeedTArith104_062 hCFeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_053 hCDlt), Or.inr (by exact sigmaSpeedTArith104_113 hCEeq), Or.inl hGz⟩
        · -- F strictly outranks CE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_064 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith104_065 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_066 hCDlt hCFgt), Or.inr (by exact sigmaSpeedTArith104_139 hCEeq hCFgt), Or.inl hGz⟩
      · -- E strictly outranks C
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_090 hCEgt hBCgt), Or.inr hCEgt,
            Or.inr (by exact sigmaSpeedTArith104_091 hCEgt hCDlt), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith104_090 hCEgt hBCgt),
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith104_091 hCEgt hCDlt), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_140 hCEgt hBCgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith104_141 hCEgt hEFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_142 hCEgt hCDlt hEFgt), Or.inr hEFgt, Or.inl hGz⟩
    · -- D ties C
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
              Or.inr hCElt, Or.inr hmCFlt, Or.inl hGz⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
              Or.inr hBCgt, Or.inr hCElt, Or.inl hGz⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith104_054 hCFlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inr (by exact sigmaSpeedTArith104_111 hCElt), Or.inl hGz⟩
        · -- F ties CD
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith104_061 hCFeq hAC), (by exact sigmaSpeedTArith104_062 hCFeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inr (by exact sigmaSpeedTArith104_111 hCElt), Or.inl hGz⟩
        · -- F strictly outranks CD
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_064 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith104_065 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_072 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith104_138 hCElt hCFgt), Or.inl hGz⟩
      · -- E ties CD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
              Or.inr hBCgt, Or.inr hmCFlt, Or.inl hGz⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCDEF ⟨hA, hCne, hDne, hEne, hFne, hCDeq, hCEeq,
              hmCFeq, Or.inr hBCgt, Or.inl hGz⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by exact sigmaSpeedTArith104_054 hCFlt),
              Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inr (by exact sigmaSpeedTArith104_113 hCEeq), Or.inl hGz⟩
        · -- F ties CDE
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by exact sigmaSpeedTArith104_061 hCFeq hAC), (by exact sigmaSpeedTArith104_062 hCFeq),
            Or.inr (by exact sigmaSpeedTArith104_052 hBCgt), Or.inr (by exact sigmaSpeedTArith104_070 hCDeq), Or.inr (by exact sigmaSpeedTArith104_113 hCEeq), Or.inl hGz⟩
        · -- F strictly outranks CDE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_064 hBCgt hCFgt hAC), Or.inr (by exact sigmaSpeedTArith104_065 hCFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_072 hCDeq hCFgt), Or.inr (by exact sigmaSpeedTArith104_139 hCEeq hCFgt), Or.inl hGz⟩
      · -- E strictly outranks CD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_090 hCEgt hBCgt), Or.inr hCEgt,
            Or.inr (by exact sigmaSpeedTArith104_092 hCEgt hCDeq), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith104_090 hCEgt hBCgt),
            Or.inr hCEgt, Or.inr (by exact sigmaSpeedTArith104_092 hCEgt hCDeq), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_140 hCEgt hBCgt hEFgt hAC), Or.inr (by exact sigmaSpeedTArith104_141 hCEgt hEFgt hAC),
            Or.inr (by exact sigmaSpeedTArith104_143 hCEgt hCDeq hEFgt), Or.inr hEFgt, Or.inl hGz⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt), Or.inr hCDgt,
            Or.inr hDElt, Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties D
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt),
            Or.inr hCDgt, Or.inr hDElt, Or.inl hGz⟩
        · -- F strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_077 hAF hCDgt hBCgt hDFgt), Or.inr (by exact sigmaSpeedTArith104_078 hAF hCDgt hDFgt),
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith104_130 hDElt hDFgt), Or.inl hGz⟩
      · -- E ties D
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt),
            Or.inr hCDgt, Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties DE
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inr (by exact sigmaSpeedTArith104_074 hCDgt hBCgt), Or.inr hCDgt, Or.inl hGz⟩
        · -- F strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_077 hAF hCDgt hBCgt hDFgt), Or.inr (by exact sigmaSpeedTArith104_078 hAF hCDgt hDFgt),
            Or.inr hDFgt, Or.inr (by exact sigmaSpeedTArith104_131 hDEeq hDFgt), Or.inl hGz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by exact sigmaSpeedTArith104_093 hCDgt hBCgt hDEgt), Or.inr (by exact sigmaSpeedTArith104_094 hCDgt hDEgt),
            Or.inr hDEgt, Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by exact sigmaSpeedTArith104_093 hCDgt hBCgt hDEgt),
            Or.inr (by exact sigmaSpeedTArith104_094 hCDgt hDEgt), Or.inr hDEgt, Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by exact sigmaSpeedTArith104_144 hCDgt hBCgt hDEgt hEFgt hAE), Or.inr (by exact sigmaSpeedTArith104_145 hCDgt hDEgt hEFgt hAE),
            Or.inr (by exact sigmaSpeedTArith104_134 hDEgt hEFgt), Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 50 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
/-- κ kills `zeta` when `2s > 7 a`, expanded per letter. -/
def QuarticKappaLoadTopZeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    (C = 0 ∨ 4 * C.natDegree < A.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < 3 * A.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 5 * A.natDegree) ∧
    (F = 0 ∨ 4 * F.natDegree < 7 * A.natDegree) ∧
    (G = 0 ∨ 4 * G.natDegree < 9 * A.natDegree)


set_option maxHeartbeats 64000000 in
theorem quarticKappaLoadTopL810_bounds
    {A B C D E F G : k[X]}
    (h : QuarticKappaLoadTopL810 A B C D E F G) :
    0 < A.natDegree ∧
      2 * B.natDegree < 3 * A.natDegree ∧
      C.natDegree < 2 * A.natDegree ∧
      2 * D.natDegree < 5 * A.natDegree ∧
      E.natDegree < 3 * A.natDegree ∧
      2 * F.natDegree < 7 * A.natDegree ∧
      G.natDegree < 4 * A.natDegree ∧
      4 * B.natDegree < 5 * A.natDegree ∧
      4 * C.natDegree < 7 * A.natDegree ∧
      4 * D.natDegree < 9 * A.natDegree ∧
      4 * E.natDegree < 11 * A.natDegree ∧
      4 * F.natDegree < 13 * A.natDegree ∧
      4 * G.natDegree < 15 * A.natDegree := by
  rcases h with ⟨hA, hB, hC, hD, hE, hF, hG⟩
  rcases hA with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  refine ⟨hApos, by omega, by omega, by omega, by omega, by omega, by omega,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hB with h0 | hlt
    · have : B.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  · rcases hC with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  · rcases hD with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  · rcases hE with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  · rcases hF with h0 | hlt
    · have : F.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  · rcases hG with h0 | hlt
    · have : G.natDegree = 0 := by simp [h0]
      omega
    · exact hlt


end QuarticKappaLadder810
end Max11DegreeRoutes
end
