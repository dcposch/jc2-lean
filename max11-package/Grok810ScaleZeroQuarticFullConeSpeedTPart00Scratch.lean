import Grok810ScaleZeroQuarticDefsScratch

/-! # Full 7-letter cone `R = {A,B,C,D,E,F,G}` of normalized `(8,10)`, `H = 0`

Continuation of `Grok810ScaleZeroQuarticConesScratch`.  That file exports
`normalized810ScaleZero_quarticADominantResidual` whose last conjunct is
`QuarticRatioConeA810 ∨ QuarticRatioConeABCDEFG810`.  This file treats the
ABCDEFG branch only.

CAS (Singular, weighted grevlex, Rabinowitsch `T·abcdefg-1`): the saturated
load-free ideal on this cone is `(1)`.  The Groebner basis contains `g^7`
and `c d f² g²`.  Explicit lift multipliers have ~300-digit coefficients,
too large for Lean `ring`.  Lean has the G-eliminating Sylvester cores
(plan §6) and the next a-resultant layer: 2×2 identities of the cores
linear in `a`, the deg-1/deg-2 Sylvester of `ν` against `ο`, and the
weight-26 combination `R_ο − 10 b⁴ d R_{μν} = 8 b⁶ d T` whose factor `T`
is linear in `e`.  The remaining Groebner `(1)` certificate among the
e-free faces is not transcribed.

No `sorry`, no new axioms, no finite-root shortcut.  Untracked working
note.
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

section QuarticFullConeABCDEFG810

variable {k : Type*} [Field k] [CharZero k]


/-! ## Restricted inners and Sylvester cores -/

set_option maxHeartbeats 64000000 in
def kappaQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + (-60 : k) * b * c ^ 2 + 160 * b * g + 160 * c * f + 160 * d * e

set_option maxHeartbeats 64000000 in
def muQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  60 * a * b ^ 2 * c + (-160 : k) * a * b * f + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * c * g + 640 * d * f + 320 * e ^ 2

set_option maxHeartbeats 64000000 in
def nuQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + 60 * a * b * c ^ 2 + (-160 : k) * a * b * g + (-160 : k) * a * c * f + (-160 : k) * a * d * e + 280 * b ^ 3 * c + (-480 : k) * b ^ 2 * f + (-960 : k) * b * c * e + (-480 : k) * b * d ^ 2 + (-480 : k) * c ^ 2 * d + 1280 * d * g + 1280 * e * f

set_option maxHeartbeats 64000000 in
def xiQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + 120 * a * b * c * d + (-160 : k) * a * d * f + 110 * b ^ 3 * d + 180 * b ^ 2 * c ^ 2 + (-160 : k) * b ^ 2 * g + (-400 : k) * b * c * f + (-400 : k) * b * d * e + (-240 : k) * c ^ 2 * e + (-240 : k) * c * d ^ 2 + 640 * e * g + 320 * f ^ 2

set_option maxHeartbeats 64000000 in
def omicronQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * b * g + (-160 : k) * a ^ 2 * c * f + (-160 : k) * a ^ 2 * d * e + (-1120 : k) * a * b ^ 3 * c + 1600 * a * b ^ 2 * f + 1920 * a * b * c * e + 2240 * a * b * d ^ 2 + 960 * a * c ^ 2 * d + (-2560 : k) * a * d * g + (-2560 : k) * a * e * f + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + 8640 * b ^ 2 * c * d + 2880 * b * c ^ 3 + (-7680 : k) * b * c * g + (-10240 : k) * b * d * f + (-5120 : k) * b * e ^ 2 + (-5120 : k) * c ^ 2 * f + (-12800 : k) * c * d * e + (-2560 : k) * d ^ 3 + 20480 * f * g

set_option maxHeartbeats 64000000 in
def piQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + (-360 : k) * a * b ^ 2 * c ^ 2 + 320 * a * b ^ 2 * g + 640 * a * b * c * f + 1280 * a * b * d * e + 640 * a * c * d ^ 2 + (-1280 : k) * a * f ^ 2 + (-560 : k) * b ^ 4 * c + 800 * b ^ 3 * f + 2880 * b ^ 2 * c * e + 1440 * b ^ 2 * d ^ 2 + 2880 * b * c ^ 2 * d + (-2560 : k) * b * d * g + (-3840 : k) * b * e * f + 240 * c ^ 4 + (-1280 : k) * c ^ 2 * g + (-3840 : k) * c * d * f + (-2560 : k) * c * e ^ 2 + (-2560 : k) * d ^ 2 * e + 5120 * g ^ 2

set_option maxHeartbeats 64000000 in
def primitiveQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * b * g + (-160 : k) * a ^ 3 * c * f + (-160 : k) * a ^ 3 * d * e + 120 * a ^ 2 * b ^ 3 * c + (-160 : k) * a ^ 2 * b ^ 2 * f + 960 * a ^ 2 * b * c * e + (-800 : k) * a ^ 2 * b * d ^ 2 + 480 * a ^ 2 * c ^ 2 * d + (-1280 : k) * a ^ 2 * d * g + (-1280 : k) * a ^ 2 * e * f + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + (-8640 : k) * a * b ^ 2 * c * d + (-960 : k) * a * b * c ^ 3 + 2560 * a * b * c * g + 10240 * a * b * d * f + 5120 * a * b * e ^ 2 + 7680 * a * c * d * e + 2560 * a * d ^ 3 + (-20480 : k) * a * f * g + (-4000 : k) * b ^ 4 * d + (-8480 : k) * b ^ 3 * c ^ 2 + 3840 * b ^ 3 * g + 21760 * b ^ 2 * c * f + 21760 * b ^ 2 * d * e + 23040 * b * c ^ 2 * e + 23040 * b * c * d ^ 2 + (-20480 : k) * b * e * g + (-20480 : k) * b * f ^ 2 + 7680 * c ^ 3 * d + (-20480 : k) * c * d * g + (-40960 : k) * c * e * f + (-20480 : k) * d ^ 2 * f + (-20480 : k) * d * e ^ 2

set_option maxHeartbeats 64000000 in
def quarticCoreMuABCDEFG810 (a b c d e f : k) : k :=
  8 * a * b ^ 3 * c + (-32 : k) * a * b ^ 2 * f + (-16 : k) * a * b * d ^ 2 + 7 * b ^ 5 + (-48 : k) * b ^ 3 * e + (-48 : k) * b ^ 2 * c * d + 32 * b * c ^ 3 + 128 * b * d * f + 64 * b * e ^ 2 + (-128 : k) * c ^ 2 * f + (-128 : k) * c * d * e

set_option maxHeartbeats 64000000 in
def quarticCoreNuABCDEFG810 (a b c d e f : k) : k :=
  2 * a * b ^ 3 * d + 7 * b ^ 4 * c + (-12 : k) * b ^ 3 * f + (-24 : k) * b ^ 2 * c * e + 32 * b * e * f + (-32 : k) * c * d * f + (-32 : k) * d ^ 2 * e

set_option maxHeartbeats 64000000 in
def quarticCoreXiABCDEFG810 (a b c d e f : k) : k :=
  -a * b ^ 5 + 4 * a * b ^ 3 * e + 12 * a * b ^ 2 * c * d + (-16 : k) * a * b * d * f + 5 * b ^ 4 * d + 12 * b ^ 3 * c ^ 2 + (-24 : k) * b ^ 2 * c * f + (-24 : k) * b * c * d ^ 2 + 32 * b * f ^ 2 + (-64 : k) * c * e * f + (-64 : k) * d * e ^ 2

set_option maxHeartbeats 64000000 in
def quarticCoreOmicronABCDEFG810 (a b c d e f : k) : k :=
  (-10 : k) * a ^ 2 * b ^ 3 * d + (-55 : k) * a * b ^ 4 * c + 60 * a * b ^ 3 * f + 120 * a * b ^ 2 * c * e + 80 * a * b ^ 2 * d ^ 2 + (-160 : k) * a * b * e * f + 160 * a * c * d * f + 160 * a * d ^ 2 * e + (-21 : k) * b ^ 6 + 160 * b ^ 4 * e + 360 * b ^ 3 * c * d + (-160 : k) * b ^ 2 * d * f + (-320 : k) * b ^ 2 * e ^ 2 + 640 * b * c ^ 2 * f + (-320 : k) * b * c * d * e + (-160 : k) * b * d ^ 3 + (-1280 : k) * c * f ^ 2 + (-1280 : k) * d * e * f

set_option maxHeartbeats 64000000 in
def quarticCorePiABCDEFG810 (a b c d e f : k) : k :=
  a ^ 2 * b ^ 6 + (-40 : k) * a * b ^ 5 * d + (-32 : k) * a * b ^ 4 * c ^ 2 + 64 * a * b ^ 3 * c * f + 128 * a * b ^ 3 * d * e + 64 * a * b ^ 2 * c * d ^ 2 + (-128 : k) * a * b ^ 2 * f ^ 2 + (-56 : k) * b ^ 6 * c + 80 * b ^ 5 * f + 288 * b ^ 4 * c * e + 120 * b ^ 4 * d ^ 2 + 288 * b ^ 3 * c ^ 2 * d + (-384 : k) * b ^ 3 * e * f + 48 * b ^ 2 * c ^ 4 + (-512 : k) * b ^ 2 * c * d * f + (-256 : k) * b ^ 2 * c * e ^ 2 + (-384 : k) * b ^ 2 * d ^ 2 * e + (-256 : k) * b * c ^ 3 * f + (-256 : k) * b * c ^ 2 * d * e + 512 * c ^ 2 * f ^ 2 + 1024 * c * d * e * f + 512 * d ^ 2 * e ^ 2

set_option maxHeartbeats 64000000 in
def quarticCorePrimitiveABCDEFG810 (a b c d e f : k) : k :=
  (-2 : k) * a ^ 3 * b ^ 3 * d + a ^ 2 * b ^ 4 * c + 12 * a ^ 2 * b ^ 3 * f + 24 * a ^ 2 * b ^ 2 * c * e + (-32 : k) * a ^ 2 * b ^ 2 * d ^ 2 + (-32 : k) * a ^ 2 * b * e * f + 32 * a ^ 2 * c * d * f + 32 * a ^ 2 * d ^ 2 * e + 10 * a * b ^ 6 + (-64 : k) * a * b ^ 4 * e + (-176 : k) * a * b ^ 3 * c * d + 64 * a * b ^ 2 * d * f + 128 * a * b ^ 2 * e ^ 2 + (-256 : k) * a * b * c ^ 2 * f + 128 * a * b * c * d * e + 64 * a * b * d ^ 3 + 512 * a * c * f ^ 2 + 512 * a * d * e * f + (-64 : k) * b ^ 5 * d + (-176 : k) * b ^ 4 * c ^ 2 + 448 * b ^ 3 * c * f + 256 * b ^ 3 * d * e + 384 * b ^ 2 * c ^ 2 * e + 384 * b ^ 2 * c * d ^ 2 + (-512 : k) * b ^ 2 * f ^ 2 + (-512 : k) * b * c * e * f + (-512 : k) * b * d ^ 2 * f + 512 * c ^ 2 * d * f + 512 * c * d ^ 2 * e

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCDEFG_sylvester_mu
    (a b c d e f g : k) :
    ((-640 : k) * c) * kappaQuarticInnerABCDEFG810 a b c d e f g +
      (160 * b) * muQuarticInnerABCDEFG810 a b c d e f g =
      (800 : k) * quarticCoreMuABCDEFG810 a b c d e f := by
  simp only [kappaQuarticInnerABCDEFG810, muQuarticInnerABCDEFG810, quarticCoreMuABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCDEFG_sylvester_nu
    (a b c d e f g : k) :
    (160 * a * b + (-1280 : k) * d) * kappaQuarticInnerABCDEFG810 a b c d e f g +
      (160 * b) * nuQuarticInnerABCDEFG810 a b c d e f g =
      (6400 : k) * quarticCoreNuABCDEFG810 a b c d e f := by
  simp only [kappaQuarticInnerABCDEFG810, nuQuarticInnerABCDEFG810, quarticCoreNuABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCDEFG_sylvester_xi
    (a b c d e f g : k) :
    (160 * b ^ 2 + (-640 : k) * e) * kappaQuarticInnerABCDEFG810 a b c d e f g +
      (160 * b) * xiQuarticInnerABCDEFG810 a b c d e f g =
      (1600 : k) * quarticCoreXiABCDEFG810 a b c d e f := by
  simp only [kappaQuarticInnerABCDEFG810, xiQuarticInnerABCDEFG810, quarticCoreXiABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCDEFG_sylvester_omicron
    (a b c d e f g : k) :
    (160 * a ^ 2 * b + 2560 * a * d + 7680 * b * c + (-20480 : k) * f) * kappaQuarticInnerABCDEFG810 a b c d e f g +
      (160 * b) * omicronQuarticInnerABCDEFG810 a b c d e f g =
      (2560 : k) * quarticCoreOmicronABCDEFG810 a b c d e f := by
  simp only [kappaQuarticInnerABCDEFG810, omicronQuarticInnerABCDEFG810, quarticCoreOmicronABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCDEFG_sylvester_pi
    (a b c d e f g : k) :
    ((-25600 : k) * a * b ^ 3 + 102400 * b ^ 2 * d + (-102400 : k) * b * c ^ 2 + (-819200 : k) * b * g + 819200 * c * f + 819200 * d * e) * kappaQuarticInnerABCDEFG810 a b c d e f g +
      (25600 * b ^ 2) * piQuarticInnerABCDEFG810 a b c d e f g =
      (256000 : k) * quarticCorePiABCDEFG810 a b c d e f := by
  simp only [kappaQuarticInnerABCDEFG810, piQuarticInnerABCDEFG810, quarticCorePiABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCDEFG_sylvester_primitive
    (a b c d e f g : k) :
    (160 * a ^ 3 * b + 1280 * a ^ 2 * d + (-2560 : k) * a * b * c + 20480 * a * f + (-3840 : k) * b ^ 3 + 20480 * b * e + 20480 * c * d) * kappaQuarticInnerABCDEFG810 a b c d e f g +
      (160 * b) * primitiveQuarticInnerABCDEFG810 a b c d e f g =
      (6400 : k) * quarticCorePrimitiveABCDEFG810 a b c d e f := by
  simp only [kappaQuarticInnerABCDEFG810, primitiveQuarticInnerABCDEFG810, quarticCorePrimitiveABCDEFG810]
  ring


/-! ## Face / rest splits -/

set_option maxHeartbeats 64000000 in
def kappaQuarticFaceABCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoABCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (5 / 1024 * delta : k) • A ^ 3
  + (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABCDEFG810, degreeZeroKappaQuarticNoABCDEFG810]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoABCDEFG810` (29 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoABCDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * l : k), (45 / 8192 * l : k), (-(9 / 16384 * l) : k),
      (27 / 1024 * l : k), (-(9 / 512 * l) : k), (9 / 1024 * l : k),
      (-(63 / 1024 * l) : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 128 * l : k), (35 / 32768 * beta : k),
      (21 / 1024 * beta : k), (7 / 1024 * beta : k), (7 / 64 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k), (7 / 8 * beta : k),
      (-(3 / 16 * gamma) : k), (3 / 4 * gamma : k), (5 / 1024 * delta : k),
      (5 / 64 * delta : k), (-(15 / 128 * delta) : k), (5 / 8 * delta : k),
      (1 / 2 * epsilon : k), (3 / 128 * zeta : k), (3 / 8 * zeta : k),
      (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaQuarticNoABCDEFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  rw [speedRefl_degreeZeroKappaQuarticNoABCDEFG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  clear * - hApos hAB hAC hAD hAE hAF hAG
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticFaceABCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceABCDEFG810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 512 : k) * kappaQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  simp only [kappaQuarticFaceABCDEFG810, kappaQuarticInnerABCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B2D : ((B ^ 2 * D)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BG : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BG : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_CF : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_CF : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DE : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_DE : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_B2D, hcf_BC2, hcf_BG, hcf_CF, hcf_DE]
  ring

set_option maxHeartbeats 64000000 in
def muQuarticFaceABCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroMuQuarticNoABCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 262144 * l : k)) • (A ^ 4 * B)
  - (9 / 8192 * l : k) • (A ^ 3 * D)
  - (9 / 8192 * l : k) • (A ^ 2 * B * C)
  + (63 / 8192 * l : k) • (A * B ^ 3)
  - (9 / 1024 * l : k) • (A ^ 2 * F)
  - (9 / 512 * l : k) • (A * B * E)
  - (9 / 512 * l : k) • (A * C * D)
  - (63 / 1024 * l : k) • (B ^ 2 * D)
  - (63 / 1024 * l : k) • (B * C ^ 2)
  + (9 / 64 * l : k) • (B * G)
  + (9 / 64 * l : k) • (C * F)
  + (9 / 64 * l : k) • (D * E)
  - (7 / 8192 * beta : k) • (A ^ 3 * B)
  - (7 / 1024 * beta : k) • (A ^ 2 * D)
  + (7 / 512 * beta : k) • (A * B * C)
  + (21 / 1024 * beta : k) • B ^ 3
  - (7 / 64 * beta : k) • (A * F)
  - (7 / 64 * beta : k) • (B * E)
  - (7 / 64 * beta : k) • (C * D)
  + (3 / 128 * gamma : k) • (A * B ^ 2)
  - (3 / 16 * gamma : k) • (B * D)
  - (3 / 32 * gamma : k) • C ^ 2
  + (3 / 4 * gamma : k) • G
  - (5 / 1024 * delta : k) • (A ^ 2 * B)
  - (5 / 64 * delta : k) • (A * D)
  - (15 / 64 * delta : k) • (B * C)
  + (5 / 8 * delta : k) • F
  - (1 / 8 * epsilon : k) • B ^ 2
  + (1 / 2 * epsilon : k) • E
  - (3 / 64 * zeta : k) • (A * B)
  + (3 / 8 * zeta : k) • D
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroMuQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceABCDEFG810, degreeZeroMuQuarticNoABCDEFG810]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuQuarticNoABCDEFG810` (33 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoABCDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k),
      (63 / 8192 * l : k), (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (21 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k),
      (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuQuarticNoABCDEFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  rw [speedRefl_degreeZeroMuQuarticNoABCDEFG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  clear * - hApos hAB hAC hAD hAE hAF hAG
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem muQuarticFaceABCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceABCDEFG810 A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 2048 : k) * muQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  simp only [muQuarticFaceABCDEFG810, muQuarticInnerABCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABF : ((A * B * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABF : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BCD : ((B * C * D)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne hGne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_CG : ((C * G)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DF : ((D * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hDne hFne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_DF : ((D * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_ABF, hcf_AD2, hcf_B4, hcf_B2E, hcf_BCD, hcf_C3, hcf_CG, hcf_DF, hcf_E2]
  ring

set_option maxHeartbeats 64000000 in
def nuQuarticFaceABCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
def degreeZeroNuQuarticNoABCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 4096 * l : k) • (A ^ 3 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * F)
  - (9 / 512 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2
  + (7 / 65536 * beta : k) • A ^ 5
  + (7 / 4096 * beta : k) • (A ^ 3 * C)
  - (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * D)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2
  + (3 / 128 * gamma : k) • (A * B * C)
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 32 * gamma : k) • (A * F)
  - (3 / 16 * gamma : k) • (B * E)
  - (3 / 16 * gamma : k) • (C * D)
  + (15 / 32768 * delta : k) • A ^ 4
  + (5 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 512 * delta : k) • (A * B ^ 2)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G
  - (1 / 16 * epsilon : k) • (A * D)
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (1 / 512 * zeta : k) • A ^ 3
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  - (1 / 32 * eta : k) • (A * B)
  + (1 / 4 * eta : k) • D
  + (1 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroNuQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceABCDEFG810, degreeZeroNuQuarticNoABCDEFG810]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroNuQuarticNoABCDEFG810` (46 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroNuQuarticNoABCDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroNuQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (105 / 4194304 * l : k), (135 / 262144 * l : k), (9 / 4096 * l : k),
      (9 / 8192 * l : k), (9 / 16384 * l : k), (63 / 4096 * l : k),
      (315 / 32768 * l : k), (9 / 1024 * l : k), (-(9 / 256 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 512 * l) : k),
      (-(21 / 1024 * l) : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (7 / 65536 * beta : k), (7 / 4096 * beta : k),
      (-(7 / 16384 * beta) : k), (7 / 1024 * beta : k), (7 / 256 * beta : k),
      (63 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (3 / 128 * gamma : k), (5 / 128 * gamma : k),
      (-(3 / 32 * gamma) : k), (-(3 / 16 * gamma) : k), (-(3 / 16 * gamma) : k),
      (15 / 32768 * delta : k), (5 / 1024 * delta : k), (15 / 512 * delta : k),
      (-(15 / 64 * delta) : k), (-(15 / 128 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 16 * epsilon) : k), (-(1 / 4 * epsilon) : k), (1 / 2 * epsilon : k),
      (1 / 512 * zeta : k), (-(15 / 128 * zeta) : k), (3 / 8 * zeta : k),
      (-(1 / 32 * eta) : k), (1 / 4 * eta : k), (1 / 128 * theta : k),
      (1 / 8 * theta : k)]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0],
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [degreeZeroNuQuarticNoABCDEFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroNuQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  rw [speedRefl_degreeZeroNuQuarticNoABCDEFG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  clear * - hApos hAB hAC hAD hAE hAF hAG
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticFaceABCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceABCDEFG810 A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 4096 : k) * nuQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  simp only [nuQuarticFaceABCDEFG810, nuQuarticInnerABCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABG : ((A * B * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABG : ((A * B * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ACF : ((A * C * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ACF : ((A * C * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ACF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ADE : ((A * D * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ADE : ((A * D * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ADE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2F : ((B ^ 2 * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hFne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B2F : ((B ^ 2 * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BCE : ((B * C * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DG : ((D * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hGne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_DG : ((D * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_DG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_EF : ((E * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hEne hFne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_EF : ((E * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A2B3, hcf_AB2D, hcf_ABC2, hcf_ABG, hcf_ACF, hcf_ADE, hcf_B3C, hcf_B2F, hcf_BCE, hcf_BD2, hcf_C2D, hcf_DG, hcf_EF]
  ring

set_option maxHeartbeats 64000000 in
def xiQuarticFaceABCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroXiQuarticNoABCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 262144 * l : k)) • (A ^ 4 * D)
  + (9 / 16384 * l : k) • (A ^ 3 * B * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 3)
  - (9 / 8192 * l : k) • (A ^ 3 * F)
  + (9 / 4096 * l : k) • (A ^ 2 * B * E)
  - (9 / 8192 * l : k) • (A ^ 2 * C * D)
  + (171 / 8192 * l : k) • (A * B ^ 2 * D)
  + (9 / 1024 * l : k) • (A * B * C ^ 2)
  + (63 / 2048 * l : k) • (B ^ 3 * C)
  - (9 / 512 * l : k) • (A * C * F)
  - (9 / 512 * l : k) • (A * D * E)
  - (45 / 1024 * l : k) • (B ^ 2 * F)
  - (27 / 256 * l : k) • (B * C * E)
  - (27 / 512 * l : k) • (B * D ^ 2)
  - (63 / 1024 * l : k) • (C ^ 2 * D)
  + (9 / 64 * l : k) • (D * G)
  + (9 / 64 * l : k) • (E * F)
  - (7 / 8192 * beta : k) • (A ^ 3 * D)
  + (7 / 2048 * beta : k) • (A ^ 2 * B * C)
  - (7 / 1024 * beta : k) • (A * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 2 * F)
  + (7 / 256 * beta : k) • (A * B * E)
  + (7 / 512 * beta : k) • (A * C * D)
  + (49 / 1024 * beta : k) • (B ^ 2 * D)
  + (7 / 128 * beta : k) • (B * C ^ 2)
  - (7 / 64 * beta : k) • (C * F)
  - (7 / 64 * beta : k) • (D * E)
  + (3 / 64 * gamma : k) • (A * B * D)
  + (3 / 32 * gamma : k) • (B ^ 2 * C)
  - (3 / 32 * gamma : k) • (B * F)
  - (3 / 16 * gamma : k) • (C * E)
  - (3 / 32 * gamma : k) • D ^ 2
  - (5 / 1024 * delta : k) • (A ^ 2 * D)
  + (5 / 128 * delta : k) • (A * B * C)
  + (5 / 128 * delta : k) • B ^ 3
  - (5 / 64 * delta : k) • (A * F)
  - (5 / 32 * delta : k) • (B * E)
  - (15 / 64 * delta : k) • (C * D)
  + (1 / 32 * epsilon : k) • (A * B ^ 2)
  - (3 / 16 * epsilon : k) • (B * D)
  - (1 / 8 * epsilon : k) • C ^ 2
  + (1 / 2 * epsilon : k) • G
  - (3 / 64 * zeta : k) • (A * D)
  - (3 / 16 * zeta : k) • (B * C)
  + (3 / 8 * zeta : k) • F
  - (1 / 16 * eta : k) • B ^ 2
  + (1 / 4 * eta : k) • E
  + (1 / 8 * theta : k) • D

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroXiQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceABCDEFG810, degreeZeroXiQuarticNoABCDEFG810]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiQuarticNoABCDEFG810` (48 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiQuarticNoABCDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroXiQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 262144 * l) : k), (9 / 16384 * l : k), (-(9 / 16384 * l) : k),
      (-(9 / 8192 * l) : k), (9 / 4096 * l : k), (-(9 / 8192 * l) : k),
      (171 / 8192 * l : k), (9 / 1024 * l : k), (63 / 2048 * l : k),
      (-(9 / 512 * l) : k), (-(9 / 512 * l) : k), (-(45 / 1024 * l) : k),
      (-(27 / 256 * l) : k), (-(27 / 512 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (-(7 / 8192 * beta) : k),
      (7 / 2048 * beta : k), (-(7 / 1024 * beta) : k), (-(7 / 1024 * beta) : k),
      (7 / 256 * beta : k), (7 / 512 * beta : k), (49 / 1024 * beta : k),
      (7 / 128 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (3 / 64 * gamma : k), (3 / 32 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k), (-(5 / 1024 * delta) : k),
      (5 / 128 * delta : k), (5 / 128 * delta : k), (-(5 / 64 * delta) : k),
      (-(5 / 32 * delta) : k), (-(15 / 64 * delta) : k), (1 / 32 * epsilon : k),
      (-(3 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k),
      (-(3 / 64 * zeta) : k), (-(3 / 16 * zeta) : k), (3 / 8 * zeta : k),
      (-(1 / 16 * eta) : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [4, 0, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0],
      [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0],
      [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1],
      [0, 0, 0, 0, 1, 1, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroXiQuarticNoABCDEFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  rw [speedRefl_degreeZeroXiQuarticNoABCDEFG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  clear * - hApos hAB hAC hAD hAE hAF hAG
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticFaceABCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceABCDEFG810 A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 2048 : k) * xiQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  simp only [xiQuarticFaceABCDEFG810, xiQuarticInnerABCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB4 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne), natDegree_pow]
  have hcf_AB4 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hdeg_AB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCD : ((A * B * C * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABCD : ((A * B * C * D)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_ABCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ADF : ((A * D * F)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ADF : ((A * D * F)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ADF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B3D : ((B ^ 3 * D)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B2G : ((B ^ 2 * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B2G : ((B ^ 2 * G)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_B2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCF : ((B * C * F)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hFne, natDegree_mul hBne hCne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BCF : ((B * C * F)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BDE : ((B * D * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BDE : ((B * D * E)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EG : ((E * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hEne hGne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_EG : ((E * G)).coeff (A.natDegree + 4 * B.natDegree) =
      E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_EG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_F2 : (F ^ 2).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_F2 : (F ^ 2).coeff (A.natDegree + 4 * B.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB4, hcf_AB2E, hcf_ABCD, hcf_ADF, hcf_B3D, hcf_B2C2, hcf_B2G, hcf_BCF, hcf_BDE, hcf_C2E, hcf_CD2, hcf_EG, hcf_F2]
  ring

set_option maxHeartbeats 64000000 in
def omicronQuarticFaceABCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronQuarticNoABCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (135 / 33554432 * l : k) • A ^ 7
  + (225 / 2097152 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (81 / 262144 * l : k) • (A ^ 4 * E)
  - (9 / 65536 * l : k) • (A ^ 3 * B * D)
  + (99 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  - (45 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (189 / 65536 * l : k) • (A * B ^ 4)
  + (9 / 8192 * l : k) • (A ^ 3 * G)
  - (9 / 4096 * l : k) • (A ^ 2 * B * F)
  + (27 / 8192 * l : k) • (A ^ 2 * C * E)
  + (45 / 4096 * l : k) • (A * B ^ 2 * E)
  + (99 / 4096 * l : k) • (A * B * C * D)
  + (9 / 8192 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 512 * l : k) • (A * C * G)
  - (9 / 256 * l : k) • (A * D * F)
  - (27 / 1024 * l : k) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)
  - (45 / 512 * l : k) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)
  - (27 / 512 * l : k) • (C * D ^ 2)
  + (9 / 64 * l : k) • (E * G)
  + (9 / 128 * l : k) • F ^ 2
  + (35 / 2097152 * beta : k) • A ^ 6
  + (49 / 131072 * beta : k) • (A ^ 4 * C)
  - (35 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 4096 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  - (91 / 8192 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (7 / 512 * beta : k) • (A * C * E)
  + (7 / 512 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2
  + (3 / 2048 * gamma : k) • (A ^ 2 * B * C)
  - (9 / 1024 * gamma : k) • (A * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 2 * F)
  + (3 / 128 * gamma : k) • (A * B * E)
  + (3 / 128 * gamma : k) • (A * C * D)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)
  + (9 / 131072 * delta : k) • A ^ 5
  + (5 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 4096 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 128 * delta : k) • (A * B * D)
  + (5 / 512 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2
  - (1 / 256 * epsilon : k) • (A ^ 2 * D)
  + (1 / 32 * epsilon : k) • (A * B * C)
  + (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 16 * epsilon : k) • (A * F)
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (9 / 32768 * zeta : k) • A ^ 4
  + (3 / 1024 * zeta : k) • (A ^ 2 * C)
  + (9 / 512 * zeta : k) • (A * B ^ 2)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (1 / 512 * eta : k) • (A ^ 2 * B)
  - (1 / 32 * eta : k) • (A * D)
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (1 / 1024 * theta : k) • A ^ 3
  + (1 / 64 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroOmicronQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceABCDEFG810, degreeZeroOmicronQuarticNoABCDEFG810]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroOmicronQuarticNoABCDEFG810` (78 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronQuarticNoABCDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroOmicronQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (135 / 33554432 * l : k), (225 / 2097152 * l : k), (-(171 / 4194304 * l) : k),
      (81 / 262144 * l : k), (-(9 / 65536 * l) : k), (99 / 131072 * l : k),
      (-(45 / 131072 * l) : k), (-(189 / 65536 * l) : k), (9 / 8192 * l : k),
      (-(9 / 4096 * l) : k), (27 / 8192 * l : k), (45 / 4096 * l : k),
      (99 / 4096 * l : k), (9 / 8192 * l : k), (189 / 8192 * l : k),
      (567 / 16384 * l : k), (9 / 512 * l : k), (-(9 / 256 * l) : k),
      (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k), (-(45 / 512 * l) : k),
      (-(45 / 1024 * l) : k), (-(27 / 512 * l) : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 2097152 * beta : k), (49 / 131072 * beta : k),
      (-(35 / 131072 * beta) : k), (7 / 8192 * beta : k), (-(7 / 4096 * beta) : k),
      (21 / 8192 * beta : k), (-(91 / 8192 * beta) : k), (-(189 / 32768 * beta) : k),
      (7 / 512 * beta : k), (7 / 512 * beta : k), (35 / 1024 * beta : k),
      (21 / 256 * beta : k), (7 / 512 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (3 / 2048 * gamma : k), (-(9 / 1024 * gamma) : k),
      (-(3 / 512 * gamma) : k), (3 / 128 * gamma : k), (3 / 128 * gamma : k),
      (9 / 128 * gamma : k), (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (9 / 131072 * delta : k), (5 / 4096 * delta : k),
      (-(5 / 4096 * delta) : k), (5 / 128 * delta : k), (5 / 512 * delta : k),
      (45 / 512 * delta : k), (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k),
      (-(15 / 128 * delta) : k), (-(1 / 256 * epsilon) : k), (1 / 32 * epsilon : k),
      (1 / 32 * epsilon : k), (-(1 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k),
      (-(3 / 16 * epsilon) : k), (9 / 32768 * zeta : k), (3 / 1024 * zeta : k),
      (9 / 512 * zeta : k), (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k),
      (3 / 8 * zeta : k), (-(1 / 512 * eta) : k), (-(1 / 32 * eta) : k),
      (-(3 / 32 * eta) : k), (1 / 4 * eta : k), (1 / 1024 * theta : k),
      (1 / 64 * theta : k), (-(3 / 128 * theta) : k), (1 / 8 * theta : k)]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0], [2, 0, 1, 0, 1, 0, 0], [1, 2, 0, 0, 1, 0, 0],
      [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1],
      [0, 0, 0, 0, 0, 2, 0], [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0],
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0],
      [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0],
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [degreeZeroOmicronQuarticNoABCDEFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  rw [speedRefl_degreeZeroOmicronQuarticNoABCDEFG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  clear * - hApos hAB hAC hAD hAE hAF hAG
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticFaceABCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceABCDEFG810 A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * omicronQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  simp only [omicronQuarticFaceABCDEFG810, omicronQuarticInnerABCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BC2 : ((A ^ 2 * B * C ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2BC2 : ((A ^ 2 * B * C ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BG : ((A ^ 2 * B * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2BG : ((A ^ 2 * B * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2CF : ((A ^ 2 * C * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hCne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2CF : ((A ^ 2 * C * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A2CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2DE : ((A ^ 2 * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2DE : ((A ^ 2 * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3C : ((A * B ^ 3 * C)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AB3C : ((A * B ^ 3 * C)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_AB3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2F : ((A * B ^ 2 * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hFne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AB2F : ((A * B ^ 2 * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_AB2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCE : ((A * B * C * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABCE : ((A * B * C * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ABCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABD2 : ((A * B * D ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hDne), natDegree_mul hAne hBne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABD2 : ((A * B * D ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ABD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AC2D : ((A * C ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AC2D : ((A * C ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ADG : ((A * D * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ADG : ((A * D * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ADG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AEF : ((A * E * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hEne) hFne, natDegree_mul hAne hEne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AEF : ((A * E * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_AEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CD : ((B ^ 2 * C * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hDne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B2CD : ((B ^ 2 * C * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_B2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCG : ((B * C * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hGne, natDegree_mul hBne hCne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BCG : ((B * C * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BCG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BDF : ((B * D * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hFne, natDegree_mul hBne hDne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BDF : ((B * D * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BE2 : ((B * E ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hEne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BE2 : ((B * E ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_BE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_C2F : ((C ^ 2 * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDE : ((C * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hEne, natDegree_mul hCne hDne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_CDE : ((C * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_CDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_FG : ((F * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hFne hGne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_FG : ((F * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_FG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A3B3, hcf_A2B2D, hcf_A2BC2, hcf_A2BG, hcf_A2CF, hcf_A2DE, hcf_AB3C, hcf_AB2F, hcf_ABCE, hcf_ABD2, hcf_AC2D, hcf_ADG, hcf_AEF, hcf_B5, hcf_B3E, hcf_B2CD, hcf_BC3, hcf_BCG, hcf_BDF, hcf_BE2, hcf_C2F, hcf_CDE, hcf_D3, hcf_FG]
  ring


end QuarticFullConeABCDEFG810

end Max11DegreeRoutes
