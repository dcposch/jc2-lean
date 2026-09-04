import Grok810ScaleZeroQuarticFullConeKillScratch

/-! # Resultant ladder killing the 7-letter cone `R = {A,B,C,D,E,F,G}`

Continuation of `Grok810ScaleZeroQuarticFullConeKillScratch`.  That file
exports `quarticConeABCDEFG810_residual2`: on this cone the seven inners
vanish, the six G-free cores vanish, and `T = 0`.

This file records the resultant ladder of the CAS certificate
`fullcone810/certificate.txt`:

* the seven inners are weighted-homogeneous of weights `(2,3,4,5,6,7,8)`
  and degrees `11..17` (one-line `ring` lemmas);
* four compact relations `U22, U24, U25a, U25b` in the six cores, with
  cofactors of 11/7/15/14 monomials;
* `b`-strips `U22 = b·P19`, `U24 = b·P21`, `U25a = b·P22`;
* the e-linear combination `V` of `U24, U25b` and the e-free `D1` of
  `P19, P22`;
* the pairwise e-resultants of `{U22, T, U25a, V, U24, U25b}`.

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

section QuarticFullConeABCDEFG810Ladder

variable {k : Type*} [Field k] [CharZero k]


/-! ## Weighted homogeneity of the seven inners -/

set_option maxHeartbeats 16000000 in
theorem kappaQuarticInnerABCDEFG810_weightedHomogeneous
    (t a b c d e f g : k) :
    kappaQuarticInnerABCDEFG810 (t ^ 2 * a) (t ^ 3 * b) (t ^ 4 * c) (t ^ 5 * d)
        (t ^ 6 * e) (t ^ 7 * f) (t ^ 8 * g) =
      t ^ 11 * kappaQuarticInnerABCDEFG810 a b c d e f g := by
  simp only [kappaQuarticInnerABCDEFG810]
  ring

set_option maxHeartbeats 16000000 in
theorem muQuarticInnerABCDEFG810_weightedHomogeneous
    (t a b c d e f g : k) :
    muQuarticInnerABCDEFG810 (t ^ 2 * a) (t ^ 3 * b) (t ^ 4 * c) (t ^ 5 * d)
        (t ^ 6 * e) (t ^ 7 * f) (t ^ 8 * g) =
      t ^ 12 * muQuarticInnerABCDEFG810 a b c d e f g := by
  simp only [muQuarticInnerABCDEFG810]
  ring

set_option maxHeartbeats 16000000 in
theorem nuQuarticInnerABCDEFG810_weightedHomogeneous
    (t a b c d e f g : k) :
    nuQuarticInnerABCDEFG810 (t ^ 2 * a) (t ^ 3 * b) (t ^ 4 * c) (t ^ 5 * d)
        (t ^ 6 * e) (t ^ 7 * f) (t ^ 8 * g) =
      t ^ 13 * nuQuarticInnerABCDEFG810 a b c d e f g := by
  simp only [nuQuarticInnerABCDEFG810]
  ring

set_option maxHeartbeats 16000000 in
theorem xiQuarticInnerABCDEFG810_weightedHomogeneous
    (t a b c d e f g : k) :
    xiQuarticInnerABCDEFG810 (t ^ 2 * a) (t ^ 3 * b) (t ^ 4 * c) (t ^ 5 * d)
        (t ^ 6 * e) (t ^ 7 * f) (t ^ 8 * g) =
      t ^ 14 * xiQuarticInnerABCDEFG810 a b c d e f g := by
  simp only [xiQuarticInnerABCDEFG810]
  ring

set_option maxHeartbeats 32000000 in
theorem omicronQuarticInnerABCDEFG810_weightedHomogeneous
    (t a b c d e f g : k) :
    omicronQuarticInnerABCDEFG810 (t ^ 2 * a) (t ^ 3 * b) (t ^ 4 * c) (t ^ 5 * d)
        (t ^ 6 * e) (t ^ 7 * f) (t ^ 8 * g) =
      t ^ 15 * omicronQuarticInnerABCDEFG810 a b c d e f g := by
  simp only [omicronQuarticInnerABCDEFG810]
  ring

set_option maxHeartbeats 32000000 in
theorem piQuarticInnerABCDEFG810_weightedHomogeneous
    (t a b c d e f g : k) :
    piQuarticInnerABCDEFG810 (t ^ 2 * a) (t ^ 3 * b) (t ^ 4 * c) (t ^ 5 * d)
        (t ^ 6 * e) (t ^ 7 * f) (t ^ 8 * g) =
      t ^ 16 * piQuarticInnerABCDEFG810 a b c d e f g := by
  simp only [piQuarticInnerABCDEFG810]
  ring

set_option maxHeartbeats 32000000 in
theorem primitiveQuarticInnerABCDEFG810_weightedHomogeneous
    (t a b c d e f g : k) :
    primitiveQuarticInnerABCDEFG810 (t ^ 2 * a) (t ^ 3 * b) (t ^ 4 * c) (t ^ 5 * d)
        (t ^ 6 * e) (t ^ 7 * f) (t ^ 8 * g) =
      t ^ 17 * primitiveQuarticInnerABCDEFG810 a b c d e f g := by
  simp only [primitiveQuarticInnerABCDEFG810]
  ring

/-! ## Compact relations `U22, U24, U25a, U25b` and `b`-strips -/

def quarticCoreU22ABCDEFG810 (b c d e f : k) : k :=
  7 * b ^ 6 * c + (-20 : k) * b ^ 5 * f + (-40 : k) * b ^ 4 * c * e + (-100 : k) * b ^ 4 * d ^ 2
  + (-240 : k) * b ^ 3 * c ^ 2 * d + 160 * b ^ 3 * e * f + 800 * b ^ 2 * c * d * f
  + 320 * b ^ 2 * d ^ 2 * e + 160 * b * c * d ^ 3 + (-640 : k) * b * d * f ^ 2

def quarticCoreU24ABCDEFG810 (b c d e f : k) : k :=
  21 * b ^ 8 + (-160 : k) * b ^ 6 * e + 720 * b ^ 5 * c * d + 800 * b ^ 4 * c ^ 3
  + (-320 : k) * b ^ 4 * d * f + 320 * b ^ 4 * e ^ 2 + (-3840 : k) * b ^ 3 * c ^ 2 * f
  + (-3840 : k) * b ^ 3 * c * d * e + 160 * b ^ 3 * d ^ 3 + (-4800 : k) * b ^ 2 * c ^ 2 * d ^ 2
  + 7680 * b ^ 2 * c * f ^ 2 + 2560 * b ^ 2 * d * e * f + 5120 * b * c * d ^ 2 * f
  + (-1280 : k) * b * d ^ 3 * e

def quarticCoreU25aABCDEFG810 (b c d e f : k) : k :=
  2 * b ^ 6 * f + 4 * b ^ 5 * c * e + 45 * b ^ 5 * d ^ 2 + 80 * b ^ 4 * c ^ 2 * d
  + (-32 : k) * b ^ 4 * e * f + (-288 : k) * b ^ 3 * c * d * f + (-168 : k) * b ^ 3 * d ^ 2 * e
  + (-160 : k) * b ^ 2 * c * d ^ 3 + 320 * b ^ 2 * d * f ^ 2 + 160 * b * d ^ 3 * f

def quarticCoreU25bABCDEFG810 (b c d e f : k) : k :=
  (-3 : k) * b ^ 6 * f + 70 * b ^ 5 * c * e + (-575 : k) * b ^ 5 * d ^ 2
  + (-910 : k) * b ^ 4 * c ^ 2 * d + 120 * b ^ 4 * e * f + 40 * b ^ 3 * c ^ 4
  + 3360 * b ^ 3 * c * d * f + (-560 : k) * b ^ 3 * c * e ^ 2 + 1840 * b ^ 3 * d ^ 2 * e
  + 160 * b ^ 2 * c ^ 3 * f + (-1520 : k) * b ^ 2 * c ^ 2 * d * e + 1000 * b ^ 2 * c * d ^ 3
  + (-3360 : k) * b ^ 2 * d * f ^ 2 + 1280 * b ^ 2 * e ^ 2 * f + (-1920 : k) * b * c ^ 2 * f ^ 2
  + 1600 * b * c * d * e * f + 320 * b * d ^ 3 * f + (-1600 : k) * c ^ 2 * d ^ 2 * f
  + (-1600 : k) * c * d ^ 3 * e + 2560 * c * f ^ 3 + 2560 * d * e * f ^ 2

def quarticCoreP19ABCDEFG810 (b c d e f : k) : k :=
  7 * b ^ 5 * c + (-20 : k) * b ^ 4 * f + (-40 : k) * b ^ 3 * c * e + (-100 : k) * b ^ 3 * d ^ 2
  + (-240 : k) * b ^ 2 * c ^ 2 * d + 160 * b ^ 2 * e * f + 800 * b * c * d * f
  + 320 * b * d ^ 2 * e + 160 * c * d ^ 3 + (-640 : k) * d * f ^ 2

def quarticCoreP21ABCDEFG810 (b c d e f : k) : k :=
  21 * b ^ 7 + (-160 : k) * b ^ 5 * e + 720 * b ^ 4 * c * d + 800 * b ^ 3 * c ^ 3
  + (-320 : k) * b ^ 3 * d * f + 320 * b ^ 3 * e ^ 2 + (-3840 : k) * b ^ 2 * c ^ 2 * f
  + (-3840 : k) * b ^ 2 * c * d * e + 160 * b ^ 2 * d ^ 3 + (-4800 : k) * b * c ^ 2 * d ^ 2
  + 7680 * b * c * f ^ 2 + 2560 * b * d * e * f + 5120 * c * d ^ 2 * f + (-1280 : k) * d ^ 3 * e

def quarticCoreP22ABCDEFG810 (b c d e f : k) : k :=
  2 * b ^ 5 * f + 4 * b ^ 4 * c * e + 45 * b ^ 4 * d ^ 2 + 80 * b ^ 3 * c ^ 2 * d
  + (-32 : k) * b ^ 3 * e * f + (-288 : k) * b ^ 2 * c * d * f + (-168 : k) * b ^ 2 * d ^ 2 * e
  + (-160 : k) * b * c * d ^ 3 + 320 * b * d * f ^ 2 + 160 * d ^ 3 * f

def quarticCoreV_ABCDEFG810 (b c d e f : k) : k :=
  147 * b ^ 8 * c + (-348 : k) * b ^ 7 * f + (-840 : k) * b ^ 6 * c * e
  + (-2300 : k) * b ^ 6 * d ^ 2 + 1400 * b ^ 5 * c ^ 2 * d + 3040 * b ^ 5 * e * f
  + 5760 * b ^ 4 * c ^ 4 + (-320 : k) * b ^ 4 * c * d * f + 7360 * b ^ 4 * d ^ 2 * e
  + (-39040 : k) * b ^ 3 * c ^ 3 * f + (-32960 : k) * b ^ 3 * c ^ 2 * d * e
  + 5120 * b ^ 3 * c * d ^ 3 + (-8320 : k) * b ^ 3 * d * f ^ 2
  + (-33600 : k) * b ^ 2 * c ^ 3 * d ^ 2 + 107520 * b ^ 2 * c ^ 2 * f ^ 2
  + 85760 * b ^ 2 * c * d * e * f + (-1280 : k) * b ^ 2 * d ^ 3 * f
  + 106240 * b * c ^ 2 * d ^ 2 * f + (-15360 : k) * b * c * d ^ 3 * e
  + (-112640 : k) * b * c * f ^ 3 + (-30720 : k) * b * d * e * f ^ 2
  + (-81920 : k) * c * d ^ 2 * f ^ 2 + 20480 * d ^ 3 * e * f

def quarticCoreAlphaABCDEFG810 (b c d f : k) : k :=
  -b ^ 2 * c + 4 * b * f + 8 * d ^ 2

def quarticCoreBetaABCDEFG810 (b c d f : k) : k :=
  b ^ 2 * c + (-8 : k) * b * f + (-42 : k) * d ^ 2

def quarticCoreD1ABCDEFG810 (b c d f : k) : k :=
  (-7 : k) * b ^ 8 * c ^ 2 + 56 * b ^ 7 * c * f + (-56 : k) * b ^ 6 * c * d ^ 2
  + (-80 : k) * b ^ 6 * f ^ 2 + (-560 : k) * b ^ 5 * c ^ 3 * d + 320 * b ^ 5 * d ^ 2 * f
  + 3360 * b ^ 4 * c ^ 2 * d * f + (-600 : k) * b ^ 4 * d ^ 4
  + (-2240 : k) * b ^ 3 * c ^ 2 * d ^ 3 + (-7680 : k) * b ^ 3 * c * d * f ^ 2
  + 3840 * b ^ 2 * c * d ^ 3 * f + 7680 * b ^ 2 * d * f ^ 3 + (-6080 : k) * b * c * d ^ 5
  + 5120 * b * d ^ 3 * f ^ 2 + 12800 * d ^ 5 * f

set_option maxHeartbeats 32000000 in
theorem quarticCoreU22_from_cores
    (a b c d e f : k) :
    (76 : k) * quarticCoreU22ABCDEFG810 b c d e f =
      (60 * b * c + (-240 : k) * f) * quarticCoreMuABCDEFG810 a b c d e f +
      (75 * a ^ 3 + 440 * a * c + (-280 : k) * b ^ 2 + 480 * e) * quarticCoreNuABCDEFG810 a b c d e f +
      ((-560 : k) * d) * quarticCoreXiABCDEFG810 a b c d e f +
      (10 * a ^ 2 + 8 * c) * quarticCoreOmicronABCDEFG810 a b c d e f +
      ((-40 : k)) * quarticCorePiABCDEFG810 a b c d e f +
      (25 * a) * quarticCorePrimitiveABCDEFG810 a b c d e f := by
  simp only [quarticCoreU22ABCDEFG810, quarticCoreMuABCDEFG810, quarticCoreNuABCDEFG810, quarticCoreXiABCDEFG810, quarticCoreOmicronABCDEFG810, quarticCorePiABCDEFG810, quarticCorePrimitiveABCDEFG810]
  ring

set_option maxHeartbeats 32000000 in
theorem quarticCoreU24_from_cores
    (a b c d e f : k) :
    (2 : k) * quarticCoreU24ABCDEFG810 b c d e f =
      ((-75 : k) * a ^ 2 * c + (-10 : k) * a * b ^ 2 + 80 * b * d + (-400 : k) * c ^ 2) * quarticCoreNuABCDEFG810 a b c d e f +
      ((-10 : k) * a * c + (-2 : k) * b ^ 2) * quarticCoreOmicronABCDEFG810 a b c d e f +
      ((-25 : k) * c) * quarticCorePrimitiveABCDEFG810 a b c d e f := by
  simp only [quarticCoreU24ABCDEFG810, quarticCoreNuABCDEFG810, quarticCoreOmicronABCDEFG810, quarticCorePrimitiveABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreU25a_from_cores
    (a b c d e f : k) :
    (304 : k) * quarticCoreU25aABCDEFG810 b c d e f =
      ((-60 : k) * b ^ 2 * c + 240 * b * f) * quarticCoreMuABCDEFG810 a b c d e f +
      ((-75 : k) * a ^ 3 * b + (-285 : k) * a ^ 2 * d + (-440 : k) * a * b * c + 356 * b ^ 3 + (-480 : k) * b * e + (-1520 : k) * c * d) * quarticCoreNuABCDEFG810 a b c d e f +
      (560 * b * d) * quarticCoreXiABCDEFG810 a b c d e f +
      ((-10 : k) * a ^ 2 * b + (-38 : k) * a * d + (-8 : k) * b * c) * quarticCoreOmicronABCDEFG810 a b c d e f +
      (40 * b) * quarticCorePiABCDEFG810 a b c d e f +
      ((-25 : k) * a * b + (-95 : k) * d) * quarticCorePrimitiveABCDEFG810 a b c d e f := by
  simp only [quarticCoreU25aABCDEFG810, quarticCoreMuABCDEFG810, quarticCoreNuABCDEFG810, quarticCoreXiABCDEFG810, quarticCoreOmicronABCDEFG810, quarticCorePiABCDEFG810, quarticCorePrimitiveABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreU25b_from_cores
    (a b c d e f : k) :
    (304 : k) * quarticCoreU25bABCDEFG810 b c d e f =
      (1640 * b ^ 2 * c + (-5040 : k) * b * f) * quarticCoreMuABCDEFG810 a b c d e f +
      (1575 * a ^ 3 * b + 10000 * a * b * c + (-3040 : k) * a * f + (-7400 : k) * b ^ 3 + 16160 * b * e + 15200 * c * d) * quarticCoreNuABCDEFG810 a b c d e f +
      ((-14800 : k) * b * d) * quarticCoreXiABCDEFG810 a b c d e f +
      (210 * a ^ 2 * b + 320 * b * c + (-608 : k) * f) * quarticCoreOmicronABCDEFG810 a b c d e f +
      ((-840 : k) * b) * quarticCorePiABCDEFG810 a b c d e f +
      (525 * a * b) * quarticCorePrimitiveABCDEFG810 a b c d e f := by
  simp only [quarticCoreU25bABCDEFG810, quarticCoreMuABCDEFG810, quarticCoreNuABCDEFG810, quarticCoreXiABCDEFG810, quarticCoreOmicronABCDEFG810, quarticCorePiABCDEFG810, quarticCorePrimitiveABCDEFG810]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCoreU22_eq_b_P19
    (b c d e f : k) :
    quarticCoreU22ABCDEFG810 b c d e f =
      b * quarticCoreP19ABCDEFG810 b c d e f := by
  simp only [quarticCoreU22ABCDEFG810, quarticCoreP19ABCDEFG810]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCoreU24_eq_b_P21
    (b c d e f : k) :
    quarticCoreU24ABCDEFG810 b c d e f =
      b * quarticCoreP21ABCDEFG810 b c d e f := by
  simp only [quarticCoreU24ABCDEFG810, quarticCoreP21ABCDEFG810]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCoreU25a_eq_b_P22
    (b c d e f : k) :
    quarticCoreU25aABCDEFG810 b c d e f =
      b * quarticCoreP22ABCDEFG810 b c d e f := by
  simp only [quarticCoreU25aABCDEFG810, quarticCoreP22ABCDEFG810]
  ring

/-! ## `V` (e-linear) and `D1` (e-free) -/

set_option maxHeartbeats 32000000 in
theorem quarticCoreV_from_U24_U25b
    (b c d e f : k) :
    b * quarticCoreV_ABCDEFG810 b c d e f =
      (7 * b * c + (-16 : k) * f) * quarticCoreU24ABCDEFG810 b c d e f +
        (4 * b ^ 2) * quarticCoreU25bABCDEFG810 b c d e f := by
  simp only [quarticCoreV_ABCDEFG810, quarticCoreU24ABCDEFG810,
    quarticCoreU25bABCDEFG810]
  ring

set_option maxHeartbeats 32000000 in
theorem quarticCoreD1_from_P19_P22
    (b c d e f : k) :
    quarticCoreD1ABCDEFG810 b c d f =
      (10 * quarticCoreAlphaABCDEFG810 b c d f) *
          quarticCoreP22ABCDEFG810 b c d e f -
        (b * quarticCoreBetaABCDEFG810 b c d f) *
          quarticCoreP19ABCDEFG810 b c d e f := by
  simp only [quarticCoreD1ABCDEFG810, quarticCoreAlphaABCDEFG810,
    quarticCoreBetaABCDEFG810, quarticCoreP22ABCDEFG810,
    quarticCoreP19ABCDEFG810]
  ring

/-! ## Pairwise e-resultants -/

def quarticCoreResE_U22_U25aABCDEFG810 (b c d f : k) : k :=
  7 * b ^ 8 * c ^ 2 + (-56 : k) * b ^ 7 * c * f + 56 * b ^ 6 * c * d ^ 2 + 80 * b ^ 6 * f ^ 2
  + 560 * b ^ 5 * c ^ 3 * d + (-320 : k) * b ^ 5 * d ^ 2 * f
  + (-3360 : k) * b ^ 4 * c ^ 2 * d * f + 600 * b ^ 4 * d ^ 4 + 2240 * b ^ 3 * c ^ 2 * d ^ 3
  + 7680 * b ^ 3 * c * d * f ^ 2 + (-3840 : k) * b ^ 2 * c * d ^ 3 * f
  + (-7680 : k) * b ^ 2 * d * f ^ 3 + 6080 * b * c * d ^ 5 + (-5120 : k) * b * d ^ 3 * f ^ 2
  + (-12800 : k) * d ^ 5 * f

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_U22_U25a
    (b c d e f : k) :
    (
      (-4 : k) * b ^ 5 * c + 32 * b ^ 4 * f + 168 * b ^ 3 * d ^ 2
      ) *
        quarticCoreU22ABCDEFG810 b c d e f +
    (
      (-40 : k) * b ^ 4 * c + 160 * b ^ 3 * f + 320 * b ^ 2 * d ^ 2
      ) *
        quarticCoreU25aABCDEFG810 b c d e f =
      (-4 : k) * b ^ 3 * quarticCoreResE_U22_U25aABCDEFG810 b c d f := by
  simp only [quarticCoreU22ABCDEFG810, quarticCoreU25aABCDEFG810, quarticCoreResE_U22_U25aABCDEFG810]
  ring

def quarticCoreResE_U22_TABCDEFG810 (b c d f : k) : k :=
  7 * b ^ 8 * c ^ 3 + 4 * b ^ 8 * d * f + (-112 : k) * b ^ 7 * c ^ 2 * f
  + (-22 : k) * b ^ 7 * d ^ 3 + (-112 : k) * b ^ 6 * c ^ 2 * d ^ 2 + 528 * b ^ 6 * c * f ^ 2
  + 320 * b ^ 5 * c ^ 4 * d + 448 * b ^ 5 * c * d ^ 2 * f + (-640 : k) * b ^ 5 * f ^ 3
  + (-4480 : k) * b ^ 4 * c ^ 3 * d * f + (-40 : k) * b ^ 4 * c * d ^ 4
  + (-640 : k) * b ^ 4 * d ^ 2 * f ^ 2 + (-880 : k) * b ^ 3 * c ^ 3 * d ^ 3
  + 17280 * b ^ 3 * c ^ 2 * d * f ^ 2 + (-1600 : k) * b ^ 3 * d ^ 4 * f
  + 320 * b ^ 2 * c ^ 2 * d ^ 3 * f + (-25600 : k) * b ^ 2 * c * d * f ^ 3
  + (-320 : k) * b ^ 2 * d ^ 6 + 640 * b * c ^ 2 * d ^ 5 + 6400 * b * c * d ^ 3 * f ^ 2
  + 10240 * b * d * f ^ 4 + 3840 * c * d ^ 5 * f + (-15360 : k) * d ^ 3 * f ^ 3

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_U22_T
    (b c d e f : k) :
    (
      40 * b ^ 4 * d + (-120 : k) * b ^ 3 * c ^ 2 + 1120 * b ^ 2 * c * f + 320 * b * c * d ^ 2
      + (-1280 : k) * b * f ^ 2 + 1920 * d ^ 2 * f
      ) *
        quarticCoreU22ABCDEFG810 b c d e f +
    (
      (-40 : k) * b ^ 4 * c + 160 * b ^ 3 * f + 320 * b ^ 2 * d ^ 2
      ) *
        quarticCoreT_ABCDEFG810 b c d e f =
      (80 : k) * b * quarticCoreResE_U22_TABCDEFG810 b c d f := by
  simp only [quarticCoreU22ABCDEFG810, quarticCoreT_ABCDEFG810, quarticCoreResE_U22_TABCDEFG810]
  ring

def quarticCoreResE_T_U25aABCDEFG810 (b c d f : k) : k :=
  7 * b ^ 10 * c * d + (-35 : k) * b ^ 9 * c ^ 3 + (-36 : k) * b ^ 9 * d * f
  + 560 * b ^ 8 * c ^ 2 * f + 156 * b ^ 8 * d ^ 3 + 980 * b ^ 7 * c ^ 2 * d ^ 2
  + (-2640 : k) * b ^ 7 * c * f ^ 2 + (-2320 : k) * b ^ 6 * c ^ 4 * d
  + (-4640 : k) * b ^ 6 * c * d ^ 2 * f + 3200 * b ^ 6 * f ^ 3 + 30560 * b ^ 5 * c ^ 3 * d * f
  + (-600 : k) * b ^ 5 * c * d ^ 4 + 8000 * b ^ 5 * d ^ 2 * f ^ 2 + 7840 * b ^ 4 * c ^ 3 * d ^ 3
  + (-119040 : k) * b ^ 4 * c ^ 2 * d * f ^ 2 + 13760 * b ^ 4 * d ^ 4 * f
  + (-40960 : k) * b ^ 3 * c ^ 2 * d ^ 3 * f + 197120 * b ^ 3 * c * d * f ^ 3
  + 3360 * b ^ 3 * d ^ 6 + (-12800 : k) * b ^ 2 * c ^ 2 * d ^ 5
  + 64000 * b ^ 2 * c * d ^ 3 * f ^ 2 + (-102400 : k) * b ^ 2 * d * f ^ 4
  + (-64000 : k) * b * c * d ^ 5 * f + 102400 * b * d ^ 3 * f ^ 3 + 76800 * d ^ 5 * f ^ 2

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_T_U25a
    (b c d e f : k) :
    (
      (-4 : k) * b ^ 5 * c + 32 * b ^ 4 * f + 168 * b ^ 3 * d ^ 2
      ) *
        quarticCoreT_ABCDEFG810 b c d e f +
    (
      (-40 : k) * b ^ 4 * d + 120 * b ^ 3 * c ^ 2 + (-1120 : k) * b ^ 2 * c * f
      + (-320 : k) * b * c * d ^ 2 + 1280 * b * f ^ 2 + (-1920 : k) * d ^ 2 * f
      ) *
        quarticCoreU25aABCDEFG810 b c d e f =
      (-4 : k) * b * quarticCoreResE_T_U25aABCDEFG810 b c d f := by
  simp only [quarticCoreT_ABCDEFG810, quarticCoreU25aABCDEFG810, quarticCoreResE_T_U25aABCDEFG810]
  ring

def quarticCoreResE_U22_VABCDEFG810 (b c d f : k) : k :=
  2 * b ^ 10 * c * f + (-11 : k) * b ^ 9 * c * d ^ 2 + (-16 : k) * b ^ 9 * f ^ 2
  + 84 * b ^ 8 * c ^ 3 * d + 88 * b ^ 8 * d ^ 2 * f + 720 * b ^ 7 * c ^ 5
  + (-1184 : k) * b ^ 7 * c ^ 2 * d * f + (-7760 : k) * b ^ 6 * c ^ 4 * f
  + 3264 * b ^ 6 * c ^ 2 * d ^ 3 + 2368 * b ^ 6 * c * d * f ^ 2 + 14760 * b ^ 5 * c ^ 4 * d ^ 2
  + 32960 * b ^ 5 * c ^ 3 * f ^ 2 + (-7872 : k) * b ^ 5 * c * d ^ 3 * f
  + (-77600 : k) * b ^ 4 * c ^ 3 * d ^ 2 * f + (-67840 : k) * b ^ 4 * c ^ 2 * f ^ 3
  + 3360 * b ^ 4 * c * d ^ 5 + 2560 * b ^ 4 * d ^ 3 * f ^ 2 + 28640 * b ^ 3 * c ^ 3 * d ^ 4
  + 132480 * b ^ 3 * c ^ 2 * d ^ 2 * f ^ 2 + 56320 * b ^ 3 * c * f ^ 4
  + (-5120 : k) * b ^ 3 * d ^ 5 * f + (-117120 : k) * b ^ 2 * c ^ 2 * d ^ 4 * f
  + (-94720 : k) * b ^ 2 * c * d ^ 2 * f ^ 3 + (-7680 : k) * b * c ^ 2 * d ^ 6
  + 148480 * b * c * d ^ 4 * f ^ 2 + 61440 * b * d ^ 2 * f ^ 4 + 10240 * c * d ^ 6 * f
  + (-40960 : k) * d ^ 4 * f ^ 3

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_U22_V
    (b c d e f : k) :
    (
      840 * b ^ 6 * c + (-3040 : k) * b ^ 5 * f + (-7360 : k) * b ^ 4 * d ^ 2
      + 32960 * b ^ 3 * c ^ 2 * d + (-85760 : k) * b ^ 2 * c * d * f + 15360 * b * c * d ^ 3
      + 30720 * b * d * f ^ 2 + (-20480 : k) * d ^ 3 * f
      ) *
        quarticCoreU22ABCDEFG810 b c d e f +
    (
      (-40 : k) * b ^ 4 * c + 160 * b ^ 3 * f + 320 * b ^ 2 * d ^ 2
      ) *
        quarticCoreV_ABCDEFG810 b c d e f =
      (-320 : k) * b * quarticCoreResE_U22_VABCDEFG810 b c d f := by
  simp only [quarticCoreU22ABCDEFG810, quarticCoreV_ABCDEFG810, quarticCoreResE_U22_VABCDEFG810]
  ring

def quarticCoreResE_U25a_VABCDEFG810 (b c d f : k) : k :=
  147 * b ^ 12 * c ^ 2 + (-1104 : k) * b ^ 11 * c * f + 976 * b ^ 10 * c * d ^ 2
  + 1264 * b ^ 10 * f ^ 2 + 18200 * b ^ 9 * c ^ 3 * d + (-4864 : k) * b ^ 9 * d ^ 2 * f
  + 5760 * b ^ 8 * c ^ 5 + (-116320 : k) * b ^ 8 * c ^ 2 * d * f + 13800 * b ^ 8 * d ^ 4
  + (-85120 : k) * b ^ 7 * c ^ 4 * f + 136320 * b ^ 7 * c ^ 2 * d ^ 3
  + 237440 * b ^ 7 * c * d * f ^ 2 + 383680 * b ^ 6 * c ^ 4 * d ^ 2
  + 419840 * b ^ 6 * c ^ 3 * f ^ 2 + (-300800 : k) * b ^ 6 * c * d ^ 3 * f
  + (-161280 : k) * b ^ 6 * d * f ^ 3 + (-2073600 : k) * b ^ 5 * c ^ 3 * d ^ 2 * f
  + (-972800 : k) * b ^ 5 * c ^ 2 * f ^ 3 + 252160 * b ^ 5 * c * d ^ 5
  + (-15360 : k) * b ^ 5 * d ^ 3 * f ^ 2 + 400000 * b ^ 4 * c ^ 3 * d ^ 4
  + 3978240 * b ^ 4 * c ^ 2 * d ^ 2 * f ^ 2 + 901120 * b ^ 4 * c * f ^ 4
  + (-471040 : k) * b ^ 4 * d ^ 5 * f + (-1228800 : k) * b ^ 3 * c ^ 2 * d ^ 4 * f
  + (-3686400 : k) * b ^ 3 * c * d ^ 2 * f ^ 3 + (-614400 : k) * b ^ 2 * c ^ 2 * d ^ 6
  + 1484800 * b ^ 2 * c * d ^ 4 * f ^ 2 + 2457600 * b ^ 2 * d ^ 2 * f ^ 4
  + 1433600 * b * c * d ^ 6 * f + (-409600 : k) * b * d ^ 4 * f ^ 3
  + (-819200 : k) * d ^ 6 * f ^ 2

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_U25a_V
    (b c d e f : k) :
    (
      840 * b ^ 6 * c + (-3040 : k) * b ^ 5 * f + (-7360 : k) * b ^ 4 * d ^ 2
      + 32960 * b ^ 3 * c ^ 2 * d + (-85760 : k) * b ^ 2 * c * d * f + 15360 * b * c * d ^ 3
      + 30720 * b * d * f ^ 2 + (-20480 : k) * d ^ 3 * f
      ) *
        quarticCoreU25aABCDEFG810 b c d e f +
    (
      4 * b ^ 5 * c + (-32 : k) * b ^ 4 * f + (-168 : k) * b ^ 3 * d ^ 2
      ) *
        quarticCoreV_ABCDEFG810 b c d e f =
      (4 : k) * b * quarticCoreResE_U25a_VABCDEFG810 b c d f := by
  simp only [quarticCoreU25aABCDEFG810, quarticCoreV_ABCDEFG810, quarticCoreResE_U25a_VABCDEFG810]
  ring

def quarticCoreResE_U22_U24ABCDEFG810 (b c d f : k) : k :=
  7 * b ^ 12 * c ^ 2 + (-80 : k) * b ^ 11 * c * f + 20 * b ^ 10 * c * d ^ 2
  + 240 * b ^ 10 * f ^ 2 + 840 * b ^ 9 * c ^ 3 * d + (-240 : k) * b ^ 9 * d ^ 2 * f
  + 2000 * b ^ 8 * c ^ 5 + (-9760 : k) * b ^ 8 * c ^ 2 * d * f + 360 * b ^ 8 * d ^ 4
  + (-25600 : k) * b ^ 7 * c ^ 4 * f + 12800 * b ^ 7 * c ^ 2 * d ^ 3
  + 26240 * b ^ 7 * c * d * f ^ 2 + 42400 * b ^ 6 * c ^ 4 * d ^ 2
  + 128000 * b ^ 6 * c ^ 3 * f ^ 2 + (-43520 : k) * b ^ 6 * c * d ^ 3 * f
  + (-12800 : k) * b ^ 6 * d * f ^ 3 + (-262400 : k) * b ^ 5 * c ^ 3 * d ^ 2 * f
  + (-307200 : k) * b ^ 5 * c ^ 2 * f ^ 3 + (-73920 : k) * b ^ 5 * c * d ^ 5
  + 51200 * b ^ 5 * d ^ 3 * f ^ 2 + (-198400 : k) * b ^ 4 * c ^ 3 * d ^ 4
  + 460800 * b ^ 4 * c ^ 2 * d ^ 2 * f ^ 2 + 307200 * b ^ 4 * c * f ^ 4
  + 57600 * b ^ 4 * d ^ 5 * f + 422400 * b ^ 3 * c ^ 2 * d ^ 4 * f
  + (-307200 : k) * b ^ 3 * c * d ^ 2 * f ^ 3 + (-38400 : k) * b ^ 3 * d ^ 7
  + (-614400 : k) * b ^ 2 * c ^ 2 * d ^ 6 + (-102400 : k) * b ^ 2 * c * d ^ 4 * f ^ 2
  + 614400 * b ^ 2 * d ^ 2 * f ^ 4 + 1177600 * b * c * d ^ 6 * f + 614400 * b * d ^ 4 * f ^ 3
  + 102400 * c * d ^ 8 + (-409600 : k) * d ^ 6 * f ^ 2

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_U22_U24
    (b c d e f : k) :
    (
      (-4160 : k) * b ^ 10 * c + 19200 * b ^ 9 * f + 12800 * b ^ 8 * c * e
      + 19200 * b ^ 8 * d ^ 2 + (-230400 : k) * b ^ 7 * c ^ 2 * d + (-51200 : k) * b ^ 7 * e * f
      + 972800 * b ^ 6 * c * d * f + (-102400 : k) * b ^ 6 * d ^ 2 * e
      + 1228800 * b ^ 5 * c * d ^ 3 + (-614400 : k) * b ^ 5 * d * f ^ 2
      + (-614400 : k) * b ^ 4 * d ^ 3 * f + 409600 * b ^ 3 * d ^ 5
      ) *
        quarticCoreU22ABCDEFG810 b c d e f +
    (
      1600 * b ^ 8 * c ^ 2 + (-12800 : k) * b ^ 7 * c * f + (-25600 : k) * b ^ 6 * c * d ^ 2
      + 25600 * b ^ 6 * f ^ 2 + 102400 * b ^ 5 * d ^ 2 * f + 102400 * b ^ 4 * d ^ 4
      ) *
        quarticCoreU24ABCDEFG810 b c d e f =
      (640 : k) * b ^ 4 * quarticCoreResE_U22_U24ABCDEFG810 b c d f := by
  simp only [quarticCoreU22ABCDEFG810, quarticCoreU24ABCDEFG810, quarticCoreResE_U22_U24ABCDEFG810]
  ring

def quarticCoreResE_T_VABCDEFG810 (b c d f : k) : k :=
  147 * b ^ 11 * c ^ 3 + 92 * b ^ 11 * d * f + (-2320 : k) * b ^ 10 * c ^ 2 * f
  + (-506 : k) * b ^ 10 * d ^ 3 + (-1996 : k) * b ^ 9 * c ^ 2 * d ^ 2
  + 10736 * b ^ 9 * c * f ^ 2 + 14360 * b ^ 8 * c ^ 4 * d + 8320 * b ^ 8 * c * d ^ 2 * f
  + (-12672 : k) * b ^ 8 * f ^ 3 + (-8640 : k) * b ^ 7 * c ^ 6
  + (-175680 : k) * b ^ 7 * c ^ 3 * d * f + (-1624 : k) * b ^ 7 * c * d ^ 4
  + (-13440 : k) * b ^ 7 * d ^ 2 * f ^ 2 + 139200 * b ^ 6 * c ^ 5 * f
  + (-29520 : k) * b ^ 6 * c ^ 3 * d ^ 3 + 641280 * b ^ 6 * c ^ 2 * d * f ^ 2
  + (-35008 : k) * b ^ 6 * d ^ 4 * f + 40480 * b ^ 5 * c ^ 5 * d ^ 2
  + (-800000 : k) * b ^ 5 * c ^ 4 * f ^ 2 + 64960 * b ^ 5 * c ^ 2 * d ^ 3 * f
  + (-885760 : k) * b ^ 5 * c * d * f ^ 3 + (-7360 : k) * b ^ 5 * d ^ 6
  + (-627840 : k) * b ^ 4 * c ^ 4 * d ^ 2 * f + 2298880 * b ^ 4 * c ^ 3 * f ^ 3
  + 41920 * b ^ 4 * c ^ 2 * d ^ 5 + 55040 * b ^ 4 * c * d ^ 3 * f ^ 2
  + 317440 * b ^ 4 * d * f ^ 4 + (-149760 : k) * b ^ 3 * c ^ 4 * d ^ 4
  + 2572800 * b ^ 3 * c ^ 3 * d ^ 2 * f ^ 2 + (-3297280 : k) * b ^ 3 * c ^ 2 * f ^ 4
  + 1280 * b ^ 3 * c * d ^ 5 * f + (-394240 : k) * b ^ 3 * d ^ 3 * f ^ 3
  + (-391680 : k) * b ^ 2 * c ^ 3 * d ^ 4 * f + (-2836480 : k) * b ^ 2 * c ^ 2 * d ^ 2 * f ^ 3
  + 15360 * b ^ 2 * c * d ^ 7 + 1802240 * b ^ 2 * c * f ^ 5 + 61440 * b ^ 2 * d ^ 5 * f ^ 2
  + 2631680 * b * c ^ 2 * d ^ 4 * f ^ 2 + (-655360 : k) * b * c * d ^ 2 * f ^ 4
  + (-20480 : k) * b * d ^ 7 * f + (-2457600 : k) * c * d ^ 4 * f ^ 3

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_T_V
    (b c d e f : k) :
    (
      840 * b ^ 6 * c + (-3040 : k) * b ^ 5 * f + (-7360 : k) * b ^ 4 * d ^ 2
      + 32960 * b ^ 3 * c ^ 2 * d + (-85760 : k) * b ^ 2 * c * d * f + 15360 * b * c * d ^ 3
      + 30720 * b * d * f ^ 2 + (-20480 : k) * d ^ 3 * f
      ) *
        quarticCoreT_ABCDEFG810 b c d e f +
    (
      (-40 : k) * b ^ 4 * d + 120 * b ^ 3 * c ^ 2 + (-1120 : k) * b ^ 2 * c * f
      + (-320 : k) * b * c * d ^ 2 + 1280 * b * f ^ 2 + (-1920 : k) * d ^ 2 * f
      ) *
        quarticCoreV_ABCDEFG810 b c d e f =
      (-80 : k) * quarticCoreResE_T_VABCDEFG810 b c d f := by
  simp only [quarticCoreT_ABCDEFG810, quarticCoreV_ABCDEFG810, quarticCoreResE_T_VABCDEFG810]
  ring

def quarticCoreResE_U25a_U24ABCDEFG810 (b c d f : k) : k :=
  21 * b ^ 13 * c ^ 2 + (-256 : k) * b ^ 12 * c * f + 36 * b ^ 11 * c * d ^ 2
  + 784 * b ^ 11 * f ^ 2 + 3920 * b ^ 10 * c ^ 3 * d + (-48 : k) * b ^ 10 * d ^ 2 * f
  + 800 * b ^ 9 * c ^ 5 + (-40640 : k) * b ^ 9 * c ^ 2 * d * f + 1944 * b ^ 9 * d ^ 4
  + (-16640 : k) * b ^ 8 * c ^ 4 * f + (-13920 : k) * b ^ 8 * c ^ 2 * d ^ 3
  + 116480 * b ^ 8 * c * d * f ^ 2 + 132800 * b ^ 7 * c ^ 4 * d ^ 2
  + 120320 * b ^ 7 * c ^ 3 * f ^ 2 + 64000 * b ^ 7 * c * d ^ 3 * f
  + (-87040 : k) * b ^ 7 * d * f ^ 3 + (-921600 : k) * b ^ 6 * c ^ 3 * d ^ 2 * f
  + (-368640 : k) * b ^ 6 * c ^ 2 * f ^ 3 + (-562560 : k) * b ^ 6 * c * d ^ 5
  + 74240 * b ^ 6 * d ^ 3 * f ^ 2 + (-2051200 : k) * b ^ 5 * c ^ 3 * d ^ 4
  + 2181120 * b ^ 5 * c ^ 2 * d ^ 2 * f ^ 2 + 491520 * b ^ 5 * c * f ^ 4
  + 629760 * b ^ 5 * d ^ 5 * f + 6876160 * b ^ 4 * c ^ 2 * d ^ 4 * f
  + (-2334720 : k) * b ^ 4 * c * d ^ 2 * f ^ 3 + (-322560 : k) * b ^ 4 * d ^ 7
  + (-2630400 : k) * b ^ 3 * c ^ 2 * d ^ 6 + (-8857600 : k) * b ^ 3 * c * d ^ 4 * f ^ 2
  + 3686400 * b ^ 3 * d ^ 2 * f ^ 4 + 1587200 * b ^ 2 * c * d ^ 6 * f
  + 10649600 * b ^ 2 * d ^ 4 * f ^ 3 + 2150400 * b * c * d ^ 8 + 102400 * b * d ^ 6 * f ^ 2
  + (-2150400 : k) * d ^ 8 * f

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_U25a_U24
    (b c d e f : k) :
    (
      640 * b ^ 11 * c + (-4480 : k) * b ^ 10 * f + (-1280 : k) * b ^ 9 * c * e
      + (-12480 : k) * b ^ 9 * d ^ 2 + 40960 * b ^ 8 * c ^ 2 * d + 10240 * b ^ 8 * e * f
      + (-225280 : k) * b ^ 7 * c * d * f + 53760 * b ^ 7 * d ^ 2 * e
      + (-691200 : k) * b ^ 6 * c * d ^ 3 + 184320 * b ^ 6 * d * f ^ 2
      + 440320 * b ^ 5 * d ^ 3 * f + (-215040 : k) * b ^ 4 * d ^ 5
      ) *
        quarticCoreU25aABCDEFG810 b c d e f +
    (
      16 * b ^ 10 * c ^ 2 + (-256 : k) * b ^ 9 * c * f + (-1344 : k) * b ^ 8 * c * d ^ 2
      + 1024 * b ^ 8 * f ^ 2 + 10752 * b ^ 7 * d ^ 2 * f + 28224 * b ^ 6 * d ^ 4
      ) *
        quarticCoreU24ABCDEFG810 b c d e f =
      (16 : k) * b ^ 5 * quarticCoreResE_U25a_U24ABCDEFG810 b c d f := by
  simp only [quarticCoreU25aABCDEFG810, quarticCoreU24ABCDEFG810, quarticCoreResE_U25a_U24ABCDEFG810]
  ring

def quarticCoreResE_U22_U25bABCDEFG810 (b c d f : k) : k :=
  49 * b ^ 12 * c ^ 3 + (-712 : k) * b ^ 11 * c ^ 2 * f + 360 * b ^ 10 * c ^ 2 * d ^ 2
  + 3440 * b ^ 10 * c * f ^ 2 + 4200 * b ^ 9 * c ^ 4 * d + (-4320 : k) * b ^ 9 * c * d ^ 2 * f
  + (-5120 : k) * b ^ 9 * f ^ 3 + (-400 : k) * b ^ 8 * c ^ 6
  + (-51360 : k) * b ^ 8 * c ^ 3 * d * f + 760 * b ^ 8 * c * d ^ 4
  + 8320 * b ^ 8 * d ^ 2 * f ^ 2 + 1600 * b ^ 7 * c ^ 5 * f + 37760 * b ^ 7 * c ^ 3 * d ^ 3
  + 197760 * b ^ 7 * c ^ 2 * d * f ^ 2 + 8320 * b ^ 7 * d ^ 4 * f
  + 116800 * b ^ 6 * c ^ 5 * d ^ 2 + 25600 * b ^ 6 * c ^ 4 * f ^ 2
  + (-280320 : k) * b ^ 6 * c ^ 2 * d ^ 3 * f + (-320000 : k) * b ^ 6 * c * d * f ^ 3
  + (-1024000 : k) * b ^ 5 * c ^ 4 * d ^ 2 * f + (-204800 : k) * b ^ 5 * c ^ 3 * f ^ 3
  + (-62400 : k) * b ^ 5 * c ^ 2 * d ^ 5 + 752640 * b ^ 5 * c * d ^ 3 * f ^ 2
  + 204800 * b ^ 5 * d * f ^ 4 + 400000 * b ^ 4 * c ^ 4 * d ^ 4
  + 3840000 * b ^ 4 * c ^ 3 * d ^ 2 * f ^ 2 + 512000 * b ^ 4 * c ^ 2 * f ^ 4
  + 697600 * b ^ 4 * c * d ^ 5 * f + (-614400 : k) * b ^ 4 * d ^ 3 * f ^ 3
  + (-1651200 : k) * b ^ 3 * c ^ 3 * d ^ 4 * f + (-7884800 : k) * b ^ 3 * c ^ 2 * d ^ 2 * f ^ 3
  + 268800 * b ^ 3 * c * d ^ 7 + (-409600 : k) * b ^ 3 * c * f ^ 5
  + (-921600 : k) * b ^ 3 * d ^ 5 * f ^ 2 + 435200 * b ^ 2 * c ^ 3 * d ^ 6
  + 1382400 * b ^ 2 * c ^ 2 * d ^ 4 * f ^ 2 + 9420800 * b ^ 2 * c * d ^ 2 * f ^ 4
  + (-204800 : k) * b ^ 2 * d ^ 7 * f + (-1484800 : k) * b * c ^ 2 * d ^ 6 * f
  + 3481600 * b * c * d ^ 4 * f ^ 3 + (-4915200 : k) * b * d ^ 2 * f ^ 5
  + (-512000 : k) * c ^ 2 * d ^ 8 + 2867200 * c * d ^ 6 * f ^ 2 + (-3276800 : k) * d ^ 4 * f ^ 4

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_U22_U25b
    (b c d e f : k) :
    (
      (-1120 : k) * b ^ 9 * c ^ 2 + 13760 * b ^ 8 * c * f + (-22400 : k) * b ^ 7 * c ^ 2 * e
      + 107200 * b ^ 7 * c * d ^ 2 + (-44800 : k) * b ^ 7 * f ^ 2 + 73600 * b ^ 6 * c ^ 3 * d
      + 140800 * b ^ 6 * c * e * f + (-460800 : k) * b ^ 6 * d ^ 2 * f
      + (-448000 : k) * b ^ 5 * c ^ 2 * d * f + 179200 * b ^ 5 * c * d ^ 2 * e
      + (-588800 : k) * b ^ 5 * d ^ 4 + (-204800 : k) * b ^ 5 * e * f ^ 2
      + 332800 * b ^ 4 * c ^ 2 * d ^ 3 + 1228800 * b ^ 4 * c * d * f ^ 2
      + (-409600 : k) * b ^ 4 * d ^ 2 * e * f + (-51200 : k) * b ^ 3 * c * d ^ 3 * f
      + (-1228800 : k) * b ^ 3 * d * f ^ 3 + 512000 * b ^ 2 * c * d ^ 5
      + (-819200 : k) * b ^ 2 * d ^ 3 * f ^ 2
      ) *
        quarticCoreU22ABCDEFG810 b c d e f +
    (
      1600 * b ^ 8 * c ^ 2 + (-12800 : k) * b ^ 7 * c * f + (-25600 : k) * b ^ 6 * c * d ^ 2
      + 25600 * b ^ 6 * f ^ 2 + 102400 * b ^ 5 * d ^ 2 * f + 102400 * b ^ 4 * d ^ 4
      ) *
        quarticCoreU25bABCDEFG810 b c d e f =
      (-160 : k) * b ^ 3 * quarticCoreResE_U22_U25bABCDEFG810 b c d f := by
  simp only [quarticCoreU22ABCDEFG810, quarticCoreU25bABCDEFG810, quarticCoreResE_U22_U25bABCDEFG810]
  ring

/-! ## Residual: five-polynomial kill set plus e-free layer

On the cone the cores and `T` vanish, hence `U22 = U24 = U25a = U25b = 0`,
hence `P19 = P21 = P22 = 0` after cancelling `B.leadingCoeff ≠ 0`, hence
`V = D1 = 0` and the pairwise e-resultants vanish.  The remaining system
is e-free in `(b, c, d, f)`.
-/

set_option maxHeartbeats 16000000 in
theorem quarticConeABCDEFG810_residual3
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    quarticCoreU22ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreU24ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreU25aABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreU25bABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreP19ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreP21ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreP22ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreV_ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreD1ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResE_U22_TABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResE_T_U25aABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResE_U22_VABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResE_U25a_VABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResE_U22_U24ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResE_T_VABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResE_U25a_U24ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResE_U22_U25bABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 := by
  have hres2 := quarticConeABCDEFG810_residual2 (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  rcases hres2 with ⟨hk, hmu0, hnu0, hxi0, hom0, hpi0, hpr0, hcmu, hcnu, hcxi, hcom, hcpi, hcpr, hmn, hnx, hno, hT, hlin, hmnE, hnxE⟩
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, _⟩
    omega
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, _⟩
    omega
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, _⟩
    omega
  have hClc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, _⟩
    omega
  have hDlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, _⟩
    omega
  have hElc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, _⟩
    omega
  have hFlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, _⟩
    omega
  have hGlc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have hU22mul : (76 : k) * quarticCoreU22ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCoreU22_from_cores A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hcmu, hcnu, hcxi, hcom, hcpi, hcpr] at hid
    simp only [mul_zero, add_zero] at hid
    exact hid
  have hU22 : quarticCoreU22ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hcnt : (76 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hU22mul
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hU24mul : (2 : k) * quarticCoreU24ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCoreU24_from_cores A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hcnu, hcom, hcpr] at hid
    simp only [mul_zero, add_zero] at hid
    exact hid
  have hU24 : quarticCoreU24ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hcnt : (2 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hU24mul
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hU25amul : (304 : k) * quarticCoreU25aABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCoreU25a_from_cores A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hcmu, hcnu, hcxi, hcom, hcpi, hcpr] at hid
    simp only [mul_zero, add_zero] at hid
    exact hid
  have hU25a : quarticCoreU25aABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hcnt : (304 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hU25amul
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hU25bmul : (304 : k) * quarticCoreU25bABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCoreU25b_from_cores A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hcmu, hcnu, hcxi, hcom, hcpi, hcpr] at hid
    simp only [mul_zero, add_zero] at hid
    exact hid
  have hU25b : quarticCoreU25bABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hcnt : (304 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hU25bmul
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hP19 : quarticCoreP19ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCoreU22_eq_b_P19 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hU22] at hid
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hBlc h).elim
    · exact h
  have hP21 : quarticCoreP21ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCoreU24_eq_b_P21 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hU24] at hid
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hBlc h).elim
    · exact h
  have hP22 : quarticCoreP22ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCoreU25a_eq_b_P22 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hU25a] at hid
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hBlc h).elim
    · exact h
  have hV : quarticCoreV_ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCoreV_from_U24_U25b B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hU24, hU25b] at hid
    simp only [mul_zero, add_zero] at hid
    have hmul := mul_eq_zero.mp hid
    rcases hmul with h | h
    · exact (hBlc h).elim
    · exact h
  have hD1 : quarticCoreD1ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCoreD1_from_P19_P22 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hP22, hP19] at hid
    simp only [mul_zero, sub_zero] at hid
    exact hid
  have hResE_U22_T : quarticCoreResE_U22_TABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resE_U22_T B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hU22, hT] at hid
    simp only [mul_zero, add_zero] at hid
    have hid' := hid.symm
    have hne : (80 : k) * B.leadingCoeff ≠ 0 := mul_ne_zero ((by norm_num : (80 : k) ≠ 0)) (hBlc)
    exact (mul_eq_zero.mp hid').resolve_left hne
  have hResE_T_U25a : quarticCoreResE_T_U25aABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resE_T_U25a B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hT, hU25a] at hid
    simp only [mul_zero, add_zero] at hid
    have hid' := hid.symm
    have hne : (-4 : k) * B.leadingCoeff ≠ 0 := mul_ne_zero ((by norm_num : (-4 : k) ≠ 0)) (hBlc)
    exact (mul_eq_zero.mp hid').resolve_left hne
  have hResE_U22_V : quarticCoreResE_U22_VABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resE_U22_V B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hU22, hV] at hid
    simp only [mul_zero, add_zero] at hid
    have hid' := hid.symm
    have hne : (-320 : k) * B.leadingCoeff ≠ 0 := mul_ne_zero ((by norm_num : (-320 : k) ≠ 0)) (hBlc)
    exact (mul_eq_zero.mp hid').resolve_left hne
  have hResE_U25a_V : quarticCoreResE_U25a_VABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resE_U25a_V B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hU25a, hV] at hid
    simp only [mul_zero, add_zero] at hid
    have hid' := hid.symm
    have hne : (4 : k) * B.leadingCoeff ≠ 0 := mul_ne_zero ((by norm_num : (4 : k) ≠ 0)) (hBlc)
    exact (mul_eq_zero.mp hid').resolve_left hne
  have hResE_U22_U24 : quarticCoreResE_U22_U24ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resE_U22_U24 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hU22, hU24] at hid
    simp only [mul_zero, add_zero] at hid
    have hid' := hid.symm
    have hne : (640 : k) * B.leadingCoeff ^ 4 ≠ 0 := mul_ne_zero ((by norm_num : (640 : k) ≠ 0)) (pow_ne_zero 4 hBlc)
    exact (mul_eq_zero.mp hid').resolve_left hne
  have hResE_T_V : quarticCoreResE_T_VABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resE_T_V B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hT, hV] at hid
    simp only [mul_zero, add_zero] at hid
    have hid' := hid.symm
    have hne : (-80 : k) ≠ 0 := (by norm_num : (-80 : k) ≠ 0)
    exact (mul_eq_zero.mp hid').resolve_left hne
  have hResE_U25a_U24 : quarticCoreResE_U25a_U24ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resE_U25a_U24 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hU25a, hU24] at hid
    simp only [mul_zero, add_zero] at hid
    have hid' := hid.symm
    have hne : (16 : k) * B.leadingCoeff ^ 5 ≠ 0 := mul_ne_zero ((by norm_num : (16 : k) ≠ 0)) (pow_ne_zero 5 hBlc)
    exact (mul_eq_zero.mp hid').resolve_left hne
  have hResE_U22_U25b : quarticCoreResE_U22_U25bABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resE_U22_U25b B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hU22, hU25b] at hid
    simp only [mul_zero, add_zero] at hid
    have hid' := hid.symm
    have hne : (-160 : k) * B.leadingCoeff ^ 3 ≠ 0 := mul_ne_zero ((by norm_num : (-160 : k) ≠ 0)) (pow_ne_zero 3 hBlc)
    exact (mul_eq_zero.mp hid').resolve_left hne
  exact ⟨hU22, hU24, hU25a, hU25b, hP19, hP21, hP22, hV, hD1, hResE_U22_T, hResE_T_U25a, hResE_U22_V, hResE_U25a_V, hResE_U22_U24, hResE_T_V, hResE_U25a_U24, hResE_U22_U25b⟩

#print axioms kappaQuarticInnerABCDEFG810_weightedHomogeneous
#print axioms muQuarticInnerABCDEFG810_weightedHomogeneous
#print axioms nuQuarticInnerABCDEFG810_weightedHomogeneous
#print axioms xiQuarticInnerABCDEFG810_weightedHomogeneous
#print axioms omicronQuarticInnerABCDEFG810_weightedHomogeneous
#print axioms piQuarticInnerABCDEFG810_weightedHomogeneous
#print axioms primitiveQuarticInnerABCDEFG810_weightedHomogeneous
#print axioms quarticCoreU22_from_cores
#print axioms quarticCoreU24_from_cores
#print axioms quarticCoreU25a_from_cores
#print axioms quarticCoreU25b_from_cores
#print axioms quarticCoreU22_eq_b_P19
#print axioms quarticCoreU24_eq_b_P21
#print axioms quarticCoreU25a_eq_b_P22
#print axioms quarticCoreV_from_U24_U25b
#print axioms quarticCoreD1_from_P19_P22
#print axioms quarticConeABCDEFG810_residual3
#print axioms quarticCore_resE_U22_U25a
#print axioms quarticCore_resE_U22_T
#print axioms quarticCore_resE_T_U25a
#print axioms quarticCore_resE_U22_V
#print axioms quarticCore_resE_U25a_V
#print axioms quarticCore_resE_U22_U24
#print axioms quarticCore_resE_T_V
#print axioms quarticCore_resE_U25a_U24
#print axioms quarticCore_resE_U22_U25b


end QuarticFullConeABCDEFG810Ladder

end Max11DegreeRoutes
