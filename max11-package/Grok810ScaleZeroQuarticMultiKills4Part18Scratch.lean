import Grok810ScaleZeroQuarticMultiKills4Part17Scratch

/-! # Part 18 of `Grok810ScaleZeroQuarticMultiKills4Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills4Scratch`; statements are byte-identical.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]

def xiQuarticInnerABEFG810 (a b e f g : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + (-160 : k) * b ^ 2 * g + 640 * e * g + 320 * f ^ 2

def omicronQuarticInnerABEFG810 (a b e f g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-160 : k) * a ^ 2 * b * g + 1600 * a * b ^ 2 * f + (-2560 : k) * a * e * f + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + (-5120 : k) * b * e ^ 2 + 20480 * f * g

def piQuarticInnerABEFG810 (a b e f g : k) : k :=
  15 * a ^ 2 * b ^ 4 + 320 * a * b ^ 2 * g + (-1280 : k) * a * f ^ 2 + 800 * b ^ 3 * f + (-3840 : k) * b * e * f + 5120 * g ^ 2

def primitiveQuarticInnerABEFG810 (a b e f g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-160 : k) * a ^ 3 * b * g + (-160 : k) * a ^ 2 * b ^ 2 * f + (-1280 : k) * a ^ 2 * e * f + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + 5120 * a * b * e ^ 2 + (-20480 : k) * a * f * g + 3840 * b ^ 3 * g + (-20480 : k) * b * e * g + (-20480 : k) * b * f ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_ABEFG_identity
    (a b e f g : k) :
    ((165 / 729088 : k) * a ^ 5 * b + (-5599 / 182272 : k) * a ^ 3 * f + (31599 / 23330816 : k) * a ^ 2 * b ^ 3 + (-109339 / 14581760 : k) * a ^ 2 * b * e + (-5787 / 1822720 : k) * a * b * g + (-2471 / 1822720 : k) * b ^ 2 * f + (10317 / 227840 : k) * e * f) * kappaQuarticInnerABEFG810 a b e f g +
      ((-55 / 91136 : k) * a ^ 3 * b ^ 2 + (-55 / 2848 : k) * a ^ 2 * g + (33 / 45568 : k) * a * b * f + (21 / 81920 : k) * b ^ 4 + (-41 / 10240 : k) * b ^ 2 * e + (1 / 320 : k) * e ^ 2) * muQuarticInnerABEFG810 a b e f g +
      ((55 / 364544 : k) * a ^ 4 * b + (-165 / 91136 : k) * a ^ 2 * f + (8063 / 7290880 : k) * a * b * e + (1253 / 1822720 : k) * b * g) * nuQuarticInnerABEFG810 a b e f g +
      ((-121 / 45568 : k) * a ^ 2 * b ^ 2 + (55 / 5696 : k) * a ^ 2 * e + (-11 / 2848 : k) * a * g) * xiQuarticInnerABEFG810 a b e f g +
      ((55 / 729088 : k) * a ^ 3 * b + (11 / 182272 : k) * a * f + (7 / 262144 : k) * b ^ 3 + (-13 / 32768 : k) * b * e) * omicronQuarticInnerABEFG810 a b e f g +
      ((11 / 22784 : k) * a * e) * piQuarticInnerABEFG810 a b e f g =
      e ^ 4 := by
  simp only [kappaQuarticInnerABEFG810, muQuarticInnerABEFG810, nuQuarticInnerABEFG810, xiQuarticInnerABEFG810, omicronQuarticInnerABEFG810, piQuarticInnerABEFG810, primitiveQuarticInnerABEFG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_ABEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoABEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABEFG810, degreeZeroKappaQuarticNoABEFG810]
  all_goals module

end QuarticKills810

end Max11DegreeRoutes
