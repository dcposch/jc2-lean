import Grok810ScaleZeroQuarticConesScratch

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

def kappaQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + (-60 : k) * b * c ^ 2 + 160 * b * g + 160 * c * f + 160 * d * e

def muQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  60 * a * b ^ 2 * c + (-160 : k) * a * b * f + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * c * g + 640 * d * f + 320 * e ^ 2

def nuQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + 60 * a * b * c ^ 2 + (-160 : k) * a * b * g + (-160 : k) * a * c * f + (-160 : k) * a * d * e + 280 * b ^ 3 * c + (-480 : k) * b ^ 2 * f + (-960 : k) * b * c * e + (-480 : k) * b * d ^ 2 + (-480 : k) * c ^ 2 * d + 1280 * d * g + 1280 * e * f

def xiQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + 120 * a * b * c * d + (-160 : k) * a * d * f + 110 * b ^ 3 * d + 180 * b ^ 2 * c ^ 2 + (-160 : k) * b ^ 2 * g + (-400 : k) * b * c * f + (-400 : k) * b * d * e + (-240 : k) * c ^ 2 * e + (-240 : k) * c * d ^ 2 + 640 * e * g + 320 * f ^ 2

def omicronQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * b * g + (-160 : k) * a ^ 2 * c * f + (-160 : k) * a ^ 2 * d * e + (-1120 : k) * a * b ^ 3 * c + 1600 * a * b ^ 2 * f + 1920 * a * b * c * e + 2240 * a * b * d ^ 2 + 960 * a * c ^ 2 * d + (-2560 : k) * a * d * g + (-2560 : k) * a * e * f + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + 8640 * b ^ 2 * c * d + 2880 * b * c ^ 3 + (-7680 : k) * b * c * g + (-10240 : k) * b * d * f + (-5120 : k) * b * e ^ 2 + (-5120 : k) * c ^ 2 * f + (-12800 : k) * c * d * e + (-2560 : k) * d ^ 3 + 20480 * f * g

def piQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + (-360 : k) * a * b ^ 2 * c ^ 2 + 320 * a * b ^ 2 * g + 640 * a * b * c * f + 1280 * a * b * d * e + 640 * a * c * d ^ 2 + (-1280 : k) * a * f ^ 2 + (-560 : k) * b ^ 4 * c + 800 * b ^ 3 * f + 2880 * b ^ 2 * c * e + 1440 * b ^ 2 * d ^ 2 + 2880 * b * c ^ 2 * d + (-2560 : k) * b * d * g + (-3840 : k) * b * e * f + 240 * c ^ 4 + (-1280 : k) * c ^ 2 * g + (-3840 : k) * c * d * f + (-2560 : k) * c * e ^ 2 + (-2560 : k) * d ^ 2 * e + 5120 * g ^ 2

def primitiveQuarticInnerABCDEFG810 (a b c d e f g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * b * g + (-160 : k) * a ^ 3 * c * f + (-160 : k) * a ^ 3 * d * e + 120 * a ^ 2 * b ^ 3 * c + (-160 : k) * a ^ 2 * b ^ 2 * f + 960 * a ^ 2 * b * c * e + (-800 : k) * a ^ 2 * b * d ^ 2 + 480 * a ^ 2 * c ^ 2 * d + (-1280 : k) * a ^ 2 * d * g + (-1280 : k) * a ^ 2 * e * f + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + (-8640 : k) * a * b ^ 2 * c * d + (-960 : k) * a * b * c ^ 3 + 2560 * a * b * c * g + 10240 * a * b * d * f + 5120 * a * b * e ^ 2 + 7680 * a * c * d * e + 2560 * a * d ^ 3 + (-20480 : k) * a * f * g + (-4000 : k) * b ^ 4 * d + (-8480 : k) * b ^ 3 * c ^ 2 + 3840 * b ^ 3 * g + 21760 * b ^ 2 * c * f + 21760 * b ^ 2 * d * e + 23040 * b * c ^ 2 * e + 23040 * b * c * d ^ 2 + (-20480 : k) * b * e * g + (-20480 : k) * b * f ^ 2 + 7680 * c ^ 3 * d + (-20480 : k) * c * d * g + (-40960 : k) * c * e * f + (-20480 : k) * d ^ 2 * f + (-20480 : k) * d * e ^ 2

def quarticCoreMuABCDEFG810 (a b c d e f : k) : k :=
  8 * a * b ^ 3 * c + (-32 : k) * a * b ^ 2 * f + (-16 : k) * a * b * d ^ 2 + 7 * b ^ 5 + (-48 : k) * b ^ 3 * e + (-48 : k) * b ^ 2 * c * d + 32 * b * c ^ 3 + 128 * b * d * f + 64 * b * e ^ 2 + (-128 : k) * c ^ 2 * f + (-128 : k) * c * d * e

def quarticCoreNuABCDEFG810 (a b c d e f : k) : k :=
  2 * a * b ^ 3 * d + 7 * b ^ 4 * c + (-12 : k) * b ^ 3 * f + (-24 : k) * b ^ 2 * c * e + 32 * b * e * f + (-32 : k) * c * d * f + (-32 : k) * d ^ 2 * e

def quarticCoreXiABCDEFG810 (a b c d e f : k) : k :=
  -a * b ^ 5 + 4 * a * b ^ 3 * e + 12 * a * b ^ 2 * c * d + (-16 : k) * a * b * d * f + 5 * b ^ 4 * d + 12 * b ^ 3 * c ^ 2 + (-24 : k) * b ^ 2 * c * f + (-24 : k) * b * c * d ^ 2 + 32 * b * f ^ 2 + (-64 : k) * c * e * f + (-64 : k) * d * e ^ 2

def quarticCoreOmicronABCDEFG810 (a b c d e f : k) : k :=
  (-10 : k) * a ^ 2 * b ^ 3 * d + (-55 : k) * a * b ^ 4 * c + 60 * a * b ^ 3 * f + 120 * a * b ^ 2 * c * e + 80 * a * b ^ 2 * d ^ 2 + (-160 : k) * a * b * e * f + 160 * a * c * d * f + 160 * a * d ^ 2 * e + (-21 : k) * b ^ 6 + 160 * b ^ 4 * e + 360 * b ^ 3 * c * d + (-160 : k) * b ^ 2 * d * f + (-320 : k) * b ^ 2 * e ^ 2 + 640 * b * c ^ 2 * f + (-320 : k) * b * c * d * e + (-160 : k) * b * d ^ 3 + (-1280 : k) * c * f ^ 2 + (-1280 : k) * d * e * f

def quarticCorePiABCDEFG810 (a b c d e f : k) : k :=
  a ^ 2 * b ^ 6 + (-40 : k) * a * b ^ 5 * d + (-32 : k) * a * b ^ 4 * c ^ 2 + 64 * a * b ^ 3 * c * f + 128 * a * b ^ 3 * d * e + 64 * a * b ^ 2 * c * d ^ 2 + (-128 : k) * a * b ^ 2 * f ^ 2 + (-56 : k) * b ^ 6 * c + 80 * b ^ 5 * f + 288 * b ^ 4 * c * e + 120 * b ^ 4 * d ^ 2 + 288 * b ^ 3 * c ^ 2 * d + (-384 : k) * b ^ 3 * e * f + 48 * b ^ 2 * c ^ 4 + (-512 : k) * b ^ 2 * c * d * f + (-256 : k) * b ^ 2 * c * e ^ 2 + (-384 : k) * b ^ 2 * d ^ 2 * e + (-256 : k) * b * c ^ 3 * f + (-256 : k) * b * c ^ 2 * d * e + 512 * c ^ 2 * f ^ 2 + 1024 * c * d * e * f + 512 * d ^ 2 * e ^ 2

def quarticCorePrimitiveABCDEFG810 (a b c d e f : k) : k :=
  (-2 : k) * a ^ 3 * b ^ 3 * d + a ^ 2 * b ^ 4 * c + 12 * a ^ 2 * b ^ 3 * f + 24 * a ^ 2 * b ^ 2 * c * e + (-32 : k) * a ^ 2 * b ^ 2 * d ^ 2 + (-32 : k) * a ^ 2 * b * e * f + 32 * a ^ 2 * c * d * f + 32 * a ^ 2 * d ^ 2 * e + 10 * a * b ^ 6 + (-64 : k) * a * b ^ 4 * e + (-176 : k) * a * b ^ 3 * c * d + 64 * a * b ^ 2 * d * f + 128 * a * b ^ 2 * e ^ 2 + (-256 : k) * a * b * c ^ 2 * f + 128 * a * b * c * d * e + 64 * a * b * d ^ 3 + 512 * a * c * f ^ 2 + 512 * a * d * e * f + (-64 : k) * b ^ 5 * d + (-176 : k) * b ^ 4 * c ^ 2 + 448 * b ^ 3 * c * f + 256 * b ^ 3 * d * e + 384 * b ^ 2 * c ^ 2 * e + 384 * b ^ 2 * c * d ^ 2 + (-512 : k) * b ^ 2 * f ^ 2 + (-512 : k) * b * c * e * f + (-512 : k) * b * d ^ 2 * f + 512 * c ^ 2 * d * f + 512 * c * d ^ 2 * e

set_option maxHeartbeats 32000000 in
theorem quarticInner_ABCDEFG_sylvester_mu
    (a b c d e f g : k) :
    ((-640 : k) * c) * kappaQuarticInnerABCDEFG810 a b c d e f g +
      (160 * b) * muQuarticInnerABCDEFG810 a b c d e f g =
      (800 : k) * quarticCoreMuABCDEFG810 a b c d e f := by
  simp only [kappaQuarticInnerABCDEFG810, muQuarticInnerABCDEFG810, quarticCoreMuABCDEFG810]
  ring

set_option maxHeartbeats 32000000 in
theorem quarticInner_ABCDEFG_sylvester_nu
    (a b c d e f g : k) :
    (160 * a * b + (-1280 : k) * d) * kappaQuarticInnerABCDEFG810 a b c d e f g +
      (160 * b) * nuQuarticInnerABCDEFG810 a b c d e f g =
      (6400 : k) * quarticCoreNuABCDEFG810 a b c d e f := by
  simp only [kappaQuarticInnerABCDEFG810, nuQuarticInnerABCDEFG810, quarticCoreNuABCDEFG810]
  ring

set_option maxHeartbeats 32000000 in
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

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABCDEFG810, degreeZeroKappaQuarticNoABCDEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt hBpos
  have hC1 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt hCpos
  have hD1 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt hDpos
  have hE1 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt hEpos
  have hF1 : 0 + 1 ≤ F.natDegree := Nat.succ_le_of_lt hFpos
  have hG1 : 0 + 1 ≤ G.natDegree := Nat.succ_le_of_lt hGpos
  simp only [degreeZeroKappaQuarticNoABCDEFG810]
  compute_degree
  omega

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
    omega
  have hcf_B2D : ((B ^ 2 * D)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BG : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    omega
  have hcf_BG : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_CF : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    omega
  have hcf_CF : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DE : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_B2D, hcf_BC2, hcf_BG, hcf_CF, hcf_DE]
  ring

set_option maxHeartbeats 16000000 in
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

set_option maxHeartbeats 16000000 in
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroMuQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceABCDEFG810, degreeZeroMuQuarticNoABCDEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt hBpos
  have hC1 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt hCpos
  have hD1 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt hDpos
  have hE1 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt hEpos
  have hF1 : 0 + 1 ≤ F.natDegree := Nat.succ_le_of_lt hFpos
  have hG1 : 0 + 1 ≤ G.natDegree := Nat.succ_le_of_lt hGpos
  simp only [degreeZeroMuQuarticNoABCDEFG810]
  compute_degree
  omega

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
    omega
  have hcf_ABF : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne hGne]
    omega
  have hcf_CG : ((C * G)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DF : ((D * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_ABF, hcf_AD2, hcf_B4, hcf_B2E, hcf_BCD, hcf_C3, hcf_CG, hcf_DF, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
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

set_option maxHeartbeats 32000000 in
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroNuQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceABCDEFG810, degreeZeroNuQuarticNoABCDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt hBpos
  have hC1 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt hCpos
  have hD1 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt hDpos
  have hE1 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt hEpos
  have hF1 : 0 + 1 ≤ F.natDegree := Nat.succ_le_of_lt hFpos
  have hG1 : 0 + 1 ≤ G.natDegree := Nat.succ_le_of_lt hGpos
  simp only [degreeZeroNuQuarticNoABCDEFG810]
  compute_degree
  omega

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
    omega
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABG : ((A * B * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    omega
  have hcf_ABG : ((A * B * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ACF : ((A * C * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
    omega
  have hcf_ACF : ((A * C * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ACF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ADE : ((A * D * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    omega
  have hcf_ADE : ((A * D * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ADE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2F : ((B ^ 2 * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hFne, natDegree_pow]
    omega
  have hcf_B2F : ((B ^ 2 * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DG : ((D * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hGne]
    omega
  have hcf_DG : ((D * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_DG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_EF : ((E * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A2B3, hcf_AB2D, hcf_ABC2, hcf_ABG, hcf_ACF, hcf_ADE, hcf_B3C, hcf_B2F, hcf_BCE, hcf_BD2, hcf_C2D, hcf_DG, hcf_EF]
  ring

set_option maxHeartbeats 16000000 in
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

set_option maxHeartbeats 32000000 in
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroXiQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceABCDEFG810, degreeZeroXiQuarticNoABCDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt hBpos
  have hC1 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt hCpos
  have hD1 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt hDpos
  have hE1 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt hEpos
  have hF1 : 0 + 1 ≤ F.natDegree := Nat.succ_le_of_lt hFpos
  have hG1 : 0 + 1 ≤ G.natDegree := Nat.succ_le_of_lt hGpos
  simp only [degreeZeroXiQuarticNoABCDEFG810]
  compute_degree
  omega

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
    omega
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCD : ((A * B * C * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCD : ((A * B * C * D)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_ABCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ADF : ((A * D * F)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    omega
  have hcf_ADF : ((A * D * F)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ADF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
    omega
  have hcf_B3D : ((B ^ 3 * D)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B2G : ((B ^ 2 * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne, natDegree_pow]
    omega
  have hcf_B2G : ((B ^ 2 * G)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_B2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCF : ((B * C * F)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hFne, natDegree_mul hBne hCne]
    omega
  have hcf_BCF : ((B * C * F)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BDE : ((B * D * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    omega
  have hcf_BDE : ((B * D * E)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EG : ((E * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hEne hGne]
    omega
  have hcf_EG : ((E * G)).coeff (A.natDegree + 4 * B.natDegree) =
      E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_EG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_F2 : (F ^ 2).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (A.natDegree + 4 * B.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB4, hcf_AB2E, hcf_ABCD, hcf_ADF, hcf_B3D, hcf_B2C2, hcf_B2G, hcf_BCF, hcf_BDE, hcf_C2E, hcf_CD2, hcf_EG, hcf_F2]
  ring

set_option maxHeartbeats 16000000 in
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

set_option maxHeartbeats 32000000 in
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroOmicronQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceABCDEFG810, degreeZeroOmicronQuarticNoABCDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt hBpos
  have hC1 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt hCpos
  have hD1 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt hDpos
  have hE1 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt hEpos
  have hF1 : 0 + 1 ≤ F.natDegree := Nat.succ_le_of_lt hFpos
  have hG1 : 0 + 1 ≤ G.natDegree := Nat.succ_le_of_lt hGpos
  simp only [degreeZeroOmicronQuarticNoABCDEFG810]
  compute_degree
  omega

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
    omega
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BC2 : ((A ^ 2 * B * C ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BC2 : ((A ^ 2 * B * C ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BG : ((A ^ 2 * B * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow]
    omega
  have hcf_A2BG : ((A ^ 2 * B * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2CF : ((A ^ 2 * C * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hCne, natDegree_pow]
    omega
  have hcf_A2CF : ((A ^ 2 * C * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A2CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2DE : ((A ^ 2 * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DE : ((A ^ 2 * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3C : ((A * B ^ 3 * C)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3C : ((A * B ^ 3 * C)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_AB3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2F : ((A * B ^ 2 * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hFne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2F : ((A * B ^ 2 * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_AB2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCE : ((A * B * C * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCE : ((A * B * C * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ABCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABD2 : ((A * B * D ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hDne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABD2 : ((A * B * D ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ABD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AC2D : ((A * C ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_AC2D : ((A * C ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ADG : ((A * D * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    omega
  have hcf_ADG : ((A * D * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ADG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AEF : ((A * E * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hEne) hFne, natDegree_mul hAne hEne]
    omega
  have hcf_AEF : ((A * E * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_AEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CD : ((B ^ 2 * C * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hDne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CD : ((B ^ 2 * C * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_B2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCG : ((B * C * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hGne, natDegree_mul hBne hCne]
    omega
  have hcf_BCG : ((B * C * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BCG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BDF : ((B * D * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hFne, natDegree_mul hBne hDne]
    omega
  have hcf_BDF : ((B * D * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BE2 : ((B * E ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_BE2 : ((B * E ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_BE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
    omega
  have hcf_C2F : ((C ^ 2 * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDE : ((C * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hEne, natDegree_mul hCne hDne]
    omega
  have hcf_CDE : ((C * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_CDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_FG : ((F * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hFne hGne]
    omega
  have hcf_FG : ((F * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_FG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A3B3, hcf_A2B2D, hcf_A2BC2, hcf_A2BG, hcf_A2CF, hcf_A2DE, hcf_AB3C, hcf_AB2F, hcf_ABCE, hcf_ABD2, hcf_AC2D, hcf_ADG, hcf_AEF, hcf_B5, hcf_B3E, hcf_B2CD, hcf_BC3, hcf_BCG, hcf_BDF, hcf_BE2, hcf_C2F, hcf_CDE, hcf_D3, hcf_FG]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceABCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoABCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroPiQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceABCDEFG810, degreeZeroPiQuarticNoABCDEFG810]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroPiQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroPiQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt hBpos
  have hC1 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt hCpos
  have hD1 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt hDpos
  have hE1 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt hEpos
  have hF1 : 0 + 1 ≤ F.natDegree := Nat.succ_le_of_lt hFpos
  have hG1 : 0 + 1 ≤ G.natDegree := Nat.succ_le_of_lt hGpos
  simp only [degreeZeroPiQuarticNoABCDEFG810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticFaceABCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceABCDEFG810 A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) =
      (1 / 4096 : k) * piQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  simp only [piQuarticFaceABCDEFG810, piQuarticInnerABCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B4 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B4 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hdeg_A2B4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB3D : ((A * B ^ 3 * D)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3D : ((A * B ^ 3 * D)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_AB3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2C2 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_AB2C2 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_AB2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2G : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2G : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_AB2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCF : ((A * B * C * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCF : ((A * B * C * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABDE : ((A * B * D * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne]
    omega
  have hcf_ABDE : ((A * B * D * E)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ABDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ACD2 : ((A * C * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne, natDegree_pow]
    omega
  have hcf_ACD2 : ((A * C * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ACD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AF2 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow]
    omega
  have hcf_AF2 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_AF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4C : ((B ^ 4 * C)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hCne, natDegree_pow]
    omega
  have hcf_B4C : ((B ^ 4 * C)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 4 * C.leadingCoeff := by
    rw [← hdeg_B4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3F : ((B ^ 3 * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hFne, natDegree_pow]
    omega
  have hcf_B3F : ((B ^ 3 * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * F.leadingCoeff := by
    rw [← hdeg_B3F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CE : ((B ^ 2 * C * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CE : ((B ^ 2 * C * E)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2CE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D2 : ((B ^ 2 * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hDne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2D2 : ((B ^ 2 * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff ^ 2 := by
    rw [← hdeg_B2D2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BC2D : ((B * C ^ 2 * D)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2D : ((B * C ^ 2 * D)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_BC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDG : ((B * D * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hGne, natDegree_mul hBne hDne]
    omega
  have hcf_BDG : ((B * D * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BEF : ((B * E * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hFne, natDegree_mul hBne hEne]
    omega
  have hcf_BEF : ((B * E * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C4 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDF : ((C * D * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hFne, natDegree_mul hCne hDne]
    omega
  have hcf_CDF : ((C * D * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CE2 : ((C * E ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_CE2 : ((C * E ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_CE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D2E : ((D ^ 2 * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hEne, natDegree_pow]
    omega
  have hcf_D2E : ((D ^ 2 * E)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      D.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_D2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_G2 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A2B4, hcf_AB3D, hcf_AB2C2, hcf_AB2G, hcf_ABCF, hcf_ABDE, hcf_ACD2, hcf_AF2, hcf_B4C, hcf_B3F, hcf_B2CE, hcf_B2D2, hcf_BC2D, hcf_BDG, hcf_BEF, hcf_C4, hcf_C2G, hcf_CDF, hcf_CE2, hcf_D2E, hcf_G2]
  ring

set_option maxHeartbeats 16000000 in
def primitiveQuarticFaceABCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  - (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveQuarticNoABCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * B * F)
  + (99 / 8192 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (9 / 4096 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (243 / 8192 * l : k) • (A * B ^ 3 * D)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)
  - (9 / 512 * l : k) • (A ^ 2 * D * F)
  + (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)
  + (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (9 / 256 * l : k) • (A * B * C * F)
  + (45 / 512 * l : k) • (A * B * D * E)
  + (9 / 1024 * l : k) • (A * C ^ 2 * E)
  + (9 / 256 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 64 * l : k) • (A * E * G)
  - (9 / 64 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2
  + (25 / 1048576 * beta : k) • A ^ 7
  + (21 / 32768 * beta : k) • (A ^ 5 * C)
  - (119 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 2048 * beta : k) • (A ^ 3 * B * D)
  + (21 / 4096 * beta : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 * beta : k) • (A * B ^ 4)
  + (21 / 512 * beta : k) • (A ^ 2 * C * E)
  - (7 / 512 * beta : k) • (A ^ 2 * D ^ 2)
  - (21 / 512 * beta : k) • (A * B ^ 2 * E)
  - (7 / 128 * beta : k) • (A * B * C * D)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)
  + (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2
  + (3 / 2048 * gamma : k) • (A ^ 3 * B * C)
  + (3 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 3 * F)
  + (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  + (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 128 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 128 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 32 * gamma : k) • (A * C * F)
  + (3 / 16 * gamma : k) • (A * D * E)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)
  + (25 / 262144 * delta : k) • A ^ 6
  + (35 / 16384 * delta : k) • (A ^ 4 * C)
  - (25 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (5 / 512 * delta : k) • (A ^ 2 * B * D)
  + (15 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (5 / 64 * delta : k) • (A * C * E)
  + (5 / 64 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2
  - (1 / 256 * epsilon : k) • (A ^ 3 * D)
  + (1 / 64 * epsilon : k) • (A ^ 2 * B * C)
  - (1 / 32 * epsilon : k) • (A * B ^ 3)
  - (1 / 32 * epsilon : k) • (A ^ 2 * F)
  + (1 / 8 * epsilon : k) • (A * B * E)
  + (1 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)
  + (3 / 8192 * zeta : k) • A ^ 5
  + (3 / 512 * zeta : k) • (A ^ 3 * C)
  - (3 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (3 / 32 * zeta : k) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2
  - (1 / 512 * eta : k) • (A ^ 3 * B)
  - (1 / 64 * eta : k) • (A ^ 2 * D)
  + (1 / 32 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3
  - (1 / 4 * eta : k) • (A * F)
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)
  + (5 / 4096 * theta : k) • A ^ 4
  + (3 / 128 * theta : k) • (A ^ 2 * C)
  + (1 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 8 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroPrimitiveQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810,
    rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810, primitiveQuarticFaceABCDEFG810, degreeZeroPrimitiveQuarticNoABCDEFG810]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroPrimitiveQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt hBpos
  have hC1 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt hCpos
  have hD1 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt hDpos
  have hE1 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt hEpos
  have hF1 : 0 + 1 ≤ F.natDegree := Nat.succ_le_of_lt hFpos
  have hG1 : 0 + 1 ≤ G.natDegree := Nat.succ_le_of_lt hGpos
  simp only [degreeZeroPrimitiveQuarticNoABCDEFG810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticFaceABCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (primitiveQuarticFaceABCDEFG810 A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * primitiveQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  simp only [primitiveQuarticFaceABCDEFG810, primitiveQuarticInnerABCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A4B3 : ((A ^ 4 * B ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A4B3 : ((A ^ 4 * B ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A4B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3B2D : ((A ^ 3 * B ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A3B2D : ((A ^ 3 * B ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A3B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BC2 : ((A ^ 3 * B * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A3BC2 : ((A ^ 3 * B * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A3BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BG : ((A ^ 3 * B * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow]
    omega
  have hcf_A3BG : ((A ^ 3 * B * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A3BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A3CF : ((A ^ 3 * C * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 3 hAne) hCne, natDegree_pow]
    omega
  have hcf_A3CF : ((A ^ 3 * C * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A3CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A3DE : ((A ^ 3 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 3 hAne) hDne, natDegree_pow]
    omega
  have hcf_A3DE : ((A ^ 3 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A3DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2B3C : ((A ^ 2 * B ^ 3 * C)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne)) hCne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B3C : ((A ^ 2 * B ^ 3 * C)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_A2B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2F : ((A ^ 2 * B ^ 2 * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hFne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2F : ((A ^ 2 * B ^ 2 * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_A2B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BCE : ((A ^ 2 * B * C * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hCne) hEne, natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hCne, natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow]
    omega
  have hcf_A2BCE : ((A ^ 2 * B * C * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2BD2 : ((A ^ 2 * B * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hDne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BD2 : ((A ^ 2 * B * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2C2D : ((A ^ 2 * C ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2C2D : ((A ^ 2 * C ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2DG : ((A ^ 2 * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DG : ((A ^ 2 * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2DG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2EF : ((A ^ 2 * E * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hEne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hEne, natDegree_pow]
    omega
  have hcf_A2EF : ((A ^ 2 * E * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A2EF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB5 : ((A * B ^ 5)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 5 hBne), natDegree_pow]
    omega
  have hcf_AB5 : ((A * B ^ 5)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 5 := by
    rw [← hdeg_AB5, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3E : ((A * B ^ 3 * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3E : ((A * B ^ 3 * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_AB3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2CD : ((A * B ^ 2 * C * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne) hDne, natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2CD : ((A * B ^ 2 * C * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_AB2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC3 : ((A * B * C ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 3 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC3 : ((A * B * C ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_ABC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCG : ((A * B * C * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hGne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCG : ((A * B * C * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABCG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABDF : ((A * B * D * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne]
    omega
  have hcf_ABDF : ((A * B * D * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABE2 : ((A * B * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hEne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABE2 : ((A * B * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_ABE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ACDE : ((A * C * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hCne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hCne) hDne, natDegree_mul hAne hCne]
    omega
  have hcf_ACDE : ((A * C * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ACDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AD3 : ((A * D ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hDne), natDegree_pow]
    omega
  have hcf_AD3 : ((A * D ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 3 := by
    rw [← hdeg_AD3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AFG : ((A * F * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hFne) hGne, natDegree_mul hAne hFne]
    omega
  have hcf_AFG : ((A * F * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_AFG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B4D : ((B ^ 4 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hDne, natDegree_pow]
    omega
  have hcf_B4D : ((B ^ 4 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 4 * D.leadingCoeff := by
    rw [← hdeg_B4D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C2 : ((B ^ 3 * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B3C2 : ((B ^ 3 * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B3C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B3G : ((B ^ 3 * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hGne, natDegree_pow]
    omega
  have hcf_B3G : ((B ^ 3 * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * G.leadingCoeff := by
    rw [← hdeg_B3G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CF : ((B ^ 2 * C * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CF : ((B ^ 2 * C * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_B2CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2DE : ((B ^ 2 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2DE : ((B ^ 2 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2E : ((B * C ^ 2 * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hEne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2E : ((B * C ^ 2 * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_BC2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD2 : ((B * C * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) (pow_ne_zero 2 hDne), natDegree_mul hBne hCne, natDegree_pow]
    omega
  have hcf_BCD2 : ((B * C * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BCD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BEG : ((B * E * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hGne, natDegree_mul hBne hEne]
    omega
  have hcf_BEG : ((B * E * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BEG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BF2 : ((B * F ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hFne), natDegree_pow]
    omega
  have hcf_BF2 : ((B * F ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_BF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3D : ((C ^ 3 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hCne) hDne, natDegree_pow]
    omega
  have hcf_C3D : ((C ^ 3 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_C3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDG : ((C * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hGne, natDegree_mul hCne hDne]
    omega
  have hcf_CDG : ((C * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CEF : ((C * E * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hEne) hFne, natDegree_mul hCne hEne]
    omega
  have hcf_CEF : ((C * E * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D2F : ((D ^ 2 * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hFne, natDegree_pow]
    omega
  have hcf_D2F : ((D ^ 2 * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_D2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE2 : ((D * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_DE2 : ((D * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_DE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A4B3, hcf_A3B2D, hcf_A3BC2, hcf_A3BG, hcf_A3CF, hcf_A3DE, hcf_A2B3C, hcf_A2B2F, hcf_A2BCE, hcf_A2BD2, hcf_A2C2D, hcf_A2DG, hcf_A2EF, hcf_AB5, hcf_AB3E, hcf_AB2CD, hcf_ABC3, hcf_ABCG, hcf_ABDF, hcf_ABE2, hcf_ACDE, hcf_AD3, hcf_AFG, hcf_B4D, hcf_B3C2, hcf_B3G, hcf_B2CF, hcf_B2DE, hcf_BC2E, hcf_BCD2, hcf_BEG, hcf_BF2, hcf_C3D, hcf_CDG, hcf_CEF, hcf_D2F, hcf_DE2]
  ring


/-! ## Inners and cores vanish on the cone -/

set_option maxHeartbeats 16000000 in
theorem quarticConeABCDEFG810_inners_eq_zero
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
    kappaQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      muQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      nuQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      xiQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      omicronQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      piQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      primitiveQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := primitiveQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroPrimitiveQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  exact ⟨hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner, hprimitiveinner⟩

set_option maxHeartbeats 16000000 in
theorem quarticConeABCDEFG810_cores_eq_zero
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
    quarticCoreMuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreNuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreXiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreOmicronABCDEFG810 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCorePiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCorePrimitiveABCDEFG810 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
  have hinners := quarticConeABCDEFG810_inners_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  rcases hinners with ⟨hk, hmu0, hnu0, hxi0, hom0, hpi0, hpr0⟩
  have hmucore : quarticCoreMuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_mu
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hmu0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (800 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hnucore : quarticCoreNuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_nu
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hnu0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (6400 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hxicore : quarticCoreXiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_xi
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hxi0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (1600 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have homicroncore : quarticCoreOmicronABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_omicron
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hom0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (2560 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hpicore : quarticCorePiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_pi
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hpi0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (256000 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hprimitivecore : quarticCorePrimitiveABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_primitive
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hpr0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (6400 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  exact ⟨hmucore, hnucore, hxicore, homicroncore, hpicore, hprimitivecore⟩


/-! ## a-resultants of the G-free cores, and the weight-26 factor T -/

def quarticCoreResA_mu_nuABCDEFG810 (b c d e f : k) : k :=
  (-14 : k) * b ^ 8 * d + 56 * b ^ 7 * c ^ 2 + (-320 : k) * b ^ 6 * c * f +
    96 * b ^ 6 * d * e + (-192 : k) * b ^ 5 * c ^ 2 * e +
    (-16 : k) * b ^ 5 * c * d ^ 2 + 384 * b ^ 5 * f ^ 2 +
    (-64 : k) * b ^ 4 * c ^ 3 * d + 1024 * b ^ 4 * c * e * f +
    (-64 : k) * b ^ 4 * d ^ 2 * f + (-128 : k) * b ^ 4 * d * e ^ 2 +
    384 * b ^ 3 * c * d ^ 2 * e + (-1024 : k) * b ^ 3 * e * f ^ 2 +
    1024 * b ^ 2 * c * d * f ^ 2 + 512 * b ^ 2 * d ^ 2 * e * f +
    512 * b * c * d ^ 3 * f + 512 * b * d ^ 4 * e

def quarticCoreResA_nu_xiABCDEFG810 (b c d e f : k) : k :=
  7 * b ^ 9 * c + (-12 : k) * b ^ 8 * f + (-52 : k) * b ^ 7 * c * e +
    10 * b ^ 7 * d ^ 2 + (-60 : k) * b ^ 6 * c ^ 2 * d + 80 * b ^ 6 * e * f +
    176 * b ^ 5 * c * d * f + 96 * b ^ 5 * c * e ^ 2 +
    (-32 : k) * b ^ 5 * d ^ 2 * e + 288 * b ^ 4 * c ^ 2 * d * e +
    (-48 : k) * b ^ 4 * c * d ^ 3 + (-128 : k) * b ^ 4 * d * f ^ 2 +
    (-128 : k) * b ^ 4 * e ^ 2 * f + (-768 : k) * b ^ 3 * c * d * e * f +
    384 * b ^ 2 * c ^ 2 * d ^ 2 * f + 384 * b ^ 2 * c * d ^ 3 * e +
    512 * b ^ 2 * d * e * f ^ 2 + (-512 : k) * b * c * d ^ 2 * f ^ 2 +
    (-512 : k) * b * d ^ 3 * e * f

def quarticCoreResA_nu_omicronABCDEFG810 (b c d e f : k) : k :=
  (-84 : k) * b ^ 12 * d ^ 2 + 280 * b ^ 11 * c ^ 2 * d +
    (-480 : k) * b ^ 10 * c * d * f + 640 * b ^ 10 * d ^ 2 * e +
    (-960 : k) * b ^ 9 * c ^ 2 * d * e + 320 * b ^ 9 * c * d ^ 3 +
    1280 * b ^ 8 * c * d * e * f + 1280 * b ^ 8 * d ^ 3 * f +
    (-1280 : k) * b ^ 8 * d ^ 2 * e ^ 2 + 1280 * b ^ 7 * c ^ 2 * d ^ 2 * f +
    1280 * b ^ 7 * c * d ^ 3 * e + (-640 : k) * b ^ 7 * d ^ 5 +
    (-5120 : k) * b ^ 6 * c * d ^ 2 * f ^ 2 +
    (-10240 : k) * b ^ 6 * d ^ 3 * e * f + 5120 * b ^ 5 * c * d ^ 4 * f +
    5120 * b ^ 5 * d ^ 5 * e

def quarticCoreT_ABCDEFG810 (b c d e f : k) : k :=
  7 * b ^ 6 * d + (-35 : k) * b ^ 5 * c ^ 2 + 340 * b ^ 4 * c * f +
    (-40 : k) * b ^ 4 * d * e + 120 * b ^ 3 * c ^ 2 * e +
    60 * b ^ 3 * c * d ^ 2 + (-480 : k) * b ^ 3 * f ^ 2 +
    80 * b ^ 2 * c ^ 3 * d + (-1120 : k) * b ^ 2 * c * e * f +
    240 * b ^ 2 * d ^ 2 * f + 160 * b * c ^ 2 * d * f +
    (-320 : k) * b * c * d ^ 2 * e + (-80 : k) * b * d ^ 4 +
    1280 * b * e * f ^ 2 + (-1920 : k) * c * d * f ^ 2 +
    (-1920 : k) * d ^ 2 * e * f

set_option maxHeartbeats 32000000 in
theorem quarticCore_resA_mu_nu
    (a b c d e f : k) :
    (8 * b ^ 3 * c + (-32 : k) * b ^ 2 * f + (-16 : k) * b * d ^ 2) *
        quarticCoreNuABCDEFG810 a b c d e f -
      (2 * b ^ 3 * d) * quarticCoreMuABCDEFG810 a b c d e f =
      quarticCoreResA_mu_nuABCDEFG810 b c d e f := by
  simp only [quarticCoreMuABCDEFG810, quarticCoreNuABCDEFG810,
    quarticCoreResA_mu_nuABCDEFG810]
  ring

set_option maxHeartbeats 32000000 in
theorem quarticCore_resA_nu_xi
    (a b c d e f : k) :
    (2 * b ^ 3 * d) * quarticCoreXiABCDEFG810 a b c d e f -
      ((-1 : k) * b ^ 5 + 4 * b ^ 3 * e + 12 * b ^ 2 * c * d +
          (-16 : k) * b * d * f) *
        quarticCoreNuABCDEFG810 a b c d e f =
      quarticCoreResA_nu_xiABCDEFG810 b c d e f := by
  simp only [quarticCoreNuABCDEFG810, quarticCoreXiABCDEFG810,
    quarticCoreResA_nu_xiABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCore_resA_nu_omicron
    (a b c d e f : k) :
    (4 * b ^ 6 * d ^ 2) * quarticCoreOmicronABCDEFG810 a b c d e f -
      ((-20 : k) * a * b ^ 6 * d ^ 2 + (-40 : k) * b ^ 7 * c * d +
          160 * b ^ 5 * d ^ 3) *
        quarticCoreNuABCDEFG810 a b c d e f =
      quarticCoreResA_nu_omicronABCDEFG810 b c d e f := by
  simp only [quarticCoreNuABCDEFG810, quarticCoreOmicronABCDEFG810,
    quarticCoreResA_nu_omicronABCDEFG810]
  ring

set_option maxHeartbeats 32000000 in
theorem quarticCore_T_of_resA
    (b c d e f : k) :
    quarticCoreResA_nu_omicronABCDEFG810 b c d e f -
      (10 * b ^ 4 * d) * quarticCoreResA_mu_nuABCDEFG810 b c d e f =
      (8 * b ^ 6 * d) * quarticCoreT_ABCDEFG810 b c d e f := by
  simp only [quarticCoreResA_nu_omicronABCDEFG810,
    quarticCoreResA_mu_nuABCDEFG810, quarticCoreT_ABCDEFG810]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticConeABCDEFG810_afree_eq_zero
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
    quarticCoreResA_mu_nuABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResA_nu_xiABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResA_nu_omicronABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreT_ABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
  have hcores := quarticConeABCDEFG810_cores_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  rcases hcores with ⟨hcmu, hcnu, hcxi, hcom, hcpi, hcpr⟩
  have hBne : B.leadingCoeff ≠ 0 := by
    intro h0
    have : B = 0 := leadingCoeff_eq_zero.mp h0
    have : B.natDegree = 0 := by simp [this]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hDne : D.leadingCoeff ≠ 0 := by
    intro h0
    have : D = 0 := leadingCoeff_eq_zero.mp h0
    have : D.natDegree = 0 := by simp [this]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hmn : quarticCoreResA_mu_nuABCDEFG810 B.leadingCoeff C.leadingCoeff
      D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resA_mu_nu A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hcmu, hcnu] at hid
    simp only [mul_zero, sub_zero] at hid
    exact hid.symm
  have hnx : quarticCoreResA_nu_xiABCDEFG810 B.leadingCoeff C.leadingCoeff
      D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resA_nu_xi A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hcnu, hcxi] at hid
    simp only [mul_zero, sub_zero] at hid
    exact hid.symm
  have hno : quarticCoreResA_nu_omicronABCDEFG810 B.leadingCoeff
      C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resA_nu_omicron A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hcnu, hcom] at hid
    simp only [mul_zero, sub_zero] at hid
    exact hid.symm
  have hT : quarticCoreT_ABCDEFG810 B.leadingCoeff C.leadingCoeff
      D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_T_of_resA B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hmn, hno] at hid
    simp only [mul_zero, sub_zero] at hid
    have h8 : (8 : k) ≠ 0 := by norm_num
    have hpowB : B.leadingCoeff ^ 6 ≠ 0 := pow_ne_zero 6 hBne
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · have hmul2 := mul_eq_zero.mp h
      rcases hmul2 with h' | h'
      · have hmul3 := mul_eq_zero.mp h'
        rcases hmul3 with h8' | hB6
        · exact (h8 h8').elim
        · exact (hpowB hB6).elim
      · exact (hDne h').elim
    · exact h
  exact ⟨hmn, hnx, hno, hT⟩


/-! ## Residual: Groebner `(1)` not transcribed -/

set_option maxHeartbeats 16000000 in
theorem quarticConeABCDEFG810_residual
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
    kappaQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      muQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      nuQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      xiQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      omicronQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      piQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      primitiveQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      quarticCoreMuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreNuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreXiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreOmicronABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCorePiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCorePrimitiveABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResA_mu_nuABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResA_nu_xiABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResA_nu_omicronABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreT_ABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
  have hinners := quarticConeABCDEFG810_inners_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  have hcores := quarticConeABCDEFG810_cores_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  have hafree := quarticConeABCDEFG810_afree_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  rcases hinners with ⟨hk, hmu0, hnu0, hxi0, hom0, hpi0, hpr0⟩
  rcases hcores with ⟨hcmu, hcnu, hcxi, hcom, hcpi, hcpr⟩
  rcases hafree with ⟨hmn, hnx, hno, hT⟩
  exact ⟨hk, hmu0, hnu0, hxi0, hom0, hpi0, hpr0, hcmu, hcnu, hcxi, hcom, hcpi, hcpr, hmn, hnx, hno, hT⟩

#print axioms quarticConeABCDEFG810_residual
#print axioms quarticConeABCDEFG810_inners_eq_zero
#print axioms quarticConeABCDEFG810_cores_eq_zero
#print axioms quarticConeABCDEFG810_afree_eq_zero
#print axioms quarticCore_resA_mu_nu
#print axioms quarticCore_resA_nu_xi
#print axioms quarticCore_resA_nu_omicron
#print axioms quarticCore_T_of_resA


end QuarticFullConeABCDEFG810

end Max11DegreeRoutes
