import Grok810ScaleZeroQuarticFullConeScratch

/-! # Kill the 7-letter cone `R = {A,B,C,D,E,F,G}` of normalized `(8,10)`, `H = 0`

Continuation of `Grok810ScaleZeroQuarticFullConeScratch`.  That file lands
`quarticConeABCDEFG810_residual`: on this cone the seven load-free inners
vanish in the leading coefficients, the six G-free cores vanish, the
a-resultants `R_{μν} = R_{νξ} = R_{νο} = 0`, and the weight-26 factor
`T = 0` (linear in `e`).

This file records the next elimination layer: `T = T₁ e + T₀`, and the
e-resultants `Res_e(T, R_{μν})` and `Res_e(T, R_{νξ})` vanish on the cone.

CAS (Singular, `Dp` on `k[a,b,c,d,e,f,g]`): the ideal of the seven inners
together with `T` contains the monomials `d^5 f^2`, `f^7`, `g^7` and
`b^25`.  Explicit `lift` identities were checked (`sum =` the monomial):

* `d^5 f^2`: cofactor sizes `231, 138, 166, 110, 113, 80, 74, 22`
  (~1500-digit rationals);
* `f^7`: sizes `463, 263, 334, 229, 223, 153, 148, 46` (~3800-digit);
* `g^7`: sizes `899, 567, 668, 491, 457, 349, 315, 110` (~12000-digit);
* `b^25`: sizes `3992, 2199, 2933, 1720, 1942, 1300, 1281, 390`.

At `b = 1` the same ideal is `(1)`, with `Dp` cofactors of `1` sized
`563, 216, 360, 205, 237, 78, 133, 114` (~150-digit rationals).  Those
coefficients are too large to transcribe into Lean `ring`.  Cube-root
scaling `b ↦ 1` is not available over an arbitrary `CharZero` field, so
the remaining named relation is the untranscribed membership
`d^5 f^2 ∈ ⟨inners, T⟩`.

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
set_option maxHeartbeats 64000000

section QuarticFullConeABCDEFG810Kill

variable {k : Type*} [Field k] [CharZero k]


/-! ## `T` is linear in `e` -/

def quarticCoreT0_ABCDEFG810 (b c d f : k) : k :=
  7 * b ^ 6 * d + (-35 : k) * b ^ 5 * c ^ 2 + 340 * b ^ 4 * c * f +
    60 * b ^ 3 * c * d ^ 2 + (-480 : k) * b ^ 3 * f ^ 2 +
    80 * b ^ 2 * c ^ 3 * d + 240 * b ^ 2 * d ^ 2 * f +
    160 * b * c ^ 2 * d * f + (-80 : k) * b * d ^ 4 +
    (-1920 : k) * c * d * f ^ 2

def quarticCoreT1_ABCDEFG810 (b c d f : k) : k :=
  (-40 : k) * b ^ 4 * d + 120 * b ^ 3 * c ^ 2 + (-1120 : k) * b ^ 2 * c * f +
    (-320 : k) * b * c * d ^ 2 + 1280 * b * f ^ 2 + (-1920 : k) * d ^ 2 * f

set_option maxHeartbeats 16000000 in
theorem quarticCoreT_linear_e
    (b c d e f : k) :
    quarticCoreT_ABCDEFG810 b c d e f =
      quarticCoreT1_ABCDEFG810 b c d f * e +
        quarticCoreT0_ABCDEFG810 b c d f := by
  simp only [quarticCoreT_ABCDEFG810, quarticCoreT0_ABCDEFG810,
    quarticCoreT1_ABCDEFG810]
  ring


/-! ## e-resultants of `T` against the a-resultants `R_{μν}` and `R_{νξ}` -/

def quarticCoreResE_T_mu_nuABCDEFG810 (b c d e f : k) : k :=
  (-1792 : k) * b ^ 16 * d ^ 3 + 17920 * b ^ 15 * c ^ 2 * d ^ 2 + (-62720 : k) * b ^ 14 * c ^ 4 * d
  + (-30720 : k) * b ^ 14 * c * d ^ 2 * f + 808960 * b ^ 13 * c ^ 3 * d * f + 61440 * b ^ 13 * c * d ^ 4
  + (-81920 : k) * b ^ 13 * d ^ 2 * f ^ 2 + (-256000 : k) * b ^ 12 * c ^ 3 * d ^ 3 + (-3010560 : k) * b ^ 12 * c ^ 2 * d * f ^ 2
  + (-327680 : k) * b ^ 12 * d ^ 4 * f + 409600 * b ^ 11 * c ^ 5 * d ^ 2 + 8355840 * b ^ 11 * c ^ 2 * d ^ 3 * f
  + 4915200 * b ^ 11 * c * d * f ^ 3 + (-20480 : k) * b ^ 11 * d ^ 6 + 921600 * b ^ 10 * c ^ 7 * d
  + (-22937600 : k) * b ^ 10 * c ^ 4 * d ^ 2 * f + 993280 * b ^ 10 * c ^ 2 * d ^ 5 + (-22609920 : k) * b ^ 10 * c * d ^ 3 * f ^ 2
  + (-3932160 : k) * b ^ 10 * d * f ^ 4 + (-6144000 : k) * b ^ 9 * c ^ 6 * d * f + (-2662400 : k) * b ^ 9 * c ^ 4 * d ^ 4
  + 211353600 * b ^ 9 * c ^ 3 * d ^ 2 * f ^ 2 + 11550720 * b ^ 9 * c * d ^ 5 * f + 7864320 * b ^ 9 * d ^ 3 * f ^ 3
  + (-4505600 : k) * b ^ 8 * c ^ 6 * d ^ 3 + (-62259200 : k) * b ^ 8 * c ^ 5 * d * f ^ 2 + 28672000 * b ^ 8 * c ^ 3 * d ^ 4 * f
  + (-642252800 : k) * b ^ 8 * c ^ 2 * d ^ 2 * f ^ 3 + (-81920 : k) * b ^ 8 * c * d ^ 7 + (-23920640 : k) * b ^ 8 * d ^ 5 * f ^ 2
  + (-3276800 : k) * b ^ 7 * c ^ 5 * d ^ 3 * f + 602931200 * b ^ 7 * c ^ 4 * d * f ^ 3 + 8192000 * b ^ 7 * c ^ 3 * d ^ 6
  + 337510400 * b ^ 7 * c ^ 2 * d ^ 4 * f ^ 2 + 812646400 * b ^ 7 * c * d ^ 2 * f ^ 4 + 327680 * b ^ 7 * d ^ 7 * f
  + (-1638400 : k) * b ^ 6 * c ^ 5 * d ^ 5 + (-6553600 : k) * b ^ 6 * c ^ 4 * d ^ 3 * f ^ 2 + (-1703936000 : k) * b ^ 6 * c ^ 3 * d * f ^ 4
  + 91750400 * b ^ 6 * c ^ 2 * d ^ 6 * f + (-1166540800 : k) * b ^ 6 * c * d ^ 4 * f ^ 3 + (-2457600 : k) * b ^ 6 * d ^ 9
  + (-419430400 : k) * b ^ 6 * d ^ 2 * f ^ 5 + 9830400 * b ^ 5 * c ^ 4 * d ^ 5 * f + 891289600 * b ^ 5 * c ^ 3 * d ^ 3 * f ^ 3
  + 4915200 * b ^ 5 * c ^ 2 * d ^ 8 + 1992294400 * b ^ 5 * c ^ 2 * d * f ^ 5 + 353894400 * b ^ 5 * c * d ^ 6 * f ^ 2
  + 838860800 * b ^ 5 * d ^ 4 * f ^ 4 + 13107200 * b ^ 4 * c ^ 4 * d ^ 7 + 144179200 * b ^ 4 * c ^ 3 * d ^ 5 * f ^ 2
  + (-2097152000 : k) * b ^ 4 * c ^ 2 * d ^ 3 * f ^ 4 + (-19660800 : k) * b ^ 4 * c * d ^ 8 * f + (-838860800 : k) * b ^ 4 * c * d * f ^ 6
  + (-419430400 : k) * b ^ 4 * d ^ 6 * f ^ 3 + 157286400 * b ^ 3 * c ^ 3 * d ^ 7 * f + 262144000 * b ^ 3 * c ^ 2 * d ^ 5 * f ^ 3
  + (-13107200 : k) * b ^ 3 * c * d ^ 10 + 838860800 * b ^ 3 * c * d ^ 3 * f ^ 5 + 209715200 * b ^ 3 * d ^ 8 * f ^ 2
  + 471859200 * b ^ 2 * c ^ 2 * d ^ 7 * f ^ 2 + 629145600 * b ^ 2 * c * d ^ 5 * f ^ 4 + (-78643200 : k) * b ^ 2 * d ^ 10 * f

def quarticCoreResE_T_mu_nu_cof (b c d e f : k) : k :=
  (-2944 : k) * b ^ 10 * d ^ 2 + 14720 * b ^ 9 * c ^ 2 * d + (-23040 : k) * b ^ 8 * c ^ 4
  + (-104960 : k) * b ^ 8 * c * d * f + 5120 * b ^ 8 * d ^ 2 * e + 337920 * b ^ 7 * c ^ 3 * f
  + (-15360 : k) * b ^ 7 * c ^ 2 * d * e + (-38400 : k) * b ^ 7 * c * d ^ 3 + 102400 * b ^ 7 * d * f ^ 2
  + 117760 * b ^ 6 * c ^ 3 * d ^ 2 + (-1515520 : k) * b ^ 6 * c ^ 2 * f ^ 2 + 143360 * b ^ 6 * c * d * e * f
  + (-174080 : k) * b ^ 6 * d ^ 3 * f + (-307200 : k) * b ^ 5 * c ^ 2 * d ^ 2 * f + 40960 * b ^ 5 * c * d ^ 3 * e
  + 2457600 * b ^ 5 * c * f ^ 3 + (-30720 : k) * b ^ 5 * d ^ 5 + (-163840 : k) * b ^ 5 * d * e * f ^ 2
  + (-61440 : k) * b ^ 4 * c ^ 2 * d ^ 4 + (-1966080 : k) * b ^ 4 * c * d ^ 2 * f ^ 2 + 245760 * b ^ 4 * d ^ 3 * e * f
  + (-1310720 : k) * b ^ 4 * f ^ 4 + (-1474560 : k) * b ^ 3 * c * d ^ 4 * f + 2621440 * b ^ 3 * d ^ 2 * f ^ 3
  + (-163840 : k) * b ^ 2 * c * d ^ 6 + (-327680 : k) * b ^ 2 * d ^ 4 * f ^ 2 + (-983040 : k) * b * d ^ 6 * f

def quarticCoreResE_T_nu_xiABCDEFG810 (b c d e f : k) : k :=
  1344 * b ^ 17 * c * d ^ 2 + 2240 * b ^ 16 * c ^ 3 * d + (-3072 : k) * b ^ 16 * d ^ 2 * f
  + (-32000 : k) * b ^ 15 * c ^ 2 * d * f + 7040 * b ^ 15 * d ^ 4 + (-21120 : k) * b ^ 14 * c ^ 2 * d ^ 3
  + 133120 * b ^ 14 * c * d * f ^ 2 + (-102400 : k) * b ^ 13 * c ^ 4 * d ^ 2 + 432640 * b ^ 13 * c * d ^ 3 * f
  + (-163840 : k) * b ^ 13 * d * f ^ 3 + 307200 * b ^ 12 * c ^ 6 * d + 619520 * b ^ 12 * c ^ 3 * d ^ 2 * f
  + 197120 * b ^ 12 * c * d ^ 5 + (-614400 : k) * b ^ 12 * d ^ 3 * f ^ 2 + (-7168000 : k) * b ^ 11 * c ^ 5 * d * f
  + (-778240 : k) * b ^ 11 * c ^ 3 * d ^ 4 + (-1966080 : k) * b ^ 11 * c ^ 2 * d ^ 2 * f ^ 2 + 542720 * b ^ 11 * d ^ 5 * f
  + 1049600 * b ^ 10 * c ^ 5 * d ^ 3 + 60006400 * b ^ 10 * c ^ 4 * d * f ^ 2 + 4567040 * b ^ 10 * c ^ 2 * d ^ 4 * f
  + 10240000 * b ^ 10 * c * d ^ 2 * f ^ 3 + 102400 * b ^ 10 * d ^ 7 + (-2150400 : k) * b ^ 9 * c ^ 7 * d ^ 2
  + (-22528000 : k) * b ^ 9 * c ^ 4 * d ^ 3 * f + (-225280000 : k) * b ^ 9 * c ^ 3 * d * f ^ 3 + 143360 * b ^ 9 * c ^ 2 * d ^ 6
  + 12042240 * b ^ 9 * c * d ^ 4 * f ^ 2 + (-14417920 : k) * b ^ 9 * d ^ 2 * f ^ 4 + 34816000 * b ^ 8 * c ^ 6 * d ^ 2 * f
  + (-2048000 : k) * b ^ 8 * c ^ 4 * d ^ 5 + 140083200 * b ^ 8 * c ^ 3 * d ^ 3 * f ^ 2 + 416153600 * b ^ 8 * c ^ 2 * d * f ^ 4
  + 14049280 * b ^ 8 * c * d ^ 6 * f + (-19660800 : k) * b ^ 8 * d ^ 4 * f ^ 3 + 3686400 * b ^ 7 * c ^ 6 * d ^ 4
  + (-111411200 : k) * b ^ 7 * c ^ 5 * d ^ 2 * f ^ 2 + (-17203200 : k) * b ^ 7 * c ^ 3 * d ^ 5 * f + (-301465600 : k) * b ^ 7 * c ^ 2 * d ^ 3 * f ^ 3
  + 204800 * b ^ 7 * c * d ^ 8 + (-353894400 : k) * b ^ 7 * c * d * f ^ 5 + (-1966080 : k) * b ^ 7 * d ^ 6 * f ^ 2
  + 41779200 * b ^ 6 * c ^ 5 * d ^ 4 * f + (-163840000 : k) * b ^ 6 * c ^ 4 * d ^ 2 * f ^ 3 + (-1228800 : k) * b ^ 6 * c ^ 3 * d ^ 7
  + 193331200 * b ^ 6 * c ^ 2 * d ^ 5 * f ^ 2 + 399769600 * b ^ 6 * c * d ^ 3 * f ^ 4 + 5734400 * b ^ 6 * d ^ 8 * f
  + 104857600 * b ^ 6 * d * f ^ 6 + 9830400 * b ^ 5 * c ^ 5 * d ^ 6 + (-13107200 : k) * b ^ 5 * c ^ 4 * d ^ 4 * f ^ 2
  + 1205862400 * b ^ 5 * c ^ 3 * d ^ 2 * f ^ 4 + (-58982400 : k) * b ^ 5 * c ^ 2 * d ^ 7 * f + (-439091200 : k) * b ^ 5 * c * d ^ 5 * f ^ 3
  + (-314572800 : k) * b ^ 5 * d ^ 3 * f ^ 5 + 104857600 * b ^ 4 * c ^ 4 * d ^ 6 * f + (-576716800 : k) * b ^ 4 * c ^ 3 * d ^ 4 * f ^ 3
  + (-9830400 : k) * b ^ 4 * c ^ 2 * d ^ 9 + (-1468006400 : k) * b ^ 4 * c ^ 2 * d ^ 2 * f ^ 5 + 91750400 * b ^ 4 * c * d ^ 7 * f ^ 2
  + 445644800 * b ^ 4 * d ^ 5 * f ^ 4 + 196608000 * b ^ 3 * c ^ 3 * d ^ 6 * f ^ 2 + 1153433600 * b ^ 3 * c ^ 2 * d ^ 4 * f ^ 4
  + (-45875200 : k) * b ^ 3 * c * d ^ 9 * f + 419430400 * b ^ 3 * c * d ^ 2 * f ^ 6 + (-367001600 : k) * b ^ 3 * d ^ 7 * f ^ 3
  + (-471859200 : k) * b ^ 2 * c ^ 2 * d ^ 6 * f ^ 3 + (-629145600 : k) * b ^ 2 * c * d ^ 4 * f ^ 5 + 78643200 * b ^ 2 * d ^ 9 * f ^ 2

def quarticCoreResE_T_nu_xi_cof (b c d e f : k) : k :=
  1408 * b ^ 11 * c * d + (-2880 : k) * b ^ 10 * c ^ 3 + (-2304 : k) * b ^ 10 * d * f
  + 30720 * b ^ 9 * c ^ 2 * f + (-3840 : k) * b ^ 9 * c * d * e + 1280 * b ^ 9 * d ^ 3
  + 11520 * b ^ 8 * c ^ 3 * e + (-4480 : k) * b ^ 8 * c ^ 2 * d ^ 2 + (-66560 : k) * b ^ 8 * c * f ^ 2
  + 5120 * b ^ 8 * d * e * f + 26880 * b ^ 7 * c ^ 4 * d + (-122880 : k) * b ^ 7 * c ^ 2 * e * f
  + 125440 * b ^ 7 * c * d ^ 2 * f + 40960 * b ^ 7 * f ^ 3 + (-419840 : k) * b ^ 6 * c ^ 3 * d * f
  + (-30720 : k) * b ^ 6 * c ^ 2 * d ^ 2 * e + 2560 * b ^ 6 * c * d ^ 4 + 266240 * b ^ 6 * c * e * f ^ 2
  + (-184320 : k) * b ^ 6 * d ^ 2 * f ^ 2 + (-46080 : k) * b ^ 5 * c ^ 3 * d ^ 3 + 1495040 * b ^ 5 * c ^ 2 * d * f ^ 2
  + (-143360 : k) * b ^ 5 * c * d ^ 2 * e * f + 71680 * b ^ 5 * d ^ 4 * f + (-163840 : k) * b ^ 5 * e * f ^ 3
  + (-798720 : k) * b ^ 4 * c ^ 2 * d ^ 3 * f + (-1802240 : k) * b ^ 4 * c * d * f ^ 3 + 245760 * b ^ 4 * d ^ 2 * e * f ^ 2
  + (-122880 : k) * b ^ 3 * c ^ 2 * d ^ 5 + 2375680 * b ^ 3 * c * d ^ 3 * f ^ 2 + 655360 * b ^ 3 * d * f ^ 4
  + (-573440 : k) * b ^ 2 * c * d ^ 5 * f + (-1638400 : k) * b ^ 2 * d ^ 3 * f ^ 3 + 983040 * b * d ^ 5 * f ^ 2

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_T_mu_nu
    (b c d e f : k) :
    quarticCoreT1_ABCDEFG810 b c d f ^ 2 *
        quarticCoreResA_mu_nuABCDEFG810 b c d e f -
      quarticCoreResE_T_mu_nu_cof b c d e f *
        quarticCoreT_ABCDEFG810 b c d e f =
      quarticCoreResE_T_mu_nuABCDEFG810 b c d e f := by
  simp only [quarticCoreT1_ABCDEFG810, quarticCoreResA_mu_nuABCDEFG810,
    quarticCoreResE_T_mu_nu_cof, quarticCoreT_ABCDEFG810,
    quarticCoreResE_T_mu_nuABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCore_resE_T_nu_xi
    (b c d e f : k) :
    quarticCoreT1_ABCDEFG810 b c d f ^ 2 *
        quarticCoreResA_nu_xiABCDEFG810 b c d e f -
      quarticCoreResE_T_nu_xi_cof b c d e f *
        quarticCoreT_ABCDEFG810 b c d e f =
      quarticCoreResE_T_nu_xiABCDEFG810 b c d e f := by
  simp only [quarticCoreT1_ABCDEFG810, quarticCoreResA_nu_xiABCDEFG810,
    quarticCoreResE_T_nu_xi_cof, quarticCoreT_ABCDEFG810,
    quarticCoreResE_T_nu_xiABCDEFG810]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticConeABCDEFG810_resE_eq_zero
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
    quarticCoreResE_T_mu_nuABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResE_T_nu_xiABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
  have hafree := quarticConeABCDEFG810_afree_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  rcases hafree with ⟨hmn, hnx, hno, hT⟩
  have hmnE : quarticCoreResE_T_mu_nuABCDEFG810 B.leadingCoeff C.leadingCoeff
      D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resE_T_mu_nu B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hmn, hT] at hid
    simp only [mul_zero, sub_zero] at hid
    exact hid.symm
  have hnxE : quarticCoreResE_T_nu_xiABCDEFG810 B.leadingCoeff C.leadingCoeff
      D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resE_T_nu_xi B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hnx, hT] at hid
    simp only [mul_zero, sub_zero] at hid
    exact hid.symm
  exact ⟨hmnE, hnxE⟩


/-! ## Residual: membership `d^5 f^2 ∈ ⟨inners, T⟩` not transcribed

CAS (Singular, `Dp`): `lift` of `d^5 * f^2` against the seven inners and
`T` succeeds and checks (`sum = d^5 f^2`), cofactor sizes
`231, 138, 166, 110, 113, 80, 74, 22`, coefficients ~1500-digit
rationals.  The same ideal contains `f^7`, `g^7` and `b^25`.  Those
cofactors are too large for Lean `ring` / `linear_combination`.  On the
cone `D.leadingCoeff ≠ 0` and `F.leadingCoeff ≠ 0`, so a transcribed
copy of the `d^5 f^2` identity would finish the branch.
-/

set_option maxHeartbeats 16000000 in
theorem quarticConeABCDEFG810_residual2
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
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreT_ABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff =
        quarticCoreT1_ABCDEFG810 B.leadingCoeff C.leadingCoeff
          D.leadingCoeff F.leadingCoeff *
          E.leadingCoeff +
          quarticCoreT0_ABCDEFG810 B.leadingCoeff C.leadingCoeff
            D.leadingCoeff F.leadingCoeff ∧
      quarticCoreResE_T_mu_nuABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResE_T_nu_xiABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
  have hres := quarticConeABCDEFG810_residual (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  have hE := quarticConeABCDEFG810_resE_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  have hlin := quarticCoreT_linear_e B.leadingCoeff C.leadingCoeff
      D.leadingCoeff E.leadingCoeff F.leadingCoeff
  rcases hres with ⟨hk, hmu0, hnu0, hxi0, hom0, hpi0, hpr0, hcmu, hcnu, hcxi, hcom, hcpi, hcpr, hmn, hnx, hno, hT⟩
  rcases hE with ⟨hmnE, hnxE⟩
  exact ⟨hk, hmu0, hnu0, hxi0, hom0, hpi0, hpr0, hcmu, hcnu, hcxi, hcom, hcpi, hcpr, hmn, hnx, hno, hT, hlin, hmnE, hnxE⟩

#print axioms quarticConeABCDEFG810_residual2
#print axioms quarticConeABCDEFG810_resE_eq_zero
#print axioms quarticCoreT_linear_e
#print axioms quarticCore_resE_T_mu_nu
#print axioms quarticCore_resE_T_nu_xi

end QuarticFullConeABCDEFG810Kill

end Max11DegreeRoutes
