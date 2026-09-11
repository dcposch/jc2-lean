import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart02Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart101Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart10Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart101Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart102Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextLambdaSpeedPart03Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart19Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- On the globally merged deeper jet the cleared `λ` defect factors
exactly as `h⁵⁴` times its order-`54` head plus `h` times the deep
tail. -/
theorem bridgeClearedLambdaDefect610_deepJet_factored
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedLambdaDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        (h ^ 3 * q53) (h * q41) q3 q2 q1 lambda =
      h ^ 54 *
        (bridgeLambdaDeepHead610 a41 s1 b62 p2 q41 +
          h * bridgeLambdaDeepTail610 h w1 a41 p32 s1 u2 b62 q53 p2 p1
            p0 q41 q3 q2 q1 (Polynomial.C lambda)) := by
  unfold bridgeClearedLambdaDefect610 bridgeLambdaDeepHead610 bridgeLambdaDeepTail610
  ring

end BridgeLambdaJetFactor610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the order-`52` head. -/
theorem bridgeLambdaJetHead610_eval
    (p31 u1 q4 : k[X]) (x : k) :
    (bridgeLambdaJetHead610 p31 u1 q4).eval x =
      bridgeLambdaJetHead610 (p31.eval x) (u1.eval x) (q4.eval x) := by
  simp only [bridgeLambdaJetHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

end BridgeLambdaJetFactor610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the order-`54` head. -/
theorem bridgeLambdaDeepHead610_eval
    (a41 s1 b62 p2 q41 : k[X]) (x : k) :
    (bridgeLambdaDeepHead610 a41 s1 b62 p2 q41).eval x =
      bridgeLambdaDeepHead610 (a41.eval x) (s1.eval x) (b62.eval x)
        (p2.eval x) (q41.eval x) := by
  simp only [bridgeLambdaDeepHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

end BridgeLambdaJetFactor610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free kill: modulo the tenth-face root laws alone the
vanishing order-`52` head forces `7971615 p₃₁⁴ = 0`, hence
`p₃₁ = 0`. -/
theorem bridgeLambda_chamberFree_kill610
    (p31 u1 q4 : F)
    (hhead : bridgeLambdaJetHead610 p31 u1 q4 = 0)
    (hu : (3 : F) * u1 = (5 : F) * p31)
    (hq4 : (9 : F) * q4 = (5 : F) * p31 ^ 2) :
    p31 = 0 := by
  simp only [bridgeLambdaJetHead610] at hhead
  have h4 : p31 ^ 4 = 0 := by
    linear_combination (1 / 7971615 : F) * hhead -
      (7 / 3 : F) * p31 ^ 3 * hu + (4 / 5 : F) * p31 ^ 2 * hq4
  by_contra hne
  exact pow_ne_zero 4 hne h4

end BridgeLambdaScalars610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free reduction of the vanishing order-`54` head modulo
`3 s₁ = 5 a₄₁` and the `p₃₁`-killed `U`-load alone. -/
theorem bridgeLambda_deepReduction610
    (a41 s1 b62 p2 q41 : F)
    (hhead : bridgeLambdaDeepHead610 a41 s1 b62 p2 q41 = 0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hU : (10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2 = 0) :
    (100 : F) * a41 ^ 6 - (1575 : F) * a41 ^ 4 * p2 +
        (810 : F) * a41 ^ 3 * q41 + (4860 : F) * a41 ^ 2 * p2 ^ 2 -
      (2916 : F) * a41 * p2 * q41 - (1620 : F) * p2 ^ 3 = 0 := by
  simp only [bridgeLambdaDeepHead610] at hhead
  linear_combination (1 / 39366 : F) * hhead -
    (12 : F) * a41 * ((22 : F) * a41 ^ 4 - (120 : F) * a41 ^ 2 * p2 +
      (135 : F) * p2 ^ 2) * hs -
    (9 / 2 : F) * ((10 : F) * a41 ^ 4 - (45 : F) * a41 ^ 2 * p2 +
      (27 : F) * p2 ^ 2) * hU

end BridgeLambdaScalars610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaPowerRelation610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- The eleventh sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁶⁰`.  The weight-fifty `ι` and
weight-fifty-five `κ` residuals remain available from the terminal and
kappa bridge packets. -/
theorem nonzeroFace610_bridgeLambdaPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ nu : k,
      bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C nu * h0 ^ 60 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    simp only [hp6, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  have hNrat : 5 * a5 * hRF ^ 4 - 3 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) (h0 ^ 9) = hRF ^ 9 := by
      simp only [hRF, map_pow]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * h0 ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hLval :
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 =
        RatFunc.C (-lambda / 3) := by
    have hL := depressedL610_eq_of_ninthPower hRF a5 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (sexticDepressionR610 hRF a5) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 q)
  have hf5 : f.coeff 5 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_five]
  have hf6 : f.coeff 6 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_six]
  have hf_high : ∀ n, 6 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_of_gt_six _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedQ610, depressedQ810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg6 :
      g.coeff 6 =
        depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedR610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 :
      g.coeff 5 =
        depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
          b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedS610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 :
      g.coeff 4 =
        depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedT610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg2 :
      g.coeff 2 =
        depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedV610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg3 :
      g.coeff 3 =
        depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedU610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg1 :
      g.coeff 1 =
        terminalDepressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_610_bridge (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [terminalDepressedW610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hg8' :
      g.coeff 8 =
        depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP610, depressedP810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 3) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * sexticDepressionR610 hRF a5 +
        (sourceToRatFunc68 q).coeff 9 / hRF ^ 9 =
          depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 3) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow13 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_13_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow12 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_12_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 12) hbracket
    simpa [f, g, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 3) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 8) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 3) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 7) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 3) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 4) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 6) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 2) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 3) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 4) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 3) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 5) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow6 :
      (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 0) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 1) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 2) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 3) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 5) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 3) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_6_monicSexticDecic_bridge
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 6) hbracket
    simpa [f, g, Polynomial.coeff_C, show (6 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow5 :
      (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 0) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 1) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 2) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 3) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 5) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 3) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 2) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_5_monicSexticDecic_bridge
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 5) hbracket
    simpa [f, g, Polynomial.coeff_C, show (5 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow3 :
      (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 0) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 1) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 2) +
        (1 : RatFunc k) * g.coeff 1 * ratFuncDerivation68 (f.coeff 3) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 3) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 2) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 1) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_3_monicSexticDecic_bridge
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 3) hbracket
    simpa [f, g, Polynomial.coeff_C, show (3 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf4 : f.coeff 4 =
      depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
    dsimp only [f, depressedA610, a5, a4]
    rw [hpDep, coeff_depressedSextic68_four]
  have hf3 : f.coeff 3 =
      depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 := by
    dsimp only [f, depressedB610, a5, a4, a3]
    rw [hpDep, coeff_depressedSextic68_three]
  have hf2 : f.coeff 2 =
      depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 := by
    dsimp only [f, depressedC610, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedSextic68_two]
  have hf1 : f.coeff 1 =
      depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedD610, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedSextic68_one]
  have hf0 : f.coeff 0 =
      depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedE610, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedSextic68_zero]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual610 (f.coeff 4) (g.coeff 8)) = 0 :=
    alphaResidual610_deriv_zero ratFuncDerivation68 (f.coeff 4)
      (g.coeff 8) hrow13
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (g.coeff 7)) = 0 :=
    betaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (g.coeff 7) hLconst (by simpa using hrow12)
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow11)
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow10)
  have heps0deriv :
      ratFuncDerivation68
        (epsilonResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha0
      hbeta0 hgamma0 (by simpa using hrow9)
  have hzeta0deriv :
      ratFuncDerivation68
        (zetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)
      hLconst halpha0 hbeta0 hgamma0 hdelta0 (by simpa using hrow8)
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2)) = 0 :=
    etaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 2) hLconst halpha0 hbeta0 hgamma0 hdelta0 heps0deriv
      (by simpa using hrow7)
  have htheta0deriv :
      ratFuncDerivation68
        (bridgeThetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 1)) = 0 :=
    bridgeThetaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 1) hLconst halpha0 hbeta0 hgamma0 hdelta0
      heps0deriv hzeta0deriv (by simpa using hrow6)
  have hlambda0deriv :
      ratFuncDerivation68
        (bridgeLambdaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1)) = 0 :=
    bridgeLambdaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst halpha0
      hbeta0 hgamma0 hdelta0 heps0deriv hzeta0deriv heta0deriv
      htheta0deriv (by simpa using hrow6) (by simpa using hrow5)
      (by simpa using hrow3)
  obtain ⟨nu0, hnu0⟩ :
      ∃ a : k,
        bridgeLambdaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hlambda0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        (258280326 : RatFunc k) * hRF ^ 60 *
          bridgeLambdaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) := by
    have hF := bridgeLambdaDefect_eq_cleared610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh
      (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    unfold bridgeClearedLambdaDefect610 bridgeLambdaResidual610 alphaResidual610 betaResidual610 deltaResidual610 epsilonResidual610 zetaResidual610 etaResidual610 bridgeThetaResidual610 at hF ⊢
    simpa [map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, a0, b8, b7, b6, b5, b4, b3, b2, b1, gammaResidual610, hf4, hf3, hf2, hf1, hf0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (258280326 * nu0) * h0 ^ 60) := by
    rw [hclear, hnu0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨258280326 * nu0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end BridgeLambdaPowerRelation610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section NonzeroLambdaIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local `λ` integral bridge: the `κ` bridge packet (the `ι`
and `κ` packets reused opaquely) together with the weight-`60`
clearing of the degree-`3` first integral, its `h₀⁵²`-peeled factored
head, the chamber-free kill `p₃₁(a) = 0` (eliminating the
`p₃₁(a) ≠ 0` complement child by honest contradiction), the globally
merged deeper jet `p₃ = h₀² p₃₂`, `q₇ = h₀⁶ u₂`, `q₅ = h₀³ q₅₃`,
`q₄ = h₀ q₄₁`, the `h₀⁵⁴`-peeled deep head with its chamber-free
sextic relation, the collapsed sibling child
`a₄₁(a) = p₂(a) = 0` with its cascade, and the pinned complement
child with the honest split `a₄₁(a) = 0 ∨ 324 q₄₁(a) = 35 a₄₁(a)³`.
Neither surviving child is closed. -/
theorem nonzeroFace610_linearRoot_lambdaIntegralBridge
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a41 s1 u1 p31 b62 q52 p32 u2 q53 q41 : k[X])
      (iotaK kappaMu lambdaNu : k),
      p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        (3 : k) * s1.eval a = (5 : k) * a41.eval a ∧
        (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a -
            (9 : k) * lambda * p31.eval a +
          (30 : k) * (p.coeff 2).eval a +
            (20 : k) * p31.eval a * w1.eval a = 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j ∧
        terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda =
          Polynomial.C iotaK * h0 ^ 50 ∧
        bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 (p.coeff 2)
              (q.coeff 4) (Polynomial.C lambda) +
            h0 * bridgeIotaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
              (Polynomial.C lambda) =
          Polynomial.C iotaK * h0 ^ 6 ∧
        bridgeIotaJetHead610 (w1.eval a) (a41.eval a) (p31.eval a)
            (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
            ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda = 0 ∧
        bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C kappaMu * h0 ^ 55 ∧
        bridgeKappaJetHead610 a41 p31 s1 u1 q52 (q.coeff 4) +
            h0 * bridgeKappaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C kappaMu * h0 ^ 7 ∧
        bridgeKappaJetHead610 (a41.eval a) (p31.eval a) (s1.eval a)
            (u1.eval a) (q52.eval a) ((q.coeff 4).eval a) = 0 ∧
        bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C lambdaNu * h0 ^ 60 ∧
        bridgeLambdaJetHead610 p31 u1 (q.coeff 4) +
            h0 * bridgeLambdaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C lambdaNu * h0 ^ 8 ∧
        bridgeLambdaJetHead610 (p31.eval a) (u1.eval a)
          ((q.coeff 4).eval a) = 0 ∧
        p31.eval a = 0 ∧ u1.eval a = 0 ∧ q52.eval a = 0 ∧
        (q.coeff 4).eval a = 0 ∧
        p.coeff 3 = h0 ^ 2 * p32 ∧ q.coeff 7 = h0 ^ 6 * u2 ∧
        q.coeff 5 = h0 ^ 3 * q53 ∧ q.coeff 4 = h0 * q41 ∧
        bridgeLambdaDeepHead610 a41 s1 b62 (p.coeff 2) q41 +
            h0 * bridgeLambdaDeepTail610 h0 w1 a41 p32 s1 u2 b62 q53
              (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C lambdaNu * h0 ^ 6 ∧
        bridgeLambdaDeepHead610 (a41.eval a) (s1.eval a) (b62.eval a)
          ((p.coeff 2).eval a) (q41.eval a) = 0 ∧
        (100 : k) * (a41.eval a) ^ 6 -
            (1575 : k) * (a41.eval a) ^ 4 * (p.coeff 2).eval a +
          (810 : k) * (a41.eval a) ^ 3 * q41.eval a +
            (4860 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 -
          (2916 : k) * a41.eval a * (p.coeff 2).eval a * q41.eval a -
            (1620 : k) * ((p.coeff 2).eval a) ^ 3 = 0 ∧
        ((bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
              h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                (Polynomial.C lambda) =
            Polynomial.C iotaK * h0 ^ 5 ∧
          a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
          s1.eval a = 0 ∧ b62.eval a = 0 ∧ q41.eval a = 0 ∧
          q53.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
          (3 : k) * u2.eval a = (5 : k) * p32.eval a) ∨
        ((6 : k) * (p.coeff 2).eval a - (a41.eval a) ^ 2 = 0 ∧
          (6 : k) * b62.eval a - (5 : k) * (a41.eval a) ^ 2 = 0 ∧
          ((a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
              b62.eval a = 0) ∨
            (324 : k) * q41.eval a = (35 : k) * (a41.eval a) ^ 3))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, kappaMu, hw, ha4s,
    hp3, hs, hu, hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow,
    hroweval, hipow, hipeel, hiheadeval, _hires1, _hires2, hkpow,
    hkpeel, hkheadeval, _hksplit0, _hksplit, halt⟩ :=
    nonzeroFace610_linearRoot_kappaIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  obtain ⟨lambdaNu, hlpow⟩ :=
    nonzeroFace610_bridgeLambdaPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have hlpowJet :
      bridgeClearedLambdaDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 * p31) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 5 * u1) (h0 ^ 4 * b62) (h0 ^ 2 * q52)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C lambdaNu * h0 ^ 60 := by
    rw [← hw, ← ha4s, ← hp3, ← hs, ← hu, ← hb6s, ← hq5]
    exact hlpow
  have hlpeel :
      bridgeLambdaJetHead610 p31 u1 (q.coeff 4) +
          h0 * bridgeLambdaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
            (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
            (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda) =
        Polynomial.C lambdaNu * h0 ^ 8 := by
    have h52 : (h0 : k[X]) ^ 52 ≠ 0 := pow_ne_zero 52 hh0
    apply mul_left_cancel₀ h52
    rw [← bridgeClearedLambdaDefect610_jet_factored h0 w1 a41 p31 s1
      u1 b62 q52 (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda]
    rw [hlpowJet]
    ring
  have hlheadeval :
      bridgeLambdaJetHead610 (p31.eval a) (u1.eval a)
        ((q.coeff 4).eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hlpeel
    have h8z : (0 : k) ^ 8 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeLambdaJetHead610_eval, h8z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hp31z : p31.eval a = 0 :=
    bridgeLambda_chamberFree_kill610 (p31.eval a) (u1.eval a)
      ((q.coeff 4).eval a) hlheadeval hTu hWq
  have h3ne : (3 : k) ≠ 0 := by norm_num
  have h9ne : (9 : k) ≠ 0 := by norm_num
  have hu1z : u1.eval a = 0 := by
    have h30 : (3 : k) * u1.eval a = 0 := by
      rw [hTu, hp31z]
      ring
    exact (mul_eq_zero.mp h30).resolve_left h3ne
  have hq52z : q52.eval a = 0 := by
    have h90 : (9 : k) * q52.eval a = 0 := by
      rw [hVq, hp31z]
      ring
    exact (mul_eq_zero.mp h90).resolve_left h9ne
  have hq4z : (q.coeff 4).eval a = 0 := by
    have h90 : (9 : k) * (q.coeff 4).eval a = 0 := by
      rw [hWq, hp31z]
      ring
    exact (mul_eq_zero.mp h90).resolve_left h9ne
  obtain ⟨p32, hp32⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 p31 a hh0degree hroot
      hp31z
  obtain ⟨u2, hu2⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 u1 a hh0degree hroot
      hu1z
  obtain ⟨q53, hq53⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 q52 a hh0degree hroot
      hq52z
  obtain ⟨q41, hq41⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 4) a
      hh0degree hroot hq4z
  have hp3' : p.coeff 3 = h0 ^ 2 * p32 := by
    rw [hp3, hp32]
    ring
  have hq7' : q.coeff 7 = h0 ^ 6 * u2 := by
    rw [hu, hu2]
    ring
  have hq5' : q.coeff 5 = h0 ^ 3 * q53 := by
    rw [hq5, hq53]
    ring
  have hq4' : q.coeff 4 = h0 * q41 := hq41
  have hlpowDeep :
      bridgeClearedLambdaDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 ^ 2 * p32) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 6 * u2) (h0 ^ 4 * b62) (h0 ^ 3 * q53)
          (h0 * q41) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C lambdaNu * h0 ^ 60 := by
    rw [← hw, ← ha4s, ← hp3', ← hs, ← hq7', ← hb6s, ← hq5', ← hq4']
    exact hlpow
  have hldeepPeel :
      bridgeLambdaDeepHead610 a41 s1 b62 (p.coeff 2) q41 +
          h0 * bridgeLambdaDeepTail610 h0 w1 a41 p32 s1 u2 b62 q53
            (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
            (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda) =
        Polynomial.C lambdaNu * h0 ^ 6 := by
    have h54 : (h0 : k[X]) ^ 54 ≠ 0 := pow_ne_zero 54 hh0
    apply mul_left_cancel₀ h54
    rw [← bridgeClearedLambdaDefect610_deepJet_factored h0 w1 a41 p32
      s1 u2 b62 q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda]
    rw [hlpowDeep]
    ring
  have hldeepHeadEval :
      bridgeLambdaDeepHead610 (a41.eval a) (s1.eval a) (b62.eval a)
        ((p.coeff 2).eval a) (q41.eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hldeepPeel
    have h6z : (0 : k) ^ 6 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeLambdaDeepHead610_eval, h6z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hUz : (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a +
      (30 : k) * (p.coeff 2).eval a = 0 := by
    linear_combination hUload +
      ((9 : k) * lambda - (20 : k) * w1.eval a) * hp31z
  have hG :
      (100 : k) * (a41.eval a) ^ 6 -
          (1575 : k) * (a41.eval a) ^ 4 * (p.coeff 2).eval a +
        (810 : k) * (a41.eval a) ^ 3 * q41.eval a +
          (4860 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 -
        (2916 : k) * a41.eval a * (p.coeff 2).eval a * q41.eval a -
          (1620 : k) * ((p.coeff 2).eval a) ^ 3 = 0 :=
    bridgeLambda_deepReduction610 (a41.eval a) (s1.eval a)
      (b62.eval a) ((p.coeff 2).eval a) (q41.eval a) hldeepHeadEval
      hMs hUz
  refine ⟨w1, a41, s1, u1, p31, b62, q52, p32, u2, q53, q41, iotaK,
    kappaMu, lambdaNu, hw, ha4s, hp3, hs, hu, hb6s, hq5, hMs, hUload,
    hrow, hroweval, hipow, hipeel, hiheadeval, hkpow, hkpeel,
    hkheadeval, hlpow, hlpeel, hlheadeval, hp31z, hu1z, hq52z, hq4z,
    hp3', hq7', hq5', hq4', hldeepPeel, hldeepHeadEval, hG, ?_⟩
  rcases halt with ⟨-, p32', u2', q53', q41', hp3s, hq7s, hq5s, hq4s,
      hrel1, hrel2, hrel3, hrel4, hileft, -, hsplit⟩ |
    ⟨-, -, hcd⟩
  · have hp32e : p32' = p32 :=
      mul_left_cancel₀ (pow_ne_zero 2 hh0) (hp3s.symm.trans hp3')
    have hu2e : u2' = u2 :=
      mul_left_cancel₀ (pow_ne_zero 6 hh0) (hq7s.symm.trans hq7')
    have hq53e : q53' = q53 :=
      mul_left_cancel₀ (pow_ne_zero 3 hh0) (hq5s.symm.trans hq5')
    have hq41e : q41' = q41 :=
      mul_left_cancel₀ hh0 (hq4s.symm.trans hq4')
    simp only [hp32e, hu2e, hq53e, hq41e] at hrel1 hrel2 hrel3 hrel4 hileft
    obtain ⟨ha41z, hp2z⟩ :=
      bridgeLambda_siblingCollapse610 (a41.eval a)
        ((p.coeff 2).eval a) (q41.eval a) hG hrel2 hsplit
    have hs1z : s1.eval a = 0 := by
      have h30 : (3 : k) * s1.eval a = 0 := by
        rw [hMs, ha41z]
        ring
      exact (mul_eq_zero.mp h30).resolve_left h3ne
    have hb62z : b62.eval a = 0 := by
      linear_combination (-(1 : k) / 18) * hUz +
        ((5 : k) / 9) * a41.eval a * ha41z + ((5 : k) / 3) * hp2z
    have hq41z : q41.eval a = 0 := by
      linear_combination ((1 : k) / 81) * hrel2 +
        (((10 : k) / 9) * (p.coeff 2).eval a -
          ((5 : k) / 81) * (a41.eval a) ^ 2) * ha41z
    have hq53z : q53.eval a = 0 := by
      linear_combination ((1 : k) / 216) * hrel3 +
        (-(lambda * a41.eval a) / 8 -
          ((5 : k) / 27) * a41.eval a * w1.eval a +
          ((10 : k) / 9) * p32.eval a) * ha41z +
        (-lambda / 2 + ((10 : k) / 9) * w1.eval a) * hp2z
    have hq3z : (q.coeff 3).eval a = 0 := by
      linear_combination ((1 : k) / 3888) * hrel4 +
        (lambda * (a41.eval a) ^ 2 / 48 +
          ((20 : k) / 243) * (a41.eval a) ^ 2 * w1.eval a -
          ((5 : k) / 27) * a41.eval a * p32.eval a -
          lambda * (p.coeff 2).eval a / 4 -
          ((10 : k) / 27) * (p.coeff 2).eval a * w1.eval a) * ha41z +
        ((10 : k) / 9) * p32.eval a * hp2z
    have hu2tie : (3 : k) * u2.eval a = (5 : k) * p32.eval a := by
      linear_combination ((1 : k) / 6) * hrel1 +
        (((10 : k) / 3) * w1.eval a - ((3 : k) / 2) * lambda) * ha41z
    exact Or.inl ⟨hileft, ha41z, hp2z, hs1z, hb62z, hq41z, hq53z,
      hq3z, hu2tie⟩
  · rcases hcd with ⟨-, hp2pin, hb62pin⟩ | ⟨hnz, -⟩
    · refine Or.inr ⟨hp2pin, hb62pin, ?_⟩
      rcases bridgeLambda_complementSplit610 (a41.eval a)
          ((p.coeff 2).eval a) (q41.eval a) hG hp2pin with
        ha41z | hq41pin
      · left
        have hp2z : (p.coeff 2).eval a = 0 := by
          linear_combination ((1 : k) / 6) * hp2pin +
            ((1 : k) / 6) * a41.eval a * ha41z
        have hb62z : b62.eval a = 0 := by
          linear_combination ((1 : k) / 6) * hb62pin +
            ((5 : k) / 6) * a41.eval a * ha41z
        exact ⟨ha41z, hp2z, hb62z⟩
      · exact Or.inr hq41pin
    · exact absurd hp31z hnz

end NonzeroLambdaIntegralBridge610

end Max11DegreeRoutes
