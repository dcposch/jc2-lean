import Sol610ScaleTwoDegreeZeroPostCollapseCoordinateBridgeScratch
import Sol610ScaleTwoDegreeZeroPostCollapseHeadSplitScratch

/-! # Source-facing wrapper for the `(6,10)` degree-zero post-collapse split

`SourceBridge` currently proves the order-`69` head from an explicitly
assumed ordinary-derivative equation.  This module discharges that
assumption from a literal `(6,10)` source:

1. instantiate `differentialJacobian_affineDepress_sourceToRatFunc68`;
2. apply `degreeZeroPrimitive610_ratFuncDeriv_eq_simplePole`;
3. identify the depressed coefficients with the compact post-collapse
   coordinates via the coordinate bridge (Backwire peel);
4. only then feed the resulting head to the conditional HeadSplit.

The conclusion is the honest disjunction `p32(a) = 0 ∨ q41(a) = 0`.
Deeper chambers remain after that split and are recorded, not closed.
The last primitive slot `X0` is definitionally dummy, so the monic
Jacobian primitive agrees with the compact `X0 = 0` specialization.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section DegreeZeroPrimitiveDummy610

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
/-- The weight-fifteen primitive does not use its last slot, so the monic
Jacobian value agrees with the compact `X0 = 0` specialization. -/
theorem degreeZeroPrimitive610_independent_of_X0
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 Y0 : F) :
    degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 =
      degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 Y0 :=
  rfl

#print axioms degreeZeroPrimitive610_independent_of_X0

end DegreeZeroPrimitiveDummy610

section DegreeZeroSourceWrapper610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- The compact post-collapse primitive, on the Backwire peel of a literal
`(6,10)` source, has the ordinary simple-pole derivative supplied by the
affine source Jacobian.  The constant `58498535041007616` is the compact
clearing factor used by `SourceBridge`; no ordinary-derivative equation is
assumed. -/
theorem degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41) :
    Differential.deriv
        ((58498535041007616 : RatFunc k) *
          degreeZeroPostCollapsePrimitive610
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) w1)
            (algebraMap k[X] (RatFunc k) a42)
            (algebraMap k[X] (RatFunc k) p32)
            (algebraMap k[X] (RatFunc k) p21)
            (algebraMap k[X] (RatFunc k) (p.coeff 1))
            (algebraMap k[X] (RatFunc k) (p.coeff 0))
            (algebraMap k[X] (RatFunc k) s2)
            (algebraMap k[X] (RatFunc k) u2)
            (algebraMap k[X] (RatFunc k) b63)
            (algebraMap k[X] (RatFunc k) q53)
            (algebraMap k[X] (RatFunc k) q41)
            (algebraMap k[X] (RatFunc k) (q.coeff 3))
            (algebraMap k[X] (RatFunc k) (q.coeff 2))
            (algebraMap k[X] (RatFunc k) (q.coeff 1))
            (RatFunc.C lambda)) =
      RatFunc.C (58498535041007616 * j) /
        algebraMap k[X] (RatFunc k) h0 := by
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
  let w1RF : RatFunc k := algebraMap k[X] (RatFunc k) w1
  let a42RF : RatFunc k := algebraMap k[X] (RatFunc k) a42
  let p32RF : RatFunc k := algebraMap k[X] (RatFunc k) p32
  let p21RF : RatFunc k := algebraMap k[X] (RatFunc k) p21
  let s2RF : RatFunc k := algebraMap k[X] (RatFunc k) s2
  let u2RF : RatFunc k := algebraMap k[X] (RatFunc k) u2
  let b63RF : RatFunc k := algebraMap k[X] (RatFunc k) b63
  let q53RF : RatFunc k := algebraMap k[X] (RatFunc k) q53
  let q41RF : RatFunc k := algebraMap k[X] (RatFunc k) q41
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 q)
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    simp only [hp6, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  have hNrat :
      5 * a5 * hRF ^ 4 - 3 * b9 = RatFunc.C lambda * hRF ^ 9 := by
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
        (Polynomial.C lambda * h0 ^ 9) = RatFunc.C lambda * hRF ^ 9 := by
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
  have hg_high_src : ∀ n, 10 < n →
      (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg9L : g.coeff 9 =
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL610, depressedL810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9]
  have hg9const : g.coeff 9 = RatFunc.C (-lambda / 3) := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9const]
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 3) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hprim :
      Differential.deriv
          (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 1) (g.coeff 0)) =
        RatFunc.C j / hRF :=
    degreeZeroPrimitive610_ratFuncDeriv_eq_simplePole f g j hRF
      hf_high hf6 hf5 hg_high hg10 hLconst (by simpa only [f, g] using hbracket)
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
      depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1 a0 := by
    dsimp only [f, depressedE610, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedSextic68_zero]
  have hg8' : g.coeff 8 =
      depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP610, depressedP810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg7 : g.coeff 7 =
      depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedQ610, depressedQ810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg6 : g.coeff 6 =
      depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedR610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 : g.coeff 5 =
      depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedS610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 : g.coeff 4 =
      depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedT610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg3 : g.coeff 3 =
      depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedU610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg2 : g.coeff 2 =
      depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedV610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg1 : g.coeff 1 =
      depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 b4
        b3 b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedW610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have ha5peel : a5 = hRF ^ 5 * w1RF := by
    simp only [a5, w1RF, hRF, hw, map_mul, map_pow]
  have ha4peel : a4 = hRF ^ 4 * a42RF := by
    simp only [a4, a42RF, hRF, hp4deep, map_mul, map_pow]
  have ha3peel : a3 = hRF ^ 2 * p32RF := by
    simp only [a3, p32RF, hRF, hp3deep, map_mul, map_pow]
  have ha2peel : a2 = hRF * p21RF := by
    simp only [a2, p21RF, hRF, hp2deep, map_mul]
  have hb8peel : b8 = hRF ^ 8 * s2RF := by
    simp only [b8, s2RF, hRF, hq8deep, map_mul, map_pow]
  have hb7peel : b7 = hRF ^ 6 * u2RF := by
    simp only [b7, u2RF, hRF, hq7deep, map_mul, map_pow]
  have hb6peel : b6 = hRF ^ 5 * b63RF := by
    simp only [b6, b63RF, hRF, hq6deep, map_mul, map_pow]
  have hb5peel : b5 = hRF ^ 3 * q53RF := by
    simp only [b5, q53RF, hRF, hq5deep, map_mul, map_pow]
  have hb4peel : b4 = hRF * q41RF := by
    simp only [b4, q41RF, hRF, hq4deep, map_mul]
  have hNpeel :
      5 * (hRF ^ 5 * w1RF) * hRF ^ 4 - 3 * b9 =
        RatFunc.C lambda * hRF ^ 9 := by
    simpa only [ha5peel] using hNrat
  have hcoords :
      degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) (g.coeff 0) =
        degreeZeroPostCollapsePrimitive610 hRF w1RF a42RF p32RF p21RF
          a1 a0 s2RF u2RF b63RF q53RF q41RF b3 b2 b1
          (RatFunc.C lambda) := by
    rw [degreeZeroPrimitive610_independent_of_X0
      (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
      (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
      (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) 0]
    rw [hg9L, hf4, hf3, hf2, hf1, hf0, hg8', hg7, hg6, hg5, hg4, hg3,
      hg2, hg1, ha5peel, ha4peel, ha3peel, ha2peel, hb8peel, hb7peel,
      hb6peel, hb5peel, hb4peel]
    exact (degreeZeroPostCollapsePrimitive610_eq_depressed hRF w1RF
      a42RF p32RF p21RF a1 a0 b9 s2RF u2RF b63RF q53RF q41RF b3 b2 b1
      (RatFunc.C lambda) hh hNpeel).symm
  have hprim' :
      Differential.deriv
          (degreeZeroPostCollapsePrimitive610 hRF w1RF a42RF p32RF
            p21RF a1 a0 s2RF u2RF b63RF q53RF q41RF b3 b2 b1
            (RatFunc.C lambda)) =
        RatFunc.C j / hRF := by
    rw [← hcoords]
    exact hprim
  have hnum : (58498535041007616 : RatFunc k) =
      RatFunc.C (58498535041007616 : k) :=
    (map_natCast (RatFunc.C : k →+* RatFunc k) 58498535041007616).symm
  let prim : RatFunc k :=
    degreeZeroPostCollapsePrimitive610 hRF w1RF a42RF p32RF p21RF a1 a0
      s2RF u2RF b63RF q53RF q41RF b3 b2 b1 (RatFunc.C lambda)
  have hleib :
      Differential.deriv ((58498535041007616 : RatFunc k) * prim) =
        (58498535041007616 : RatFunc k) * (RatFunc.C j / hRF) := by
    have hmul :
        Differential.deriv
            (RatFunc.C (58498535041007616 : k) * prim) =
          RatFunc.C (58498535041007616 : k) * Differential.deriv prim := by
      simpa [ratFuncDerivation46_apply, Algebra.smul_def] using
        ratFuncDerivation46.map_smul (58498535041007616 : k) prim
    rw [hnum, hmul, hprim']
  have hscale :
      (58498535041007616 : RatFunc k) * (RatFunc.C j / hRF) =
        RatFunc.C (58498535041007616 * j) / hRF := by
    rw [hnum, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← map_mul]
  rw [hleib, hscale]

#print axioms degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source

/-- The degree-zero post-collapse head vanishes at a linear root of `h0`,
once the compact primitive derivative is obtained from the source
Jacobian rather than assumed. -/
theorem degreeZeroPostCollapseJetHead610_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41) :
    degreeZeroPostCollapseJetHead610 (p32.eval a) (q41.eval a) = 0 :=
  degreeZeroPostCollapseJetHead610_zero_of_primitiveDeriv h0 w1 a42 p32
    p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41 (q.coeff 3)
    (q.coeff 2) (q.coeff 1) lambda (58498535041007616 * j) a hh0
    hh0degree hroot
    (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
      p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hH
      hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep hq6deep
      hq5deep hq4deep)

#print axioms degreeZeroPostCollapseJetHead610_zero_of_source

/-- Source-facing degree-zero split.  After the Backwire peel, the
order-`69` head forces `p32(a) = 0 ∨ q41(a) = 0`.  Deeper chambers remain. -/
theorem degreeZeroFace610_linearRoot_postCollapseHeadSplit
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
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      degreeZeroPostCollapseJetHead610 (p32.eval a) (q41.eval a) = 0 ∧
      (p32.eval a = 0 ∨ q41.eval a = 0) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep⟩ :=
    nonzeroFace610_linearRoot_fourteenthComplementBackwire p q H h0 j
      lambda a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  have hhead := degreeZeroPostCollapseJetHead610_zero_of_source p q H h0
    j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hh0degree hH
    hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep hq8deep hq7deep
    hq6deep hq5deep hq4deep
  exact ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep, hp3deep,
    hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, hhead,
    degreeZeroPostCollapseJetHead610_split (p32.eval a) (q41.eval a)
      hhead⟩

#print axioms degreeZeroFace610_linearRoot_postCollapseHeadSplit

/-- Joint chamber split with the already landed fourth-tail head.  This is
not a closure claim: each arm still has a residual cofactor. -/
theorem degreeZeroFace610_linearRoot_postCollapseChambers
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
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      ((p32.eval a = 0 ∧ (q41.eval a = 0 ∨ p21.eval a = 0)) ∨
        (q41.eval a = 0 ∧
          (p32.eval a = 0 ∨
            10 * (p32.eval a) ^ 2 * (q53.eval a) +
                (18 * (p32.eval a) * (w1.eval a) -
                  27 * (p21.eval a)) * (q.coeff 3).eval a = 0))) := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, _nu, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      _hpost, hfourteenth⟩ :=
    nonzeroFace610_linearRoot_postCollapseResidual p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  have hdegree := degreeZeroPostCollapseJetHead610_zero_of_source p q H
    h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hh0degree
    hH hp6 hq10 hN hD hroot hw hp4deep hp3deep hp2deep hq8deep hq7deep
    hq6deep hq5deep hq4deep
  exact ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep, hp3deep,
    hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
    degreeZeroAndFourteenthPostCollapseJetHeads610_chambers
      (w1.eval a) (a42.eval a) (p32.eval a) (q53.eval a) (p21.eval a)
      ((p.coeff 1).eval a) (q41.eval a) ((q.coeff 3).eval a) hdegree
      hfourteenth⟩

#print axioms degreeZeroFace610_linearRoot_postCollapseChambers

end DegreeZeroSourceWrapper610

end Max11DegreeRoutes
