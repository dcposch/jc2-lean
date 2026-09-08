import Grok610AlignedSquareSourceWrapperPart38Scratch
import Grok610AlignedSquareSourceWrapperPart39Scratch
import Grok610AlignedSquareSourceWrapperPart41Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareSourceWrapper610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- The weight-fifteen primitive, on the MixedPair peel of a literal
aligned `(6,10)` source, has the ordinary simple-pole derivative
supplied by the affine source Jacobian.  AffineBracket divides by
exactly one power of `h`, independently of the inner degrees, and
`N = 0` makes `L` a field constant, so the derivative pole is `1`
rather than a higher-order pole `C(j)/h₀ᵏ` for `k > 1`.  This is not
the remaining pole `21` of `ρ` itself. -/
theorem alignedSquarePrimitive610_deriv_eq_simplePole_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j : k)
    (w1 f2 e1 e2 e3 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hw : p.coeff 5 = h0 ^ 4 * w1)
    (hp4 : p.coeff 4 = h0 ^ 2 * f2)
    (he1 : (3 : k[X]) * f2 - w1 ^ 2 = h0 * e1)
    (he2 : (27 : k[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2)
    (he3 : e2 = h0 * e3) :
    Differential.deriv
        (alignedSquarePeeledPrimitive610
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) w1)
          (algebraMap k[X] (RatFunc k) f2)
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 8))
          (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
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
  let f2RF : RatFunc k := algebraMap k[X] (RatFunc k) f2
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
  have hNrat : 5 * a5 * hRF ^ 4 - 3 * b9 = 0 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow]
      ring
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k) (0 : k[X]) = 0 :=
      map_zero (algebraMap k[X] (RatFunc k))
    exact hleft.symm.trans (hmapped.trans hright)
  have hLval :
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 = 0 :=
    alignedSquareL_eq_zero610 hRF a5 b9 hh hNrat
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
  have hg9const : g.coeff 9 = 0 := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9const]
    have hx := ratFuncDerivation46_polynomial (C (0 : k) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hprim :
      Differential.deriv
          (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 1) (g.coeff 0)) =
        RatFunc.C j / hRF :=
    degreeZeroPrimitive610_ratFuncDeriv_eq_simplePole f g j hRF
      hf_high hf6 hf5 hg_high hg10 hLconst
      (by simpa only [f, g] using hbracket)
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
  have ha5peel : a5 = hRF ^ 4 * w1RF := by
    simp only [a5, w1RF, hRF, hw, map_mul, map_pow]
  have ha4peel : a4 = hRF ^ 2 * f2RF := by
    simp only [a4, f2RF, hRF, hp4, map_mul, map_pow]
  have hb9peel : b9 = (5 : RatFunc k) / 3 * (hRF ^ 4 * w1RF) * hRF ^ 4 := by
    have h3 : (3 : RatFunc k) ≠ 0 := by norm_num
    have hN' :
        (3 : RatFunc k) * b9 = (5 : RatFunc k) * a5 * hRF ^ 4 := by
      linear_combination -hNrat
    have hb9 : b9 = (5 : RatFunc k) / 3 * a5 * hRF ^ 4 := by
      field_simp [h3]
      linear_combination hN'
    simpa [ha5peel] using hb9
  have hcoords :
      degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) (g.coeff 0) =
        alignedSquarePeeledPrimitive610 hRF w1RF f2RF a3 a2 a1 a0 b8 b7
          b6 b5 b4 b3 b2 b1 := by
    rw [alignedSquarePrimitive610_independent_of_X0
      (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
      (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
      (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) 0]
    simp only [alignedSquarePeeledPrimitive610,
      alignedSquareSourcePrimitive610]
    rw [hg9L, hf4, hf3, hf2, hf1, hf0, hg8', hg7, hg6, hg5, hg4, hg3,
      hg2, hg1, ha5peel, ha4peel, hb9peel]
  rw [← hcoords]
  exact hprim

end AlignedSquareSourceWrapper610

end Max11DegreeRoutes
