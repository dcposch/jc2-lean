import Sol610ScaleTwoAlignedFourteenthResidualDifferentialBridgeScratch

/-! # Same-source RatFunc bridge for the aligned `(6,10)` ν tail

No source is selected here.  The supplied sextic/decic witness is mapped to
the normalized RatFunc model, depressed by its own quintic coefficient, and
passed unchanged to the verified monic differential certificate.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000

section AlignedSquareSourceFourteenthResidual610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- The normalized weight-seventy residual attached to the supplied aligned
square-core source has zero RatFunc derivative.  In particular, this theorem
does not reselect `p`, `q`, `H`, or `h0`. -/
theorem alignedSquareSource610_fourteenthResidual_deriv_zero
    (p q : k[X][X]) (H h0 : k[X]) (j : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
    let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
    let f : (RatFunc k)[X] :=
      affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 p)
    let g : (RatFunc k)[X] :=
      affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 q)
    ratFuncDerivation68
      (fourteenthResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
        (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
        (g.coeff 1)) = 0 := by
  dsimp only
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
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
    simpa only [map_sub, map_mul, map_ofNat, map_zero, a5, b9, hH2]
      using hmapped
  have hLval :
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 = 0 := by
    have hL := depressedL610_eq_of_ninthPower hRF a5 b9 0 hh
      (by simpa using hNrat)
    simpa using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (sexticDepressionR610 hRF a5) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 q)
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
  obtain ⟨hg10, hg9, _hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg9zero : g.coeff 9 = 0 := by
    dsimp only [g]
    rw [hg9]
    have heq : -10 * sexticDepressionR610 hRF a5 +
        (sourceToRatFunc68 q).coeff 9 / hRF ^ 9 =
          depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    rw [heq, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9zero]
    exact map_zero ratFuncDerivation68
  apply fourteenthResidual610_deriv_zero_of_monic_differentialJacobian
    ratFuncDerivation68 f g (RatFunc.C j / hRF) hf_high hf6 hf5
    hg_high hg10 hLconst
  simpa only [f, g] using hbracket

#print axioms alignedSquareSource610_fourteenthResidual_deriv_zero

end AlignedSquareSourceFourteenthResidual610

end Max11DegreeRoutes
