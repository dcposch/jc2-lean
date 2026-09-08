import Sol610ScaleTwoNonzeroFourteenthCompactClearingScratch

/-! # Constant-field descent of the nonzero `(6,10)` fourth-tail defect

The compact 85-term bar-coordinate numerator is transported to `RatFunc`,
where the general monic differential-Jacobian certificate makes the fourth
tail constant.  The supplied source, square root `h0`, and ninth-power
parameter `lambda` are unchanged.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section NonzeroFourteenthDefectMap610

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 400000000 in
/-- The compact nonzero source numerator commutes with ring homomorphisms. -/
theorem map_nonzeroLocalClearedFourteenthDefect610
    (phi : R →+* S)
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    phi (nonzeroLocalClearedFourteenthDefect610 h a5 a4 a3 a2 a1 a0 b8
      b7 b6 b5 b4 b3 b2 b1 lambda) =
      nonzeroLocalClearedFourteenthDefect610
        (phi h) (phi a5) (phi a4) (phi a3) (phi a2) (phi a1) (phi a0)
        (phi b8) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3) (phi b2)
        (phi b1) (phi lambda) := by
  simp only [nonzeroLocalClearedFourteenthDefect610,
    nonzeroClearedFourteenthResidual610, clearedFourteenthResidual610,
    map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]

end NonzeroFourteenthDefectMap610

section NonzeroFourteenthConstantFieldDescent610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- On the same supplied nonzero ninth-power source, the exact compact
weight-seventy fourth-tail numerator is a ground scalar times `h₀⁷⁰`. -/
theorem nonzeroFace610_fourteenthResidualPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 = Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ nu : k,
      nonzeroLocalClearedFourteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C nu * h0 ^ 70 := by
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
  have hnuDeriv : ratFuncDerivation68
      (fourteenthResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
        (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
        (g.coeff 1)) = 0 := by
    apply fourteenthResidual610_deriv_zero_of_monic_differentialJacobian
      ratFuncDerivation68 f g (RatFunc.C j / hRF) hf_high hf6 hf5
      hg_high hg10 hLconst
    simpa only [f, g] using hbracket
  obtain ⟨nu0, hnu0⟩ : ∃ nu0 : k,
      fourteenthResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) = algebraMap k (RatFunc k) nu0 := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hnuDeriv
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
  have hmapLocal :
      algebraMap k[X] (RatFunc k)
          (nonzeroLocalClearedFourteenthDefect610 h0 (p.coeff 5)
            (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda)) =
        nonzeroLocalClearedFourteenthDefect610 hRF a5 a4 a3 a2 a1 a0 b8
          b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) := by
    simpa only [hRF, a5, a4, a3, a2, a1, a0, b8, b7, b6, b5, b4, b3,
      b2, b1, RatFunc.algebraMap_C] using
      (map_nonzeroLocalClearedFourteenthDefect610
        (algebraMap k[X] (RatFunc k) : k[X] →+* RatFunc k)
        h0 (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
        (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
        (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
        (Polynomial.C lambda))
  have hF := fourteenthDefect_eq_nonzeroClearedNu610 hRF a5 a4 a3 a2 a1
    a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh
    (by simpa using hNrat)
  have hclear :
      algebraMap k[X] (RatFunc k)
          (nonzeroLocalClearedFourteenthDefect610 h0 (p.coeff 5)
            (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda)) =
        (19042491875328 : RatFunc k) * hRF ^ 70 *
          fourteenthResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) := by
    rw [hmapLocal, ← hF]
    rw [hg9L, hf4, hf3, hf2, hf1, hf0, hg8', hg7, hg6, hg5, hg4, hg3,
      hg2, hg1]
  have htarget :
      algebraMap k[X] (RatFunc k)
          (nonzeroLocalClearedFourteenthDefect610 h0 (p.coeff 5)
            (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda)) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (19042491875328 * nu0) * h0 ^ 70) := by
    rw [hclear, hnu0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  refine ⟨19042491875328 * nu0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

#print axioms map_nonzeroLocalClearedFourteenthDefect610
#print axioms nonzeroFace610_fourteenthResidualPowerRelation

end NonzeroFourteenthConstantFieldDescent610

end Max11DegreeRoutes
