import Grok810DegreeZeroPrimitiveScratch

/-! # Source-facing wrapper for the `(8,10)` degree-zero primitive

Lane Z3 of the `(8,10)` chamber map.  Lanes Z0–Z2 record the inhomogeneous
degree-zero Jacobian row, the grouped primitive `ρ`, and the monic
differential bridge `dρ = c` on a constant depressed Jacobian.  This file
discharges that constant from a literal `(8,10)` source:

1. instantiate `differentialJacobian_affineDepress_sourceToRatFunc68`;
2. apply `rhoResidual810_deriv_eq_constant_of_monic_differentialJacobian`;
3. identify the depressed octic/decic coefficients with the source
   depression already used by the Pi chain.

The affine change is `y = (z - r)/h`.  The committed AffineBracket
identity, reused by every `(4,6)`/`(6,8)`/`(6,10)`/`(8,10)` source
wrapper, divides the outer Jacobian by exactly one power of `h`,
independent of the inner degrees.  The Pi-chain source split already
feeds the same identity the constant `C(j)/h`.  Consequently the
degree-zero pole is simple: `ρ' = C(j)/h₀`, not a higher-order pole
`C(j)/h₀^k` for `k > 1`.  This is not copied from the `(6,10)`
clearing constant, and no `h^{97}` jet is solved.

The conclusion is the ordinary-derivative equation a later pole lemma
consumes.  No linear-root vanishing, chamber split, or closure is
claimed.  After degree `0` there is no unused Keller row; the residual
is the simple-pole obstruction itself.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false

section DegreeZeroSourcePrimitive810

variable {F : Type*} [Field F] [CharZero F]

/-- The grouped degree-zero primitive, evaluated on the octic-decic
depression of literal source coefficients.  The ninth-power scalar
`λ` is not substituted: `L` remains the honest depressed `z⁹`
coefficient. -/
def sourceRhoResidual810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  rhoResidual810
    (depressedL810 h (octicDepressionR810 h a7) b9)
    (depressedA810 h (octicDepressionR810 h a7) a7 a6)
    (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
    (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
    (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
    (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
    (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1)
    (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 a0)
    (depressedP810 h (octicDepressionR810 h a7) b9 b8)
    (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
    (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
    (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
    (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
    (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3)
    (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2)
    (depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2 b1)

end DegreeZeroSourcePrimitive810

section DegreeZeroRatFuncBridge810

variable {k : Type*} [Field k] [CharZero k]

/-- Ordinary-derivative specialization of the monic degree-zero bridge.
The affine source depression supplies precisely the displayed simple
pole as its constant outer-polynomial coefficient. -/
theorem rhoResidual810_ratFuncDeriv_eq_simplePole
    (f g : (RatFunc k)[X]) (j : k) (h : RatFunc k)
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : ratFuncDerivation68 (g.coeff 9) = 0)
    (hjac : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C j / h)) :
    Differential.deriv
        (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1)) =
      RatFunc.C j / h := by
  simpa only [ratFuncDerivation68, ratFuncDerivation46_apply] using
    rhoResidual810_deriv_eq_constant_of_monic_differentialJacobian
      ratFuncDerivation68 f g (RatFunc.C j / h) hf_high hf8 hf7 hg_high
      hg10 hL hjac

#print axioms rhoResidual810_ratFuncDeriv_eq_simplePole

end DegreeZeroRatFuncBridge810

section DegreeZeroSourceWrapper810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- The grouped degree-zero primitive, on the octic-decic depression of
a literal `(8,10)` source, has the ordinary simple-pole derivative
supplied by the affine source Jacobian.  No ordinary-derivative
equation is assumed, and no `(6,10)` clearing constant is inserted. -/
theorem sourceRhoResidual810_deriv_eq_simplePole_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    Differential.deriv
        (sourceRhoResidual810
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (p.coeff 7))
          (algebraMap k[X] (RatFunc k) (p.coeff 6))
          (algebraMap k[X] (RatFunc k) (p.coeff 5))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 9))
          (algebraMap k[X] (RatFunc k) (q.coeff 8))
          (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
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
  have hh : h ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 8) = h ^ 8 := by
    simp only [hp8, hH, h, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = h ^ 10 := by
    simp only [hq10, hH, h, map_pow]
    ring
  have hpDep := affineDepress_sourceOctic68 p h
    (octicDepressionR810 h a7) hp hh hpTop
  have hL0 : depressedL68 h (octicDepressionR810 h a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter h a7 hh
  have hNrat : 5 * a7 * h ^ 2 - 4 * b9 = RatFunc.C lambda * h ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    simpa only [hH, h, a7, b9, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hLval :
      depressedL810 h (octicDepressionR810 h a7) b9 =
        RatFunc.C (-lambda / 4) := by
    have hL := depressedL810_eq_of_ninthPower h a7 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j h (octicDepressionR810 h a7) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 h (octicDepressionR810 h a7) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 h (octicDepressionR810 h a7) (sourceToRatFunc68 q)
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_seven, hL0]
  have hf8 : f.coeff 8 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_eight]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = h ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedQ810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7]
  have hg6 :
      g.coeff 6 =
        depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedR810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 :
      g.coeff 5 =
        depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedS810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 :
      g.coeff 4 =
        depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedT810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg3 :
      g.coeff 3 =
        depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedU810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg2 :
      g.coeff 2 =
        depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedV810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg1 :
      g.coeff 1 =
        depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedW810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hg8' :
      g.coeff 8 =
        depressedP810 h (octicDepressionR810 h a7) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8]
  have hg9L : g.coeff 9 =
      depressedL810 h (octicDepressionR810 h a7) b9 := by
    dsimp only [g]
    rw [hg9]
    have : -10 * octicDepressionR810 h a7 +
        (sourceToRatFunc68 q).coeff 9 / h ^ 9 =
          depressedL810 h (octicDepressionR810 h a7) b9 := by
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    rw [this]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 4) := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial
      (Polynomial.C (-lambda / 4) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hf6 : f.coeff 6 =
      depressedA810 h (octicDepressionR810 h a7) a7 a6 := by
    dsimp only [f, depressedA810, a7, a6]
    rw [hpDep, coeff_depressedOctic68_six]
  have hf5 : f.coeff 5 =
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 := by
    dsimp only [f, depressedB810, a7, a6, a5]
    rw [hpDep, coeff_depressedOctic68_five]
  have hf4 : f.coeff 4 =
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 := by
    dsimp only [f, depressedC810, a7, a6, a5, a4]
    rw [hpDep, coeff_depressedOctic68_four]
  have hf3 : f.coeff 3 =
      depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 := by
    dsimp only [f, depressedD810, a7, a6, a5, a4, a3]
    rw [hpDep, coeff_depressedOctic68_three]
  have hf2 : f.coeff 2 =
      depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 := by
    dsimp only [f, depressedE810, a7, a6, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedOctic68_two]
  have hf1 : f.coeff 1 =
      depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedF810, a7, a6, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedOctic68_one]
  have hf0 : f.coeff 0 =
      depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedG810, a7, a6, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedOctic68_zero]
  have hcoords :
      rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        sourceRhoResidual810 h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5
          b4 b3 b2 b1 := by
    simp only [sourceRhoResidual810]
    rw [hg9L, hf6, hf5, hf4, hf3, hf2, hf1, hf0, hg8', hg7, hg6, hg5,
      hg4, hg3, hg2, hg1]
  have hprim :
      Differential.deriv
          (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 1)) =
        RatFunc.C j / h :=
    rhoResidual810_ratFuncDeriv_eq_simplePole f g j h hf_high hf8 hf7
      hg_high hg10 hLconst (by simpa only [f, g] using hbracket)
  rw [← hcoords]
  exact hprim

#print axioms sourceRhoResidual810_deriv_eq_simplePole_of_source

end DegreeZeroSourceWrapper810

end Max11DegreeRoutes
