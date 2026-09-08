import Sol610ScaleTwoDegreeZeroPostCollapseCoordinateBridgeScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareLocalPole610

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareLocalPoleHahnCharZero610 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Per-order head obstruction.  If `h₀ⁿ ρ` is polynomial for `n ≠ 0`
and `ρ'` is the simple pole `C j / h₀`, then the exponent-`-n` Hahn
coefficient of `ρ` vanishes, so the numerator evaluates to zero at the
linear root.  The relevant derivative coefficient is at exponent
`-(n+1)`, which is distinct from `-1`. -/
theorem alignedSquare_localLinearPole_head_eval_zero610
    (n : ℕ) (hn : n ≠ 0) (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 := by
  obtain ⟨c, hc, hsingle, hscaleDeriv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hrhoBoundary := localHahn_coeff_neg_of_cleared a c h0 A0 rho n hc
    hsingle hclear
  have hderivBoundary := localHahn_deriv_coeff_neg_succ_of_cleared
    a c h0 A0 rho n hc hsingle hscaleDeriv hclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hderiv
  have hne : (-(n : ℚ) - 1) ≠ -(1 : ℚ) := by
    intro h
    have : -(n : ℚ) = 0 := by linear_combination h
    exact hn (Nat.cast_eq_zero.mp (neg_eq_zero.mp this))
  have hderivFar :
      (ratFuncAtHahn46 a (Differential.deriv rho)).coeff
        (-(n : ℚ) - 1) = 0 := by
    have hcoeff := congrArg
      (fun z : HahnSeries ℚ k ↦ z.coeff (-(n : ℚ) - 1)) hmapped
    simpa only [div_eq_mul_inv, map_mul, map_inv₀, ratFuncAtHahn46_C,
      hsingle, HahnSeries.inv_single, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne hne,
      smul_zero] using hcoeff
  have hrhoZero : (ratFuncAtHahn46 a rho).coeff (-(n : ℚ)) = 0 := by
    have hnC : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [hderivFar, neg_mul] at hderivBoundary
    have hprod :
        (n : k) * (ratFuncAtHahn46 a rho).coeff (-(n : ℚ)) = 0 :=
      neg_eq_zero.mp hderivBoundary.symm
    exact (mul_eq_zero.mp hprod).resolve_left hnC
  rw [hrhoZero] at hrhoBoundary
  have hcinv : (c ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero n hc)
  exact (mul_eq_zero.mp hrhoBoundary.symm).resolve_left hcinv

end AlignedSquareLocalPole610

end Max11DegreeRoutes
