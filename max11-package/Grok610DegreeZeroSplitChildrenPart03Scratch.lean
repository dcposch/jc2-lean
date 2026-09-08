import Grok610DegreeZeroSourceWrapperScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section LinearDvdAndPoleFive610

variable {k : Type*} [Field k] [CharZero k]

local instance degreeZeroSplitChildrenHahnCharZero610 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- A rational function cleared by exactly five powers of a linear local
parameter cannot have a nonzero exponent-`-5` head when its derivative is a
simple pole. -/
theorem localLinearPoleFive_head_eval_zero_of_deriv_eq_simplePole610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 := by
  obtain ⟨c, hc, hsingle, hscaleDeriv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hrhoBoundary := localHahn_coeff_neg_of_cleared a c h0 A0 rho 5 hc
    hsingle hclear
  have hderivBoundary := localHahn_deriv_coeff_neg_succ_of_cleared
    a c h0 A0 rho 5 hc hsingle hscaleDeriv hclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hderiv
  have hminusSix :
      (ratFuncAtHahn46 a (Differential.deriv rho)).coeff (-6 : ℚ) = 0 := by
    have hcoeff := congrArg
      (fun z : HahnSeries ℚ k ↦ z.coeff (-6 : ℚ)) hmapped
    simpa only [div_eq_mul_inv, map_mul, map_inv₀, ratFuncAtHahn46_C,
      hsingle,
      HahnSeries.inv_single, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne (by norm_num :
        (-6 : ℚ) ≠ -(1 : ℚ)), smul_zero] using hcoeff
  have hrhoZero : (ratFuncAtHahn46 a rho).coeff (-5 : ℚ) = 0 := by
    norm_num at hderivBoundary
    rw [hminusSix] at hderivBoundary
    have hfive : (5 : k) ≠ 0 := by norm_num
    have hprod : (5 : k) * (ratFuncAtHahn46 a rho).coeff (-5 : ℚ) = 0 :=
      neg_eq_zero.mp hderivBoundary.symm
    exact (mul_eq_zero.mp hprod).resolve_left hfive
  norm_num at hrhoBoundary
  rw [hrhoZero] at hrhoBoundary
  have hcinv : (c ^ 5)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 5 hc)
  exact (mul_eq_zero.mp hrhoBoundary.symm).resolve_left hcinv

end LinearDvdAndPoleFive610

end Max11DegreeRoutes
