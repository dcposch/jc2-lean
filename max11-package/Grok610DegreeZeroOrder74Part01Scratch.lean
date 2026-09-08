import Grok610DegreeZeroOrder73Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section LinearPoleOne610

variable {k : Type*} [Field k] [CharZero k]

local instance degreeZeroOrder74HahnCharZero610 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- A rational function cleared by exactly one power of a linear local
parameter cannot have a nonzero exponent-`-1` head when its derivative is a
simple pole. -/
theorem localLinearPoleOne_head_eval_zero_of_deriv_eq_simplePole610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 1 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 := by
  obtain ⟨c, hc, hsingle, hscaleDeriv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hrhoBoundary := localHahn_coeff_neg_of_cleared a c h0 A0 rho 1 hc
    hsingle hclear
  have hderivBoundary := localHahn_deriv_coeff_neg_succ_of_cleared
    a c h0 A0 rho 1 hc hsingle hscaleDeriv hclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hderiv
  have hminusTwo :
      (ratFuncAtHahn46 a (Differential.deriv rho)).coeff (-2 : ℚ) = 0 := by
    have hcoeff := congrArg
      (fun z : HahnSeries ℚ k ↦ z.coeff (-2 : ℚ)) hmapped
    simpa only [div_eq_mul_inv, map_mul, map_inv₀, ratFuncAtHahn46_C,
      hsingle,
      HahnSeries.inv_single, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne (by norm_num :
        (-2 : ℚ) ≠ -(1 : ℚ)), smul_zero] using hcoeff
  have hrhoZero : (ratFuncAtHahn46 a rho).coeff (-1 : ℚ) = 0 := by
    norm_num at hderivBoundary
    rw [hminusTwo] at hderivBoundary
    exact neg_eq_zero.mp hderivBoundary.symm
  norm_num at hrhoBoundary
  rw [hrhoZero] at hrhoBoundary
  have hcinv : c⁻¹ ≠ 0 := inv_ne_zero hc
  exact (mul_eq_zero.mp hrhoBoundary.symm).resolve_left hcinv

end LinearPoleOne610

end Max11DegreeRoutes
