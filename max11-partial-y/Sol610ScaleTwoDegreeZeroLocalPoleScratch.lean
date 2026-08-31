import LowScale68ScaleTwoLocalDerivativeRowTwo

/-! # The local pole-six obstruction for the `(6,10)` degree-zero primitive

This is the minimal analytic consumer needed after the exact order-`69`
source factorization.  If `h^6 rho` is polynomial and `rho'` has only the
simple pole `j/h`, then the coefficient of `rho'` at exponent `-7` is zero.
Formal differentiation says that coefficient is `-6` times the exponent
`-6` boundary coefficient, so the polynomial head must vanish.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section DegreeZeroLocalPole610

variable {k : Type*} [Field k] [CharZero k]

local instance degreeZeroLocalPoleHahnCharZero610 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- A rational function cleared by exactly six powers of a linear local
parameter cannot have a nonzero exponent-`-6` head when its derivative is a
simple pole.  The relevant derivative coefficient is explicitly `-7`. -/
theorem localLinearPoleSix_head_eval_zero_of_deriv_eq_simplePole610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 := by
  obtain ⟨c, hc, hsingle, hscaleDeriv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hrhoBoundary := localHahn_coeff_neg_of_cleared a c h0 A0 rho 6 hc
    hsingle hclear
  have hderivBoundary := localHahn_deriv_coeff_neg_succ_of_cleared
    a c h0 A0 rho 6 hc hsingle hscaleDeriv hclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hderiv
  have hminusSeven :
      (ratFuncAtHahn46 a (Differential.deriv rho)).coeff (-7 : ℚ) = 0 := by
    have hcoeff := congrArg
      (fun z : HahnSeries ℚ k ↦ z.coeff (-7 : ℚ)) hmapped
    simpa only [div_eq_mul_inv, map_mul, map_inv₀, ratFuncAtHahn46_C,
      hsingle,
      HahnSeries.inv_single, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne (by norm_num :
        (-7 : ℚ) ≠ -(1 : ℚ)), smul_zero] using hcoeff
  have hrhoZero : (ratFuncAtHahn46 a rho).coeff (-6 : ℚ) = 0 := by
    norm_num at hderivBoundary
    rw [hminusSeven] at hderivBoundary
    have hsix : (6 : k) ≠ 0 := by norm_num
    have hprod : (6 : k) * (ratFuncAtHahn46 a rho).coeff (-6 : ℚ) = 0 :=
      neg_eq_zero.mp hderivBoundary.symm
    exact (mul_eq_zero.mp hprod).resolve_left hsix
  norm_num at hrhoBoundary
  rw [hrhoZero] at hrhoBoundary
  have hcinv : (c ^ 6)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 6 hc)
  exact (mul_eq_zero.mp hrhoBoundary.symm).resolve_left hcinv

#print axioms localLinearPoleSix_head_eval_zero_of_deriv_eq_simplePole610

end DegreeZeroLocalPole610

end Max11DegreeRoutes
