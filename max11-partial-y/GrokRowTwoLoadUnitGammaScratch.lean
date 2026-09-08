import GrokRowTwoLoadUnitBaseScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
section UnitGamma
variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 4000000 in
theorem loadUnitGamma68
    (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 1 0 0 0 0 A B c ((1 / 3 : k) • (A * B) + d) e =
      cubicLoadRowTwoTranslatedPolynomial68 0 0 1 0 0 0 A B c d e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
  cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
  cubicLoadRowTwoTranslatedPolynomial68, derivative_add, derivative_sub,
  derivative_mul, derivative_pow, derivative_C, zero_mul, mul_zero,
  zero_add, add_zero, one_mul, mul_one, zero_smul, smul_zero, one_smul,
  Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
  map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
  map_zero]
  ring
end UnitGamma
end Max11DegreeRoutes
