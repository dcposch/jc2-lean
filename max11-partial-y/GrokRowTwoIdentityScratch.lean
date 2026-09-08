import LowScale68SecondaryResidualExtraction

/-! Scratch kernel check of `secondaryResidualRowTwoPolynomial68_incidenceDefect`.

This file is intentionally independent of `LowScale68SecondaryResidualDescent`
so the failing `module` proof is not imported.  The incidence-defect
polynomial is copied verbatim from that module. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RowTwoIncidenceScratch

variable {k : Type*} [Field k] [CharZero k]

/-- Copied verbatim from `LowScale68SecondaryResidualDescent`. -/
def secondaryResidualIncidenceDefectPolynomial68
    (B c d e : k[X]) : k[X] :=
  B * e + c * d - (1 / 9 : k) • B ^ 3

set_option maxHeartbeats 8000000 in
/-- The first residual one-form, rewritten through the normalized incidence
defect.  This identity separates the next comparison `2h` versus `3g`: all
terms involving the incidence defect are already below the latter face. -/
theorem secondaryResidualRowTwoPolynomial68_incidenceDefect
    (A B c d e : k[X]) :
    secondaryResidualRowTwoPolynomial68 A B c d e =
      (-4 / 27 : k) •
        (-(6 : k) •
            (A * derivative
              (secondaryResidualIncidenceDefectPolynomial68 B c d e)) +
          (3 : k) •
            (derivative A *
              secondaryResidualIncidenceDefectPolynomial68 B c d e) -
          (2 : k) • (A * B ^ 2 * derivative B) -
          (2 / 3 : k) • (derivative A * B ^ 3) +
          (6 : k) • derivative (B ^ 2 * d) +
          (6 : k) • derivative (B * c ^ 2) -
          (18 : k) • derivative (d * e)) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [secondaryResidualRowTwoPolynomial68,
    secondaryResidualIncidenceDefectPolynomial68,
    derivative_mul, derivative_pow, derivative_C,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add,
    map_sub, map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

#print axioms secondaryResidualRowTwoPolynomial68_incidenceDefect

end RowTwoIncidenceScratch

end Max11DegreeRoutes
