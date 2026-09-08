import LowScale68SecondaryResidualSelector

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

def testIncidenceDefect68 (B c d e : k[X]) : k[X] :=
  B * e + c * d - (1 / 9 : k) • B ^ 3

theorem testRowTwoIncidence68 (A B c d e : k[X]) :
    secondaryResidualRowTwoPolynomial68 A B c d e =
      (-4 / 27 : k) •
        (-(6 : k) • (A * derivative (testIncidenceDefect68 B c d e)) +
          (3 : k) • (derivative A * testIncidenceDefect68 B c d e) -
          (2 : k) • (A * B ^ 2 * derivative B) -
          (2 / 3 : k) • (derivative A * B ^ 3) +
          (6 : k) • derivative (B ^ 2 * d) +
          (6 : k) • derivative (B * c ^ 2) -
          (18 : k) • derivative (d * e)) := by
  unfold secondaryResidualRowTwoPolynomial68
  apply congrArg (fun p : k[X] => (-4 / 27 : k) • p)
  simp only [testIncidenceDefect68, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_C, zero_mul, zero_add,
    one_mul, Polynomial.smul_eq_C_mul, map_neg, map_div₀, map_ofNat,
    map_one]
  norm_num [← map_mul]
  ring

#print axioms testRowTwoIncidence68

end Max11DegreeRoutes
