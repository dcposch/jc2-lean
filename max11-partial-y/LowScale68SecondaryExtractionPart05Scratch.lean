import LowScale68SecondaryExtractionPart04Scratch

/-! # Extracting the first `(6,8)` secondary face

This module connects the abstract scalar face classified in
`LowScale68SecondaryFace` to the literal polynomial lower system.  The four
transverse coordinates have different secondary degree bounds, so the usual
single weighted-boundary lemmas are first replaced by arbitrary-bound
coefficient rules.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryExtraction68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 2000000 in
theorem firstIntegralFourPolynomial68_cubicCoordinates
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X]) :
    firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta A B
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
        cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
          A B c D e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  rw [algebraMap_firstIntegralFourPolynomial68]
  simp only [map_add, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  have hC : (1 / 3 : RatFunc k) *
        (algebraMap k[X] (RatFunc k) A) ^ 2 +
        algebraMap k[X] (RatFunc k) c =
      (algebraMap k[X] (RatFunc k) A) ^ 2 / 3 +
        algebraMap k[X] (RatFunc k) c := by ring
  have hE : (1 / 27 : RatFunc k) *
          (algebraMap k[X] (RatFunc k) A) ^ 3 +
        (1 / 3 : RatFunc k) *
          (algebraMap k[X] (RatFunc k) A *
            algebraMap k[X] (RatFunc k) c) +
        algebraMap k[X] (RatFunc k) e =
      (algebraMap k[X] (RatFunc k) A) ^ 3 / 27 +
        (algebraMap k[X] (RatFunc k) A *
          algebraMap k[X] (RatFunc k) c) / 3 +
        algebraMap k[X] (RatFunc k) e := by ring
  rw [hC, hE]
  rw [firstIntegralFour68_cubicCoordinates]
  simp only [cubicFirstIntegralFourPolynomial68, cubicFirstIntegralFour68,
    map_add, map_sub, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 2000000 in
theorem firstIntegralThreePolynomial68_cubicCoordinates
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X]) :
    firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta A B
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
        cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
          A B c D e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  rw [algebraMap_firstIntegralThreePolynomial68]
  simp only [map_add, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  have hC : (1 / 3 : RatFunc k) *
        (algebraMap k[X] (RatFunc k) A) ^ 2 +
        algebraMap k[X] (RatFunc k) c =
      (algebraMap k[X] (RatFunc k) A) ^ 2 / 3 +
        algebraMap k[X] (RatFunc k) c := by ring
  have hE : (1 / 27 : RatFunc k) *
          (algebraMap k[X] (RatFunc k) A) ^ 3 +
        (1 / 3 : RatFunc k) *
          (algebraMap k[X] (RatFunc k) A *
            algebraMap k[X] (RatFunc k) c) +
        algebraMap k[X] (RatFunc k) e =
      (algebraMap k[X] (RatFunc k) A) ^ 3 / 27 +
        (algebraMap k[X] (RatFunc k) A *
          algebraMap k[X] (RatFunc k) c) / 3 +
        algebraMap k[X] (RatFunc k) e := by ring
  rw [hC, hE]
  rw [firstIntegralThree68_cubicCoordinates]
  simp only [cubicFirstIntegralThreePolynomial68,
    cubicFirstIntegralThree68, map_add, map_sub,
    Polynomial.smul_eq_C_mul, map_mul, map_pow, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

end SecondaryExtraction68
end Max11DegreeRoutes
