import LowScale410EtaThetaAndDegenerate

/-!
# Assembly of the constant-scale `(4,10)` exclusion

The effective-load analysis is now empty once the four earlier loads
`l`, `beta`, `gamma`, and `delta` vanish.  This file assembles that terminal
result first at the polynomial-trajectory interface and then at the fully
integrated rational-function bracket.

The remaining source-side interface is deliberately not hidden here: a raw
normalized `(4,10)` source must still be put into the displayed integrated
normal form, with polynomial coordinates `A`, `B`, `C0`, and the four early
loads must be shown to vanish.
-/

noncomputable section

set_option maxHeartbeats 2000000

open Polynomial

namespace Max11DegreeRoutes

section ScaleZeroAssembly410

variable {k : Type*} [Field k] [CharZero k]

/-- The completed effective-load cascade, exposed at its exact polynomial
trajectory interface.  There are no degree hypotheses and the three
effective loads `zeta`, `eta`, and `theta` are arbitrary. -/
theorem scaleZero410_polynomial_trajectory_impossible
    (alpha epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
      B C0 = C terminal) : False := by
  exact mixedEffective410_original_trajectory_impossible
    alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
      hterminal hTwo hOne hLower

/-- Injectivity of the polynomial embedding turns the rational terminal row
back into a literal polynomial identity. -/
theorem polynomial_lowerRow410_eq_constant_of_ratFunc
    (W Z B C0 : k[X]) (terminal : k)
    (hLower :
      algebraMap k[X] (RatFunc k) W *
          ratFuncDerivation46 (algebraMap k[X] (RatFunc k) C0) -
        algebraMap k[X] (RatFunc k) B *
          ratFuncDerivation46 (algebraMap k[X] (RatFunc k) Z) =
        RatFunc.C terminal) :
    lowerRowZeroPolynomial410 W Z B C0 = C terminal := by
  apply RatFunc.algebraMap_injective k
  rw [algebraMap_lowerRowZeroPolynomial410]
  simpa [RatFunc.algebraMap_C] using hLower

/-- The polynomial representative of `W` agrees with the integrated
rational-function coefficient after embedding. -/
theorem algebraMap_integratedWPolynomial410
    (l alpha beta gamma delta epsilon zeta theta : k)
    (A B C0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
          A B C0) =
      integratedW410 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C theta) := by
  simp only [integratedWPolynomial410, integratedW410, map_add, map_sub,
    map_neg, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_neg, map_ofNat, map_natCast, map_intCast,
    map_one]
  ring

/-- The polynomial representative of `Z` agrees with the integrated
rational-function coefficient after embedding. -/
theorem algebraMap_integratedZPolynomial410
    (l alpha beta gamma delta epsilon zeta eta iota : k)
    (A B C0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
          iota A B C0) =
      integratedZ410 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C iota) := by
  simp only [integratedZPolynomial410, integratedZ410, map_add, map_sub,
    map_neg, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_neg, map_ofNat, map_natCast, map_intCast,
    map_one]
  ring

/-- Smallest rational lower-system adapter needed by the polynomial
elimination: two conserved rational first integrals and the exact terminal
row. -/
theorem scaleZero410_ratFunc_lowerSystem_impossible
    (alpha epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : ratFuncDerivation46
      (firstIntegralTwo410 (RatFunc.C 0)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (RatFunc.C 0) (RatFunc.C 0) (RatFunc.C 0)
        (RatFunc.C zeta) (RatFunc.C eta) (RatFunc.C theta)) = 0)
    (hOne : ratFuncDerivation46
      (firstIntegralOne410 (RatFunc.C 0)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (RatFunc.C 0) (RatFunc.C 0) (RatFunc.C 0)
        (RatFunc.C zeta) (RatFunc.C eta) (RatFunc.C theta)) = 0)
    (hLower :
      algebraMap k[X] (RatFunc k)
          (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0) *
          ratFuncDerivation46 (algebraMap k[X] (RatFunc k) C0) -
        algebraMap k[X] (RatFunc k) B *
          ratFuncDerivation46
            (algebraMap k[X] (RatFunc k)
              (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota
                A B C0)) = RatFunc.C terminal) : False := by
  obtain ⟨k2, k1, hTwoPoly, hOnePoly⟩ :=
    polynomialFirstIntegrals410_exist_constants
      (k := k) 0 0 0 0 zeta eta theta A B C0 hTwo hOne
  have hLowerPoly := polynomial_lowerRow410_eq_constant_of_ratFunc
    (k := k)
    (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
    (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
    B C0 terminal hLower
  exact scaleZero410_polynomial_trajectory_impossible
    alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
      hterminal hTwoPoly hOnePoly hLowerPoly

/-- Strongest currently available source-facing assembly: a nonzero
constant bracket is impossible for the fully integrated scale-zero normal
form once the earlier loads `beta`, `gamma`, and `delta` vanish. -/
theorem scaleZero410_integrated_constantBracket_impossible
    (alpha epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket :
      differentialJacobian ratFuncDerivation46
        (depressedQuartic46
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0))
        (depressedDecic410 0
          (integratedP410 (algebraMap k[X] (RatFunc k) A)
            (RatFunc.C alpha))
          (integratedQ410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B) 0)
          (integratedR410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0)
          (integratedS410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0)
          (integratedT410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0
            (RatFunc.C epsilon))
          (integratedU410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0 0
            (RatFunc.C zeta))
          (integratedV410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0 0
            (RatFunc.C epsilon) (RatFunc.C eta))
          (integratedW410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0 0
            (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C theta))
          (integratedZ410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0 0
            (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
            (RatFunc.C iota))) = C (RatFunc.C terminal)) : False := by
  have hconst (c : k) : ratFuncDerivation46 (RatFunc.C c) = 0 := by
    have hp := ratFuncDerivation46_polynomial (C c : k[X])
    simpa [RatFunc.algebraMap_C] using hp
  obtain ⟨hTwo, hOne, hLower⟩ :=
    integrated410_lowerSystem_of_constantBracket
      (k := k) (F := RatFunc k) ratFuncDerivation46
      0 (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0)
      (RatFunc.C alpha) 0 0 0 (RatFunc.C epsilon)
      (RatFunc.C zeta) (RatFunc.C eta) (RatFunc.C theta)
      (RatFunc.C iota) (RatFunc.C terminal)
      (by simp) (hconst alpha) (by simp) (by simp) (by simp)
      (hconst epsilon) (hconst zeta) (hconst eta) (hconst theta)
      (hconst iota) hbracket
  have hLowerMapped :
      algebraMap k[X] (RatFunc k)
          (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0) *
          ratFuncDerivation46 (algebraMap k[X] (RatFunc k) C0) -
        algebraMap k[X] (RatFunc k) B *
          ratFuncDerivation46
            (algebraMap k[X] (RatFunc k)
              (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota
                A B C0)) = RatFunc.C terminal := by
    rw [algebraMap_integratedWPolynomial410,
      algebraMap_integratedZPolynomial410]
    simpa using hLower
  exact scaleZero410_ratFunc_lowerSystem_impossible
    alpha epsilon zeta eta theta iota terminal A B C0 hterminal
      (by simpa using hTwo) (by simpa using hOne) hLowerMapped

end ScaleZeroAssembly410

end Max11DegreeRoutes
