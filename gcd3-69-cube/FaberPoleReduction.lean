import FaberLowerRows

noncomputable section
open Polynomial

/-! # Faber terminal pole reduction

The literal fifth lower row gives a reduced rational primitive of `j/(6s)`.
This module packages its canonical numerator and denominator and applies the
finite-place classification already proved in `Solution`.
-/

/-- Canonical reduced polynomial data for the terminal Faber invariant of a
literal polynomial source. -/
structure GCD369CubeFaberPrimitiveData
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) where
  numerator : k[X]
  denominator : k[X]
  hnumerator : numerator ≠ 0
  hdenominator : denominator ≠ 0
  hvalue :
    GCD369CubeFaberR5
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        S.faberNormalForm.d S.faberNormalForm.c7
        S.faberNormalForm.c5 S.faberNormalForm.c4
        S.faberNormalForm.c3 S.faberNormalForm.c2
        S.faberNormalForm.c1 =
      algebraMap k[X] (RatFunc k) numerator /
        algebraMap k[X] (RatFunc k) denominator
  hreduced : ∀ z : k, eval z numerator = 0 → eval z denominator ≠ 0
  hODE :
    S.s *
        (derivative numerator * denominator -
          numerator * derivative denominator) =
      C (S.j / 6) * denominator ^ 2

namespace GCD369CubePolynomialSource

/-- The fifth Faber invariant of a literal source, for concise statements
inside the pole reduction. -/
noncomputable def terminalFaberInvariant
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) : RatFunc k :=
  GCD369CubeFaberR5
    (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
    (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
    (S.normalizedP.coeff 4)
    S.faberNormalForm.d S.faberNormalForm.c7
    S.faberNormalForm.c5 S.faberNormalForm.c4
    S.faberNormalForm.c3 S.faberNormalForm.c2
    S.faberNormalForm.c1

/-- The literal lower row proves that reduced rational-primitive data exist. -/
theorem faberPrimitiveData_nonempty
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    Nonempty (GCD369CubeFaberPrimitiveData S) := by
  let r5 := S.terminalFaberInvariant
  obtain ⟨N, B, hB, hvalue, hreduced⟩ :=
    GCD369CubeRatFuncReducedPresentation r5
  have hrow := S.faberLowerRows
  have hrow5 :
      6 * GCD369CubeRatFuncDerivative r5 =
        algebraMap k (RatFunc k) S.j / S.sRat := by
    simpa only [r5, terminalFaberInvariant] using hrow.2.2.2.2
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  have hterminal :
      S.sRat * GCD369CubeRatFuncDerivative r5 =
        algebraMap k (RatFunc k) (S.j / 6) := by
    calc
      S.sRat * GCD369CubeRatFuncDerivative r5 =
          S.sRat * (6 * GCD369CubeRatFuncDerivative r5) / 6 := by ring
      _ = S.sRat * (algebraMap k (RatFunc k) S.j / S.sRat) / 6 := by
        rw [hrow5]
      _ = algebraMap k (RatFunc k) (S.j / 6) := by
        rw [map_div₀, map_ofNat]
        field_simp [hsRat]
  have hj6 : S.j / 6 ≠ 0 := div_ne_zero S.hj (by norm_num)
  have hj6map : algebraMap k (RatFunc k) (S.j / 6) ≠ 0 := by
    rw [RatFunc.algebraMap_eq_C]
    simpa using RatFunc.C_injective.ne hj6
  have hr5Derivative : GCD369CubeRatFuncDerivative r5 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hterminal
    exact hj6map hterminal.symm
  have hr5 : r5 ≠ 0 := by
    intro hz
    rw [hz, GCD369CubeRatFuncDerivative_zero] at hr5Derivative
    exact hr5Derivative rfl
  have hN : N ≠ 0 := by
    intro hz
    apply hr5
    rw [hvalue, hz, map_zero, zero_div]
  have hderivative := congrArg GCD369CubeRatFuncDerivative hvalue
  rw [GCD369CubeRatFuncDerivative_div N B hB] at hderivative
  rw [hderivative] at hterminal
  have hODE :
      S.s * (derivative N * B - N * derivative B) =
        C (S.j / 6) * B ^ 2 := by
    apply RatFunc.algebraMap_injective k
    have hBmap : algebraMap k[X] (RatFunc k) B ≠ 0 :=
      RatFunc.algebraMap_ne_zero hB
    change algebraMap k[X] (RatFunc k) S.s *
        ((algebraMap k[X] (RatFunc k) B *
              algebraMap k[X] (RatFunc k) (derivative N) -
            algebraMap k[X] (RatFunc k) N *
              algebraMap k[X] (RatFunc k) (derivative B)) /
          algebraMap k[X] (RatFunc k) B ^ 2) =
      algebraMap k (RatFunc k) (S.j / 6) at hterminal
    field_simp [hBmap] at hterminal
    simp only [map_mul, map_sub, map_pow, RatFunc.algebraMap_C]
    rw [← RatFunc.algebraMap_eq_C]
    simpa only [mul_comm] using hterminal
  exact ⟨
    { numerator := N
      denominator := B
      hnumerator := hN
      hdenominator := hB
      hvalue := by simpa only [r5, terminalFaberInvariant] using hvalue
      hreduced := hreduced
      hODE := hODE }⟩

/-- The canonical choice of reduced rational-primitive data. -/
noncomputable def faberPrimitiveData
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    GCD369CubeFaberPrimitiveData S :=
  Classical.choice S.faberPrimitiveData_nonempty

/-- If the polynomial cube root is nonconstant, the terminal primitive
forces it and the reduced denominator to be powers at one finite place. -/
theorem faberPrimitive_nonconstantCore
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : 0 < S.s.natDegree) :
    let P := S.faberPrimitiveData
    ∃ a : k, ∃ m : ℕ, 2 ≤ m ∧
      S.s = C S.s.leadingCoeff * (X - C a) ^ m ∧
      P.denominator =
        C P.denominator.leadingCoeff * (X - C a) ^ (m - 1) := by
  let P := S.faberPrimitiveData
  change ∃ a : k, ∃ m : ℕ, 2 ≤ m ∧
    S.s = C S.s.leadingCoeff * (X - C a) ^ m ∧
    P.denominator =
      C P.denominator.leadingCoeff * (X - C a) ^ (m - 1)
  exact GCD369CubeRationalPrimitiveNonconstantCore
    S.s P.numerator P.denominator (S.j / 6)
    S.hs P.hnumerator P.hdenominator (div_ne_zero S.hj (by norm_num))
    hsdegree P.hreduced P.hODE

/-- If the polynomial cube root is constant, the same primitive has constant
denominator and affine numerator. -/
theorem faberPrimitive_constantCore
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    let P := S.faberPrimitiveData
    P.denominator.natDegree = 0 ∧ P.numerator.natDegree = 1 := by
  let P := S.faberPrimitiveData
  change P.denominator.natDegree = 0 ∧ P.numerator.natDegree = 1
  exact GCD369CubeRationalPrimitiveConstantCore
    S.s P.numerator P.denominator (S.j / 6)
    S.hs P.hnumerator P.hdenominator (div_ne_zero S.hj (by norm_num))
    hsdegree P.hreduced P.hODE

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.faberPrimitiveData
#print axioms GCD369CubePolynomialSource.faberPrimitive_nonconstantCore
#print axioms GCD369CubePolynomialSource.faberPrimitive_constantCore
