import LowScale410ZeroLoadTrajectory

/-!
# Shifted constant fibers for the `(4,10)`, scale-zero leaf

The nonzero value of the first conserved polynomial is easier than the zero
fiber.  In discriminant coordinates it makes both `B` and
`3 U^2 - 8 A B^2` constant.  The terminal one-form is the derivative of the
shifted polynomial `8 B^3 U - c₂ A`, whose forced degree one is incompatible
with the even degree forced on `A`.
-/

noncomputable section

set_option maxHeartbeats 2000000

open Polynomial

namespace Max11DegreeRoutes

section ShiftedFiber410

variable {k : Type*} [Field k] [CharZero k]

/-- Primitive exposed by the terminal row on the first-invariant fiber
`alignedZeroCurveTwoPolynomial410 A B U = C c₂`. -/
def shiftedFiberPrimitive410 (c₂ : k) (A B U : k[X]) : k[X] :=
  (8 : k) • (B ^ 3 * U) - c₂ • A

/-- The terminal form is a derivative plus the first invariant times `A'`.
This identity does not assume that the first invariant is constant. -/
theorem alignedZeroEtaPolynomial410_eq_derivative_sub
    (A B U : k[X]) :
    alignedZeroEtaPolynomial410 A B U =
      (8 : k) • derivative (B ^ 3 * U) -
        alignedZeroCurveTwoPolynomial410 A B U * derivative A := by
  simp only [alignedZeroEtaPolynomial410, alignedZeroCurveTwoPolynomial410,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.smul_eq_C_mul]
  push_cast
  simp only [Polynomial.C_ofNat]
  ring

/-- On a constant first-invariant fiber, the terminal form is exactly the
derivative of the shifted primitive. -/
theorem alignedZeroEtaPolynomial410_eq_shiftedFiberDerivative
    (c₂ : k) (A B U : k[X])
    (hTwo : alignedZeroCurveTwoPolynomial410 A B U = C c₂) :
    alignedZeroEtaPolynomial410 A B U =
      derivative (shiftedFiberPrimitive410 c₂ A B U) := by
  rw [alignedZeroEtaPolynomial410_eq_derivative_sub, hTwo]
  simp only [shiftedFiberPrimitive410, Polynomial.derivative_sub,
    Polynomial.derivative_smul, Polynomial.C_mul']

/-- A polynomial with nonzero constant derivative has degree one. -/
theorem natDegree_eq_one_of_derivative_eq_nonzero_C410
    (P : k[X]) (j : k) (hj : j ≠ 0) (h : derivative P = C j) :
    P.natDegree = 1 := by
  apply natDegree_eq_one_of_scaledDerivative_eq_nonzero_C410 P (8 * j)
  · exact mul_ne_zero (by norm_num) hj
  · rw [h, Polynomial.smul_C]
    congr 1

/-- A nonzero constant first-invariant fiber forces `B` and its companion
factor to be constant polynomials. -/
theorem nonzeroAlignedFiber410_factors_constant
    (A B U : k[X]) (c₂ : k) (hc₂ : c₂ ≠ 0)
    (hTwo : alignedZeroCurveTwoPolynomial410 A B U = C c₂) :
    B.natDegree = 0 ∧
      ((3 : k) • U ^ 2 - (8 : k) • (A * B ^ 2)).natDegree = 0 := by
  have hproduct : B * ((3 : k) • U ^ 2 - (8 : k) • (A * B ^ 2)) = C c₂ := by
    simpa only [alignedZeroCurveTwoPolynomial410] using hTwo
  have hB : B ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hproduct
    exact hc₂ (C_eq_zero.mp hproduct.symm)
  have hH : (3 : k) • U ^ 2 - (8 : k) • (A * B ^ 2) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hproduct
    exact hc₂ (C_eq_zero.mp hproduct.symm)
  have hdegree := congrArg Polynomial.natDegree hproduct
  rw [natDegree_mul hB hH, natDegree_C] at hdegree
  omega

/-- Every nonzero first-invariant fiber is incompatible with a nonzero
constant terminal row.  Notice that the second conserved polynomial is not
needed in this branch. -/
theorem nonzeroAlignedFiber410_trajectory_impossible
    (A B U : k[X]) (c₂ j : k) (hc₂ : c₂ ≠ 0) (hj : j ≠ 0)
    (hTwo : alignedZeroCurveTwoPolynomial410 A B U = C c₂)
    (hEta : alignedZeroEtaPolynomial410 A B U = C j) : False := by
  obtain ⟨hBdegree, hHdegree⟩ :=
    nonzeroAlignedFiber410_factors_constant A B U c₂ hc₂ hTwo
  have hBne : B ≠ 0 := by
    intro hB
    rw [hB, alignedZeroCurveTwoPolynomial410, zero_mul] at hTwo
    exact hc₂ (C_eq_zero.mp hTwo.symm)
  obtain ⟨b, hb⟩ := natDegree_eq_zero.mp hBdegree
  have hbne : b ≠ 0 := by
    intro hb0
    apply hBne
    rw [← hb, hb0, C_0]
  obtain ⟨h, hh⟩ := natDegree_eq_zero.mp hHdegree
  have hH :
      (3 : k) • U ^ 2 - (8 * b ^ 2 : k) • A = C h := by
    calc
      (3 : k) • U ^ 2 - (8 * b ^ 2 : k) • A =
          (3 : k) • U ^ 2 - (8 : k) • (A * B ^ 2) := by
            rw [← hb]
            simp only [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul,
              ← Polynomial.C_pow]
            have hc : C (8 * b ^ 2 : k) = C (8 : k) * C (b ^ 2) := by
              rw [← Polynomial.C_mul]
            linear_combination -A * hc
      _ = C h := hh.symm
  have hcoef : (8 * b ^ 2 : k) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hbne)
  have hscaled : (8 * b ^ 2 : k) • A = (3 : k) • U ^ 2 - C h := by
    linear_combination -hH
  have hAform :
      A = (3 / (8 * b ^ 2) : k) • U ^ 2 - C (h / (8 * b ^ 2)) := by
    calc
      A = (1 / (8 * b ^ 2) : k) • ((8 * b ^ 2 : k) • A) := by
        rw [smul_smul]
        have hone : (1 / (8 * b ^ 2) : k) * (8 * b ^ 2) = 1 := by
          field_simp
        rw [hone, one_smul]
      _ = (1 / (8 * b ^ 2) : k) • ((3 : k) • U ^ 2 - C h) := by
        rw [hscaled]
      _ = (3 / (8 * b ^ 2) : k) • U ^ 2 - C (h / (8 * b ^ 2)) := by
        simp only [smul_sub, smul_smul, Polynomial.smul_C, smul_eq_mul]
        congr 1 <;> field_simp
  have hDerivative : derivative (shiftedFiberPrimitive410 c₂ A B U) = C j := by
    rw [← alignedZeroEtaPolynomial410_eq_shiftedFiberDerivative c₂ A B U hTwo]
    exact hEta
  have hPrimitiveDegree : (shiftedFiberPrimitive410 c₂ A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (shiftedFiberPrimitive410 c₂ A B U) j hj hDerivative
  by_cases hUdegree : U.natDegree = 0
  · obtain ⟨u, hu⟩ := natDegree_eq_zero.mp hUdegree
    have hAconst :
        A = C ((3 / (8 * b ^ 2) : k) * u ^ 2 - h / (8 * b ^ 2)) := by
      rw [hAform, ← hu]
      simp only [← Polynomial.C_pow, Polynomial.smul_C, ← Polynomial.C_sub,
        smul_eq_mul]
    rw [shiftedFiberPrimitive410, ← hb, ← hu, hAconst] at hPrimitiveDegree
    simp only [← Polynomial.C_pow, ← Polynomial.C_mul,
      Polynomial.smul_C, ← Polynomial.C_sub] at hPrimitiveDegree
    rw [natDegree_C] at hPrimitiveDegree
    omega
  · have hUpositive : 0 < U.natDegree := Nat.pos_of_ne_zero hUdegree
    have hUne : U ≠ 0 := by
      intro hU
      subst U
      exact hUdegree natDegree_zero
    have hAlpha : (3 / (8 * b ^ 2) : k) ≠ 0 := by
      exact div_ne_zero (by norm_num) hcoef
    have hAdegree : A.natDegree = 2 * U.natDegree := by
      rw [hAform, natDegree_sub_eq_left_of_natDegree_lt]
      · rw [natDegree_smul (U ^ 2) hAlpha, natDegree_pow]
      · rw [natDegree_C, natDegree_smul (U ^ 2) hAlpha, natDegree_pow]
        omega
    have hFirstDegree :
        ((8 : k) • (B ^ 3 * U)).natDegree = U.natDegree := by
      rw [natDegree_smul (B ^ 3 * U) (by norm_num),
        natDegree_mul (pow_ne_zero 3 hBne) hUne, natDegree_pow, hBdegree]
      omega
    have hSecondDegree : (c₂ • A).natDegree = 2 * U.natDegree := by
      rw [natDegree_smul A hc₂, hAdegree]
    rw [shiftedFiberPrimitive410,
      natDegree_sub_eq_right_of_natDegree_lt] at hPrimitiveDegree
    · rw [hSecondDegree] at hPrimitiveDegree
      omega
    · rw [hFirstDegree, hSecondDegree]
      omega

/-- All constant fibers of the two zero-load first integrals are impossible
when the surviving Jacobian row is a nonzero constant.  The zero first fiber
uses the Fermat reduction from `LowScale410ZeroLoadTrajectory`; the
nonzero first fibers use the shifted primitive above. -/
theorem zeroLoad410_allConstantFibers_trajectory_impossible
    (A B C0 : k[X]) (k₂ k₁ terminal : k) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 = C k₁)
    (hLower : lowerRowZeroPolynomial410
        (zeroLoadWPolynomial410 A B C0) (zeroLoadZPolynomial410 A B C0)
        B C0 = C terminal) : False := by
  by_cases hk₂ : k₂ = 0
  · subst k₂
    apply zeroLoad410_zeroFirstInvariant_trajectory_impossible
      A B C0 k₁ terminal hterminal
    · simpa only [C_0] using hTwo
    · exact hOne
    · exact hLower
  · let U : k[X] := A ^ 2 - (4 : k) • C0
    have hTwoBridge := firstIntegralTwoPolynomial410_zero_discriminant A B C0
    rw [hTwo] at hTwoBridge
    have hTwoAligned : alignedZeroCurveTwoPolynomial410 A B U =
        C ((64 / 5 : k) * k₂) := by
      calc
        alignedZeroCurveTwoPolynomial410 A B U =
            (1 / 5 : k) • ((5 : k) • alignedZeroCurveTwoPolynomial410 A B U) := by
              module
        _ = (1 / 5 : k) • ((64 : k) • C k₂) := by
          rw [← hTwoBridge]
        _ = C ((64 / 5 : k) * k₂) := by
          simp only [smul_smul, Polynomial.smul_C]
          congr 1
          simp only [smul_eq_mul]
          ring
    have hLowerBridge := zeroLoadLowerRow410_discriminant A B C0
    rw [hLower] at hLowerBridge
    have hEtaAligned : alignedZeroEtaPolynomial410 A B U =
        C ((256 / 5 : k) * terminal) := by
      calc
        alignedZeroEtaPolynomial410 A B U =
            (1 / 5 : k) • ((5 : k) • alignedZeroEtaPolynomial410 A B U) := by
              module
        _ = (1 / 5 : k) • ((256 : k) • C terminal) := by
          rw [← hLowerBridge]
        _ = C ((256 / 5 : k) * terminal) := by
          simp only [smul_smul, Polynomial.smul_C]
          congr 1
          simp only [smul_eq_mul]
          ring
    exact nonzeroAlignedFiber410_trajectory_impossible A B U
      ((64 / 5 : k) * k₂) ((256 / 5 : k) * terminal)
      (mul_ne_zero (by norm_num) hk₂)
      (mul_ne_zero (by norm_num) hterminal) hTwoAligned hEtaAligned

end ShiftedFiber410

end Max11DegreeRoutes
