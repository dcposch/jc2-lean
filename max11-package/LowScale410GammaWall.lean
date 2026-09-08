import LowScale410LWallUnconditional

/-!
# The pure gamma wall for the `(4,10)`, scale-zero leaf

We take `l = beta = delta = zeta = eta = theta = 0` and `gamma ≠ 0`.
After shifting `U` by `8 gamma / 5`, the two invariants and terminal row
become a constant-fiber variant of the zero-load trajectory system.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Polynomial

namespace Max11DegreeRoutes

section GammaWall410

variable {k : Type*} [Field k] [CharZero k]

private theorem C_eq_smul_one_gamma410 (x : k) :
    C x = x • (1 : k[X]) := by
  simp [Algebra.smul_def, Polynomial.C_eq_algebraMap]

def gammaCoreTwo410 (gamma : k) (A B U : k[X]) : k[X] :=
  (3 : k) • U ^ 2 - (48 / 5 * gamma : k) • U -
    (8 : k) • (A * B ^ 2)

def gammaCurveTwo410 (gamma : k) (A B U : k[X]) : k[X] :=
  B * gammaCoreTwo410 gamma A B U

def gammaCurveOne410 (gamma : k) (A B U : k[X]) : k[X] :=
  (24 : k) • (A * B ^ 2 * U) -
    (192 / 5 * gamma : k) • (A * B ^ 2) -
    (8 : k) • B ^ 4 - U ^ 3 + (24 / 5 * gamma : k) • U ^ 2

def gammaTerminalPrimitive410 (gamma : k) (B U : k[X]) : k[X] :=
  (1280 : k) • (B ^ 3 * U) - (2048 * gamma : k) • B ^ 3

def gammaFiberPrimitive410 (gamma k₂ : k) (A B U : k[X]) : k[X] :=
  gammaTerminalPrimitive410 gamma B U - k₂ • A

theorem discriminantInvariantTwoNumerator410_gamma_shift
    (gamma : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410 0 0 gamma 0 0 0 0 A B U =
      (160 : k) • gammaCurveTwo410 gamma A B U := by
  simp only [discriminantInvariantTwoNumerator410, gammaCurveTwo410,
    gammaCoreTwo410, zero_mul, mul_zero, zero_smul, add_zero, sub_zero,
    mul_sub, mul_smul_comm, smul_smul]
  have hmonomial : B * (A * B ^ 2) = A * B ^ 3 := by ring
  rw [hmonomial]
  module

theorem discriminantInvariantOneNumerator410_gamma_shift
    (gamma : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 0 0 gamma 0 0 0 0 A B U =
      (40 : k) • gammaCurveOne410 gamma A B U := by
  simp only [discriminantInvariantOneNumerator410, gammaCurveOne410,
    zero_mul, zero_smul, add_zero, sub_zero]
  module

theorem lWallTerminalNumerator410_gamma_eq_derivative_sub
    (gamma : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 0 gamma 0 0 0 0 A B U =
      derivative (gammaTerminalPrimitive410 gamma B U) -
        discriminantInvariantTwoNumerator410 0 0 gamma 0 0 0 0 A B U *
          derivative A := by
  have hPrimitiveDerivative :
      derivative (gammaTerminalPrimitive410 gamma B U) =
        (3840 : k) • (B ^ 2 * U * derivative B) +
          (1280 : k) • (B ^ 3 * derivative U) -
            (6144 * gamma : k) • (B ^ 2 * derivative B) := by
    simp only [gammaTerminalPrimitive410, Polynomial.derivative_sub,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.derivative_smul, Polynomial.derivative_C,
      Polynomial.smul_eq_C_mul]
    push_cast
    simp only [Polynomial.C_ofNat, zero_mul, mul_zero, add_zero]
    ring_nf
    have hC (x : k) : Polynomial.C x = x • (1 : k[X]) := by
      simp [Algebra.smul_def, Polynomial.C_eq_algebraMap]
    have h3 : (3 : k[X]) = (3 : k) • (1 : k[X]) := by
      rw [← hC]
      exact (Polynomial.C_ofNat 3).symm
    simp only [hC, pow_two, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_smul, _root_.smul_pow, one_pow]
    rw [h3]
    simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
    module
  have hA : lWallTerminalACoefficient410
      0 0 gamma 0 0 0 0 A B U =
        -discriminantInvariantTwoNumerator410 0 0 gamma 0 0 0 0 A B U := by
    simp only [lWallTerminalACoefficient410,
      discriminantInvariantTwoNumerator410, zero_mul, mul_zero, zero_smul,
      add_zero, sub_zero]
    module
  have hB : lWallTerminalBCoefficient410 0 0 gamma 0 0 A B U =
      (3840 : k) • (B ^ 2 * U) - (6144 * gamma : k) • B ^ 2 := by
    simp only [lWallTerminalBCoefficient410, zero_mul, mul_zero, zero_smul,
      add_zero, sub_zero]
    module
  have hU : lWallTerminalUCoefficient410 0 0 0 0 0 A B U =
      (1280 : k) • B ^ 3 := by
    simp only [lWallTerminalUCoefficient410, zero_mul, mul_zero, zero_smul,
      add_zero, sub_zero, neg_zero, Polynomial.C_0]
    simp only [zero_add]
  simp only [lWallTerminalNumerator410]
  rw [hA, hB, hU, hPrimitiveDerivative]
  simp only [neg_mul, sub_mul, add_mul, smul_mul_assoc]
  abel_nf

theorem lWallTerminalNumerator410_gamma_eq_fiberDerivative
    (gamma k₂ : k) (A B U : k[X])
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 0 0 0 A B U = C k₂) :
    lWallTerminalNumerator410 0 0 gamma 0 0 0 0 A B U =
      derivative (gammaFiberPrimitive410 gamma k₂ A B U) := by
  rw [lWallTerminalNumerator410_gamma_eq_derivative_sub, hTwo]
  simp only [gammaFiberPrimitive410, Polynomial.derivative_sub,
    Polynomial.derivative_smul, Polynomial.C_mul']

theorem gammaCurveOne410_of_core_zero
    (gamma : k) (A B U : k[X])
    (hcore : gammaCoreTwo410 gamma A B U = 0) :
    gammaCurveOne410 gamma A B U =
      (8 : k) • (U ^ 3 - B ^ 4) -
        (192 / 5 * gamma : k) • U ^ 2 +
          (1152 / 25 * gamma ^ 2 : k) • U := by
  have hAB : (8 : k) • (A * B ^ 2) =
      (3 : k) • U ^ 2 - (48 / 5 * gamma : k) • U := by
    simp only [gammaCoreTwo410] at hcore
    linear_combination -hcore
  have hABU : (24 : k) • (A * B ^ 2 * U) =
      (9 : k) • U ^ 3 - (144 / 5 * gamma : k) • U ^ 2 := by
    calc
      (24 : k) • (A * B ^ 2 * U) =
          (3 : k) • (((8 : k) • (A * B ^ 2)) * U) := by
            simp only [smul_mul_assoc, smul_smul]
            module
      _ = (3 : k) •
          (((3 : k) • U ^ 2 - (48 / 5 * gamma : k) • U) * U) := by
            rw [hAB]
      _ = (9 : k) • U ^ 3 -
          (144 / 5 * gamma : k) • U ^ 2 := by
            simp only [sub_mul, smul_sub, smul_mul_assoc, smul_smul]
            rw [show U ^ 2 * U = U ^ 3 by ring]
            rw [show U * U = U ^ 2 by ring]
            module
  have hGammaAB : (192 / 5 * gamma : k) • (A * B ^ 2) =
      (72 / 5 * gamma : k) • U ^ 2 -
        (1152 / 25 * gamma ^ 2 : k) • U := by
    calc
      (192 / 5 * gamma : k) • (A * B ^ 2) =
          (24 / 5 * gamma : k) • ((8 : k) • (A * B ^ 2)) := by
            simp only [smul_smul]
            module
      _ = (24 / 5 * gamma : k) •
          ((3 : k) • U ^ 2 - (48 / 5 * gamma : k) • U) := by rw [hAB]
      _ = (72 / 5 * gamma : k) • U ^ 2 -
          (1152 / 25 * gamma ^ 2 : k) • U := by
            simp only [smul_sub, smul_smul]
            module
  simp only [gammaCurveOne410]
  rw [hABU, hGammaAB]
  module

theorem gammaTerminalPrimitive410_factor
    (gamma : k) (B U : k[X]) :
    gammaTerminalPrimitive410 gamma B U =
      B ^ 3 * ((1280 : k) • U - (2048 * gamma : k) • (1 : k[X])) := by
  simp only [gammaTerminalPrimitive410, mul_sub, mul_smul_comm, mul_one]

theorem gammaOnly410_discriminant_trajectory_impossible
    (gamma k₂ k₁ terminal : k) (A B U : k[X])
    (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 0 0 0 A B U = C k₂)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma 0 0 0 0 A B U = C k₁)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma 0 0 0 0 A B U = C terminal) : False := by
  have hProduct : (160 : k) • (B * gammaCoreTwo410 gamma A B U) = C k₂ := by
    have ht := hTwo
    rw [discriminantInvariantTwoNumerator410_gamma_shift] at ht
    simpa only [gammaCurveTwo410] using ht
  have hDerivative : derivative (gammaFiberPrimitive410 gamma k₂ A B U) =
      C terminal := by
    rw [← lWallTerminalNumerator410_gamma_eq_fiberDerivative
      gamma k₂ A B U hTwo]
    exact hTerminal
  have hPrimitiveDegree :
      (gammaFiberPrimitive410 gamma k₂ A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (gammaFiberPrimitive410 gamma k₂ A B U) terminal hterminal hDerivative
  by_cases hk₂ : k₂ = 0
  · subst k₂
    simp only [C_0] at hProduct
    have hProductZero : B * gammaCoreTwo410 gamma A B U = 0 :=
      (smul_eq_zero.mp hProduct).resolve_left (by norm_num)
    by_cases hBzero : B = 0
    · subst B
      simp [gammaFiberPrimitive410, gammaTerminalPrimitive410] at hDerivative
      exact hterminal (C_eq_zero.mp hDerivative.symm)
    · have hBne : B ≠ 0 := hBzero
      have hCoreZero : gammaCoreTwo410 gamma A B U = 0 :=
        (mul_eq_zero.mp hProductZero).resolve_left hBzero
      simp only [gammaFiberPrimitive410, zero_smul, sub_zero] at hPrimitiveDegree
      rw [gammaTerminalPrimitive410_factor] at hPrimitiveDegree
      have hFactorNe :
          (1280 : k) • U - (2048 * gamma : k) • (1 : k[X]) ≠ 0 := by
        intro hzero
        rw [hzero, mul_zero, natDegree_zero] at hPrimitiveDegree
        omega
      rw [natDegree_mul (pow_ne_zero 3 hBne) hFactorNe, natDegree_pow]
        at hPrimitiveDegree
      have hBdegree : B.natDegree = 0 := by omega
      have hFactorDegree :
          ((1280 : k) • U - (2048 * gamma : k) • (1 : k[X])).natDegree = 1 := by
        omega
      have hUdegree : U.natDegree = 1 := by
        by_cases hU0 : U.natDegree = 0
        · have hFactorLe :
              ((1280 : k) • U - (2048 * gamma : k) • (1 : k[X])).natDegree ≤ 0 := by
            compute_degree
            omega
          omega
        · have hUpos : 0 < U.natDegree := by omega
          have hLead : ((1280 : k) • U).natDegree = U.natDegree := by
            rw [natDegree_smul U (by norm_num)]
          have hConst : ((2048 * gamma : k) • (1 : k[X])).natDegree <
              U.natDegree := by
            compute_degree
            omega
          have hDegree :
              ((1280 : k) • U - (2048 * gamma : k) • (1 : k[X])).natDegree =
                U.natDegree := by
            have hConst' : ((2048 * gamma : k) • (1 : k[X])).natDegree <
                ((1280 : k) • U).natDegree := by
              rw [hLead]
              exact hConst
            rw [natDegree_sub_eq_left_of_natDegree_lt hConst', hLead]
          omega
      have hReduced := gammaCurveOne410_of_core_zero gamma A B U hCoreZero
      have hU3degree : (U ^ 3).natDegree = 3 := by
        rw [natDegree_pow, hUdegree]
      have hB4degree : (B ^ 4).natDegree = 0 := by
        rw [natDegree_pow, hBdegree]
      have hDifferenceDegree : (U ^ 3 - B ^ 4).natDegree = 3 := by
        rw [natDegree_sub_eq_left_of_natDegree_lt]
        · exact hU3degree
        · omega
      have hMainDegree : ((8 : k) • (U ^ 3 - B ^ 4)).natDegree = 3 := by
        rw [natDegree_smul _ (by norm_num), hDifferenceDegree]
      have hLowerDegree :
          ((192 / 5 * gamma : k) • U ^ 2 -
            (1152 / 25 * gamma ^ 2 : k) • U).natDegree < 3 := by
        compute_degree
        omega
      have hCurveDegree : (gammaCurveOne410 gamma A B U).natDegree = 3 := by
        rw [hReduced]
        have hForm :
            (8 : k) • (U ^ 3 - B ^ 4) -
                (192 / 5 * gamma : k) • U ^ 2 +
              (1152 / 25 * gamma ^ 2 : k) • U =
            (8 : k) • (U ^ 3 - B ^ 4) -
              ((192 / 5 * gamma : k) • U ^ 2 -
                (1152 / 25 * gamma ^ 2 : k) • U) := by abel
        have hLowerDegree' :
            ((192 / 5 * gamma : k) • U ^ 2 -
              (1152 / 25 * gamma ^ 2 : k) • U).natDegree <
              ((8 : k) • (U ^ 3 - B ^ 4)).natDegree := by
          rw [hMainDegree]
          exact hLowerDegree
        rw [hForm, natDegree_sub_eq_left_of_natDegree_lt hLowerDegree',
          hMainDegree]
      have hOneDegree := congrArg Polynomial.natDegree hOne
      rw [discriminantInvariantOneNumerator410_gamma_shift,
        natDegree_smul _ (by norm_num), hCurveDegree, natDegree_C] at hOneDegree
      omega
  · have hProductNe : B * gammaCoreTwo410 gamma A B U ≠ 0 := by
      intro hzero
      rw [hzero, smul_zero] at hProduct
      exact hk₂ (C_eq_zero.mp hProduct.symm)
    have hBne : B ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hProductNe
      exact hProductNe rfl
    have hCoreNe : gammaCoreTwo410 gamma A B U ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hProductNe
      exact hProductNe rfl
    have hProductDegree := congrArg Polynomial.natDegree hProduct
    rw [natDegree_smul _ (by norm_num), natDegree_mul hBne hCoreNe,
      natDegree_C] at hProductDegree
    have hBdegree : B.natDegree = 0 := by omega
    have hCoreDegree : (gammaCoreTwo410 gamma A B U).natDegree = 0 := by omega
    obtain ⟨b, hb⟩ := natDegree_eq_zero.mp hBdegree
    have hbne : b ≠ 0 := by
      intro hbzero
      apply hBne
      rw [← hb, hbzero, C_0]
    obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hCoreDegree
    have hcoef : (8 * b ^ 2 : k) ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hbne)
    have hScaledA : (8 * b ^ 2 : k) • A =
        (3 : k) • U ^ 2 - (48 / 5 * gamma : k) • U - C c := by
      have hBsq : (8 * b ^ 2 : k) • A = (8 : k) • (A * B ^ 2) := by
        rw [← hb]
        simp only [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul,
          ← Polynomial.C_pow]
        have hc8 : C (8 * b ^ 2 : k) = C (8 : k) * C (b ^ 2) := by
          rw [← C_mul]
        linear_combination A * hc8
      rw [hBsq]
      simp only [gammaCoreTwo410] at hc
      linear_combination hc
    by_cases hUzeroDegree : U.natDegree = 0
    · have hRightDegree :
          ((3 : k) • U ^ 2 - (48 / 5 * gamma : k) • U - C c).natDegree = 0 := by
        have hle :
            ((3 : k) • U ^ 2 - (48 / 5 * gamma : k) • U - C c).natDegree ≤
              0 := by
          compute_degree
          omega
        omega
      have hAdegree := congrArg Polynomial.natDegree hScaledA
      rw [natDegree_smul A hcoef, hRightDegree] at hAdegree
      have hPrimitiveLe :
          (gammaFiberPrimitive410 gamma k₂ A B U).natDegree ≤ 0 := by
        simp only [gammaFiberPrimitive410, gammaTerminalPrimitive410]
        compute_degree
        omega
      omega
    · have hUpos : 0 < U.natDegree := by omega
      have hRestDegree :
          ((48 / 5 * gamma : k) • U + C c).natDegree < 2 * U.natDegree := by
        compute_degree
        omega
      have hLeadDegree : ((3 : k) • U ^ 2).natDegree = 2 * U.natDegree := by
        rw [natDegree_smul _ (by norm_num), natDegree_pow]
      have hScaledAForm : (8 * b ^ 2 : k) • A =
          (3 : k) • U ^ 2 - ((48 / 5 * gamma : k) • U + C c) := by
        linear_combination hScaledA
      have hAdegree : A.natDegree = 2 * U.natDegree := by
        have hDegree := congrArg Polynomial.natDegree hScaledAForm
        have hRestDegree' :
            ((48 / 5 * gamma : k) • U + C c).natDegree <
              ((3 : k) • U ^ 2).natDegree := by
          rw [hLeadDegree]
          exact hRestDegree
        rw [natDegree_smul A hcoef,
          natDegree_sub_eq_left_of_natDegree_lt hRestDegree', hLeadDegree]
          at hDegree
        exact hDegree
      have hGammaPrimitiveDegree :
          (gammaTerminalPrimitive410 gamma B U).natDegree = U.natDegree := by
        simp only [gammaTerminalPrimitive410]
        have hFirstDegree : ((1280 : k) • (B ^ 3 * U)).natDegree =
            U.natDegree := by
          rw [natDegree_smul _ (by norm_num),
            natDegree_mul (pow_ne_zero 3 hBne) (by
              intro hzero
              subst U
              simp at hUpos), natDegree_pow, hBdegree]
          omega
        have hSecondDegree : ((2048 * gamma : k) • B ^ 3).natDegree <
            U.natDegree := by
          compute_degree
          omega
        have hSecondDegree' : ((2048 * gamma : k) • B ^ 3).natDegree <
            ((1280 : k) • (B ^ 3 * U)).natDegree := by
          rw [hFirstDegree]
          exact hSecondDegree
        rw [natDegree_sub_eq_left_of_natDegree_lt hSecondDegree', hFirstDegree]
      have hSecondPrimitiveDegree : (k₂ • A).natDegree = 2 * U.natDegree := by
        rw [natDegree_smul A hk₂, hAdegree]
      have hFiberDegree : (gammaFiberPrimitive410 gamma k₂ A B U).natDegree =
          2 * U.natDegree := by
        simp only [gammaFiberPrimitive410]
        rw [natDegree_sub_eq_right_of_natDegree_lt, hSecondPrimitiveDegree]
        rw [hGammaPrimitiveDegree]
        omega
      omega

/-- No degree assumptions are needed on the pure `gamma` wall: if all
effective loads except `gamma` vanish, the two constant first integrals and
a nonzero terminal row are incompatible.  The formally present loads
`alpha`, `epsilon`, and `iota` cancel through the discriminant bridges. -/
theorem gammaOnly410_original_trajectory_impossible
    (alpha gamma epsilon iota k₂ k₁ terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma 0 0 0 0 A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma 0 0 0 0 A B C0 = C k₁)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma 0 epsilon 0 0 A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma 0 epsilon 0 0 iota A B C0)
      B C0 = C terminal) : False := by
  have hTwoD :
      discriminantInvariantTwoNumerator410 0 0 gamma 0 0 0 0 A B
          (A ^ 2 - (4 : k) • C0) = C (2048 * k₂) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD :
      discriminantInvariantOneNumerator410 0 0 gamma 0 0 0 0 A B
          (A ^ 2 - (4 : k) • C0) = C (2048 * k₁) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD :
      lWallTerminalNumerator410 0 0 gamma 0 0 0 0 A B
          (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact gammaOnly410_discriminant_trajectory_impossible
    gamma (2048 * k₂) (2048 * k₁) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) (mul_ne_zero (by norm_num) hterminal)
        hTwoD hOneD hTerminalD

/-- Exact residual after closing the pure `gamma` wall.  On `l = beta = 0`,
any constant-integral trajectory with nonzero terminal row must carry one of
the four later effective loads. -/
theorem gammaWall410_laterEffectiveLoad_residual
    (alpha gamma delta epsilon zeta eta theta iota k₂ k₁ terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k₁)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta iota
        A B C0) B C0 = C terminal) :
    delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0 := by
  by_contra hlater
  push_neg at hlater
  obtain ⟨hdelta, hzeta, heta, htheta⟩ := hlater
  subst delta
  subst zeta
  subst eta
  subst theta
  exact gammaOnly410_original_trajectory_impossible
    alpha gamma epsilon iota k₂ k₁ terminal A B C0 hterminal
      hTwo hOne hLower

end GammaWall410

end Max11DegreeRoutes
