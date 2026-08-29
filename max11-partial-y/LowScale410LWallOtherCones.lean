import LowScale410LWallResidual

/-!
# Remaining degree cones on the `(4,10)`, scale-zero nonic wall

Write `a = deg A`, `b = deg B`, and `u = deg U`.  Outside the already
closed `(3,4)` family, the positive Newton fan lies on
`2u = a + 2b`, between `4a = 3b` and `2b = 3a`.  We first eliminate its
strict interior directly from the two invariant faces, then treat the
aligned endpoint `(a,b,u)=(2n,3n,4n)` using the terminal row.
-/

noncomputable section

set_option maxHeartbeats 6000000

open Polynomial

namespace Max11DegreeRoutes

section LWallOtherCones410

variable {k : Type*} [Field k] [CharZero k]

/-! ## The strict intermediate cone -/

def lWallIntermediateRestTwo410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (63 * l : k) • A ^ 5 + (140 * beta : k) • A ^ 4 -
    (180 * l : k) • (A ^ 3 * U) + (320 * delta : k) • A ^ 3 -
    (360 * l : k) • (A ^ 2 * B ^ 2) -
    (336 * beta : k) • (A ^ 2 * U) + (768 * zeta : k) • A ^ 2 -
    (1344 * beta : k) • (A * B ^ 2) + (180 * l : k) • (A * U ^ 2) -
    (640 * delta : k) • (A * U) + (2048 * theta : k) • A -
    (720 * l : k) • (B ^ 2 * U) + (1280 * delta : k) • B ^ 2 -
    (1536 * gamma : k) • (B * U) + (4096 * eta : k) • B +
    (336 * beta : k) • U ^ 2 - (1536 * zeta : k) • U

theorem discriminantInvariantTwoNumerator410_eq_intermediateFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
        A B U =
      -(1280 : k) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
        lWallIntermediateRestTwo410
          l beta gamma delta zeta eta theta A B U := by
  simp only [discriminantInvariantTwoNumerator410, lWallIntermediateRestTwo410]
  module

def lWallIntermediateRestOne410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(45 * l : k) • (A ^ 4 * B) - (112 * beta : k) • (A ^ 3 * B) +
    (180 * l : k) • (A ^ 2 * B * U) -
    (320 * delta : k) • (A ^ 2 * B) -
    (720 * l : k) • (A * B ^ 3) -
    (1536 * gamma : k) • (A * B ^ 2) +
    (672 * beta : k) • (A * B * U) - (1536 * zeta : k) • (A * B) -
    (320 : k) • B ^ 4 - (448 * beta : k) • B ^ 3 +
    (180 * l : k) • (B * U ^ 2) - (640 * delta : k) • (B * U) +
    (2048 * theta : k) • B + (192 * gamma : k) • U ^ 2 -
    (1024 * eta : k) • U

theorem discriminantInvariantOneNumerator410_eq_intermediateFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B U =
      (960 : k) • (A * B ^ 2 * U) - (40 : k) • U ^ 3 +
        lWallIntermediateRestOne410
          l beta gamma delta zeta eta theta A B U := by
  simp only [discriminantInvariantOneNumerator410, lWallIntermediateRestOne410]
  module

theorem lWallIntermediateRestTwo410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hplane : 2 * u = a + 2 * b) (hlower : 4 * a < 3 * b)
    (hupper : 2 * b < 3 * a) :
    (lWallIntermediateRestTwo410 l beta gamma delta zeta eta theta A B U).natDegree <
      a + 3 * b := by
  simp only [lWallIntermediateRestTwo410]
  compute_degree
  omega

theorem lWallIntermediateRestOne410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hplane : 2 * u = a + 2 * b) (hlower : 4 * a < 3 * b)
    (hupper : 2 * b < 3 * a) :
    (lWallIntermediateRestOne410 l beta gamma delta zeta eta theta A B U).natDegree <
      3 * u := by
  simp only [lWallIntermediateRestOne410]
  compute_degree
  omega

theorem discriminantInvariantTwoNumerator410_intermediate_coeff
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hplane : 2 * u = a + 2 * b) (hlower : 4 * a < 3 * b)
    (hupper : 2 * b < 3 * a) :
    (discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
      A B U).coeff (a + 3 * b) =
        -(1280 : k) * (A.leadingCoeff * B.leadingCoeff ^ 3) +
          (480 : k) * (B.leadingCoeff * U.leadingCoeff ^ 2) := by
  have hAB3deg : (A * B ^ 3).natDegree = a + 3 * b := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow, hA, hB]
  have hBU2deg : (B * U ^ 2).natDegree = a + 3 * b := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hB, hU]
    omega
  have hAB3coeff : (A * B ^ 3).coeff (a + 3 * b) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hBU2coeff : (B * U ^ 2).coeff (a + 3 * b) =
      B.leadingCoeff * U.leadingCoeff ^ 2 := by
    rw [← hBU2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hrest := lWallIntermediateRestTwo410_natDegree_lt
    l beta gamma delta zeta eta theta A B U a b u ha hb hu hA hB hU
      hplane hlower hupper
  rw [discriminantInvariantTwoNumerator410_eq_intermediateFace_add_rest,
    coeff_add, coeff_add, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero, hAB3coeff, hBU2coeff]
  simp only [smul_eq_mul]

theorem discriminantInvariantOneNumerator410_intermediate_coeff
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hplane : 2 * u = a + 2 * b) (hlower : 4 * a < 3 * b)
    (hupper : 2 * b < 3 * a) :
    (discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
      A B U).coeff (3 * u) =
        (960 : k) *
            (A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff) -
          (40 : k) * U.leadingCoeff ^ 3 := by
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 3 * u := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow,
      hA, hB, hU]
    omega
  have hU3deg : (U ^ 3).natDegree = 3 * u := by
    rw [natDegree_pow, hU]
  have hAB2Ucoeff : (A * B ^ 2 * U).coeff (3 * u) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff := by
    rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hU3coeff : (U ^ 3).coeff (3 * u) = U.leadingCoeff ^ 3 := by
    rw [← hU3deg, coeff_natDegree, leadingCoeff_pow]
  have hrest := lWallIntermediateRestOne410_natDegree_lt
    l beta gamma delta zeta eta theta A B U a b u ha hb hu hA hB hU
      hplane hlower hupper
  rw [discriminantInvariantOneNumerator410_eq_intermediateFace_add_rest,
    coeff_add, coeff_sub, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero, hAB2Ucoeff, hU3coeff]
  simp only [smul_eq_mul]

/-- No polynomial trajectory can occupy the strict intermediate Newton
cone. -/
theorem lWall410_intermediate_cone_impossible
    (l beta gamma delta zeta eta theta k₂ k₁ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hplane : 2 * u = a + 2 * b) (hlower : 4 * a < 3 * b)
    (hupper : 2 * b < 3 * a)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) : False := by
  have hk₂ : (C k₂ : k[X]).coeff (a + 3 * b) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hk₁ : (C k₁ : k[X]).coeff (3 * u) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hTwoCoeff := congrArg (fun P : k[X] => P.coeff (a + 3 * b)) hTwo
  rw [discriminantInvariantTwoNumerator410_intermediate_coeff
    l beta gamma delta zeta eta theta A B U a b u ha hb hu
      hAne hBne hUne hA hB hU hplane hlower hupper, hk₂] at hTwoCoeff
  have hOneCoeff := congrArg (fun P : k[X] => P.coeff (3 * u)) hOne
  rw [discriminantInvariantOneNumerator410_intermediate_coeff
    l beta gamma delta zeta eta theta A B U a b u ha hb hu
      hAne hBne hUne hA hB hU hplane hlower hupper, hk₁] at hOneCoeff
  have hBle : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hUle : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hUne
  have hfaceTwo :
      (3 : k) * U.leadingCoeff ^ 2 =
        (8 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 := by
    apply mul_left_cancel₀ hBle
    linear_combination (1 / 160 : k) * hTwoCoeff
  have hfaceOne :
      (24 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 =
        U.leadingCoeff ^ 2 := by
    apply mul_right_cancel₀ hUle
    linear_combination (1 / 40 : k) * hOneCoeff
  have hzero : (64 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 = 0 := by
    linear_combination 3 * hfaceOne + hfaceTwo
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hAle) (pow_ne_zero 2 hBle)) hzero

/-! ## The aligned endpoint -/

theorem lWallIntermediateRestTwo410_aligned_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hA : A.natDegree = 2 * n)
    (hB : B.natDegree = 3 * n) (hU : U.natDegree = 4 * n) :
    (lWallIntermediateRestTwo410 l beta gamma delta zeta eta theta A B U).natDegree <
      11 * n := by
  simp only [lWallIntermediateRestTwo410]
  compute_degree
  omega

theorem discriminantInvariantTwoNumerator410_aligned_coeff
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = 2 * n) (hB : B.natDegree = 3 * n)
    (hU : U.natDegree = 4 * n) :
    (discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
      A B U).coeff (11 * n) =
        -(1280 : k) * (A.leadingCoeff * B.leadingCoeff ^ 3) +
          (480 : k) * (B.leadingCoeff * U.leadingCoeff ^ 2) := by
  have hAB3deg : (A * B ^ 3).natDegree = 11 * n := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow, hA, hB]
    omega
  have hBU2deg : (B * U ^ 2).natDegree = 11 * n := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hB, hU]
    omega
  have hAB3coeff : (A * B ^ 3).coeff (11 * n) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hBU2coeff : (B * U ^ 2).coeff (11 * n) =
      B.leadingCoeff * U.leadingCoeff ^ 2 := by
    rw [← hBU2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hrest := lWallIntermediateRestTwo410_aligned_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hn hA hB hU
  rw [discriminantInvariantTwoNumerator410_eq_intermediateFace_add_rest,
    coeff_add, coeff_add, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero, hAB3coeff, hBU2coeff]
  simp only [smul_eq_mul]

def lWallAlignedTerminalARest410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (630 * l : k) • A ^ 5 + (1120 * beta : k) • A ^ 4 -
    (1080 * l : k) • (A ^ 3 * U) + (1920 * delta : k) • A ^ 3 -
    (720 * l : k) • (A ^ 2 * B ^ 2) -
    (1344 * beta : k) • (A ^ 2 * U) + (3072 * zeta : k) • A ^ 2 +
    (360 * l : k) • (A * U ^ 2) - (1280 * delta : k) • (A * U) +
    (4096 * theta : k) • A + (1440 * l : k) • (B ^ 2 * U) -
    (2560 * delta : k) • B ^ 2 + (1536 * gamma : k) • (B * U) -
    (4096 * eta : k) • B

def lWallAlignedTerminalBRest410
    (l beta gamma delta zeta : k) (A B U : k[X]) : k[X] :=
  -(720 * l : k) • (A ^ 3 * B) - (1344 * beta : k) • (A ^ 2 * B) +
    (1440 * l : k) • (A * B * U) - (2560 * delta : k) • (A * B) -
    (2880 * l : k) • B ^ 3 - (6144 * gamma : k) • B ^ 2 +
    (2688 * beta : k) • (B * U) - (6144 * zeta : k) • B

def lWallAlignedTerminalURest410
    (l beta delta zeta theta : k) (A B U : k[X]) : k[X] :=
  -(315 * l : k) • A ^ 4 - (560 * beta : k) • A ^ 3 +
    (540 * l : k) • (A ^ 2 * U) - (960 * delta : k) • A ^ 2 +
    (720 * l : k) • (A * B ^ 2) + (672 * beta : k) • (A * U) -
    (1536 * zeta : k) • A + (1344 * beta : k) • B ^ 2 -
    (180 * l : k) • U ^ 2 + (640 * delta : k) • U - C (2048 * theta)

def lWallAlignedTerminalRest410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  lWallAlignedTerminalARest410 l beta gamma delta zeta eta theta A B U *
      derivative A +
    lWallAlignedTerminalBRest410 l beta gamma delta zeta A B U * derivative B +
    lWallAlignedTerminalURest410 l beta delta zeta theta A B U * derivative U

theorem lWallTerminalACoefficient410_eq_alignedFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalACoefficient410 l beta gamma delta zeta eta theta A B U =
      (1280 : k) • (A * B ^ 3) - (480 : k) • (B * U ^ 2) +
        lWallAlignedTerminalARest410
          l beta gamma delta zeta eta theta A B U := by
  simp only [lWallTerminalACoefficient410, lWallAlignedTerminalARest410]
  module

theorem lWallTerminalBCoefficient410_eq_alignedFace_add_rest
    (l beta gamma delta zeta : k) (A B U : k[X]) :
    lWallTerminalBCoefficient410 l beta gamma delta zeta A B U =
      (3840 : k) • (B ^ 2 * U) +
        lWallAlignedTerminalBRest410 l beta gamma delta zeta A B U := by
  simp only [lWallTerminalBCoefficient410, lWallAlignedTerminalBRest410]
  module

theorem lWallTerminalUCoefficient410_eq_alignedFace_add_rest
    (l beta delta zeta theta : k) (A B U : k[X]) :
    lWallTerminalUCoefficient410 l beta delta zeta theta A B U =
      (1280 : k) • B ^ 3 +
        lWallAlignedTerminalURest410 l beta delta zeta theta A B U := by
  simp only [lWallTerminalUCoefficient410, lWallAlignedTerminalURest410]
  module

theorem lWallTerminalNumerator410_eq_alignedFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B U =
      (1280 : k) • (A * B ^ 3 * derivative A) -
        (480 : k) • (B * U ^ 2 * derivative A) +
        (3840 : k) • (B ^ 2 * U * derivative B) +
        (1280 : k) • (B ^ 3 * derivative U) +
          lWallAlignedTerminalRest410
            l beta gamma delta zeta eta theta A B U := by
  simp only [lWallTerminalNumerator410]
  rw [lWallTerminalACoefficient410_eq_alignedFace_add_rest,
    lWallTerminalBCoefficient410_eq_alignedFace_add_rest,
    lWallTerminalUCoefficient410_eq_alignedFace_add_rest]
  simp only [lWallAlignedTerminalRest410]
  simp only [add_mul, sub_mul, smul_mul_assoc]
  abel

theorem lWallAlignedTerminalRest410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hA : A.natDegree = 2 * n)
    (hB : B.natDegree = 3 * n) (hU : U.natDegree = 4 * n) :
    (lWallAlignedTerminalRest410 l beta gamma delta zeta eta theta A B U).natDegree <
      13 * n - 1 := by
  simp only [lWallAlignedTerminalRest410, lWallAlignedTerminalARest410,
    lWallAlignedTerminalBRest410, lWallAlignedTerminalURest410]
  compute_degree
  omega

theorem lWallTerminalNumerator410_aligned_coeff
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = 2 * n) (hB : B.natDegree = 3 * n)
    (hU : U.natDegree = 4 * n) :
    (lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B U).coeff
        (13 * n - 1) =
      (1280 : k) * (A.leadingCoeff * B.leadingCoeff ^ 3) *
          (A.leadingCoeff * (2 * n : ℕ)) -
        (480 : k) * (B.leadingCoeff * U.leadingCoeff ^ 2) *
          (A.leadingCoeff * (2 * n : ℕ)) +
        (3840 : k) * (B.leadingCoeff ^ 2 * U.leadingCoeff) *
          (B.leadingCoeff * (3 * n : ℕ)) +
        (1280 : k) * B.leadingCoeff ^ 3 *
          (U.leadingCoeff * (4 * n : ℕ)) := by
  have hAdegne : A.natDegree ≠ 0 := by omega
  have hBdegne : B.natDegree ≠ 0 := by omega
  have hUdegne : U.natDegree ≠ 0 := by omega
  have hdAne : derivative A ≠ 0 := derivative_ne_zero.mpr hAdegne
  have hdBne : derivative B ≠ 0 := derivative_ne_zero.mpr hBdegne
  have hdUne : derivative U ≠ 0 := derivative_ne_zero.mpr hUdegne
  have hAB3ddeg : (A * B ^ 3 * derivative A).natDegree = 13 * n - 1 := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hdAne,
      natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow,
      natDegree_derivative, hA, hB]
    omega
  have hBU2dAdeg : (B * U ^ 2 * derivative A).natDegree = 13 * n - 1 := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hUne)) hdAne,
      natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow,
      natDegree_derivative, hA, hB, hU]
    omega
  have hB2UdBdeg : (B ^ 2 * U * derivative B).natDegree = 13 * n - 1 := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hUne) hdBne,
      natDegree_mul (pow_ne_zero 2 hBne) hUne, natDegree_pow,
      natDegree_derivative, hB, hU]
    omega
  have hB3dUdeg : (B ^ 3 * derivative U).natDegree = 13 * n - 1 := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hdUne, natDegree_pow,
      natDegree_derivative, hB, hU]
    omega
  have hAB3dcoeff : (A * B ^ 3 * derivative A).coeff (13 * n - 1) =
      (A.leadingCoeff * B.leadingCoeff ^ 3) *
        (A.leadingCoeff * (2 * n : ℕ)) := by
    rw [← hAB3ddeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_derivative, hA]
  have hBU2dAcoeff : (B * U ^ 2 * derivative A).coeff (13 * n - 1) =
      (B.leadingCoeff * U.leadingCoeff ^ 2) *
        (A.leadingCoeff * (2 * n : ℕ)) := by
    rw [← hBU2dAdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_derivative, hA]
  have hB2UdBcoeff : (B ^ 2 * U * derivative B).coeff (13 * n - 1) =
      (B.leadingCoeff ^ 2 * U.leadingCoeff) *
        (B.leadingCoeff * (3 * n : ℕ)) := by
    rw [← hB2UdBdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_derivative, hB]
  have hB3dUcoeff : (B ^ 3 * derivative U).coeff (13 * n - 1) =
      B.leadingCoeff ^ 3 * (U.leadingCoeff * (4 * n : ℕ)) := by
    rw [← hB3dUdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_derivative, hU]
  have hrest := lWallAlignedTerminalRest410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hn hA hB hU
  rw [lWallTerminalNumerator410_eq_alignedFace_add_rest,
    coeff_add, coeff_add, coeff_add, coeff_sub,
    coeff_smul, coeff_smul, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero, hAB3dcoeff,
    hBU2dAcoeff, hB2UdBcoeff, hB3dUcoeff]
  simp only [smul_eq_mul]
  ring

theorem lWall410_aligned_cone_terminal_impossible
    (l beta gamma delta zeta eta theta k₂ terminal : k) (A B U : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = 2 * n) (hB : B.natDegree = 3 * n)
    (hU : U.natDegree = 4 * n)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hTerminal : lWallTerminalNumerator410
      l beta gamma delta zeta eta theta A B U = C terminal) : False := by
  have hk₂ : (C k₂ : k[X]).coeff (11 * n) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hTwoCoeff := congrArg (fun P : k[X] => P.coeff (11 * n)) hTwo
  rw [discriminantInvariantTwoNumerator410_aligned_coeff
    l beta gamma delta zeta eta theta A B U n hn hAne hBne hUne hA hB hU,
    hk₂] at hTwoCoeff
  have hkTerminal : (C terminal : k[X]).coeff (13 * n - 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hTerminalCoeff := congrArg
    (fun P : k[X] => P.coeff (13 * n - 1)) hTerminal
  rw [lWallTerminalNumerator410_aligned_coeff
    l beta gamma delta zeta eta theta A B U n hn hAne hBne hUne hA hB hU,
    hkTerminal] at hTerminalCoeff
  push_cast at hTerminalCoeff
  have hzero :
      (16640 : k) * B.leadingCoeff ^ 3 * U.leadingCoeff * n = 0 := by
    ring_nf at hTerminalCoeff hTwoCoeff ⊢
    linear_combination hTerminalCoeff +
      2 * (n : k) * A.leadingCoeff * hTwoCoeff
  have hBle : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hUle : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hUne
  have hncast : (n : k) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hnonzero :
      (16640 : k) * B.leadingCoeff ^ 3 * U.leadingCoeff * n ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 3 hBle)) hUle) hncast
  exact hnonzero hzero

/-! ## Arithmetic fan split and source-coordinate wrappers -/

/-- The closed degree sector between the two boundary rays has only the
`(3n,4n)` boundary, its strict interior, and the aligned `(2n,3n,4n)`
endpoint. -/
theorem lWall410_closed_sector_fan_split (a b u : ℕ)
    (hplane : 2 * u = a + 2 * b) (hlower : 4 * a ≤ 3 * b)
    (hupper : 2 * b ≤ 3 * a) :
    (∃ n, a = 3 * n ∧ b = 4 * n) ∨
      (4 * a < 3 * b ∧ 2 * b < 3 * a) ∨
        ∃ n, a = 2 * n ∧ b = 3 * n ∧ u = 4 * n := by
  by_cases hlowerEq : 4 * a = 3 * b
  · left
    have hdiv : 3 ∣ a := by
      apply (by decide : Nat.Coprime 3 4).dvd_of_dvd_mul_right
      use b
      omega
    obtain ⟨n, hn⟩ := hdiv
    exact ⟨n, by omega⟩
  · right
    have hlowerStrict : 4 * a < 3 * b := by omega
    by_cases hupperEq : 2 * b = 3 * a
    · right
      have hdiv : 2 ∣ a := by
        apply (by decide : Nat.Coprime 2 3).dvd_of_dvd_mul_right
        use b
        omega
      obtain ⟨n, hn⟩ := hdiv
      exact ⟨n, by omega⟩
    · left
      exact ⟨hlowerStrict, by omega⟩

theorem lWall410_intermediate_original_invariants_impossible
    (l beta gamma delta zeta eta theta k₂ k₁ : k) (A B C0 : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b)
    (hU : (A ^ 2 - (4 : k) • C0).natDegree = u)
    (hplane : 2 * u = a + 2 * b) (hlower : 4 * a < 3 * b)
    (hupper : 2 * b < 3 * a)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₁) : False := by
  have hUne : A ^ 2 - (4 : k) • C0 ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hU
    omega
  have hTwoD :
      discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₂) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD :
      discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₁) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact lWall410_intermediate_cone_impossible
    l beta gamma delta zeta eta theta (2048 * k₂) (2048 * k₁)
      A B (A ^ 2 - (4 : k) • C0) a b u ha hb hu hAne hBne hUne
        hA hB hU hplane hlower hupper hTwoD hOneD

theorem lWall410_aligned_original_terminal_impossible
    (l alpha beta gamma delta epsilon zeta eta theta iota k₂ terminal : k)
    (A B C0 : k[X]) (n : ℕ) (hn : 0 < n)
    (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 2 * n) (hB : B.natDegree = 3 * n)
    (hU : (A ^ 2 - (4 : k) • C0).natDegree = 4 * n)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₂)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hUne : A ^ 2 - (4 : k) • C0 ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hU
    omega
  have hTwoD :
      discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₂) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD :
      lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B
          (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact lWall410_aligned_cone_terminal_impossible
    l beta gamma delta zeta eta theta (2048 * k₂) (8192 * terminal)
      A B (A ^ 2 - (4 : k) • C0) n hn hAne hBne hUne hA hB hU
        hTwoD hTerminalD

end LWallOtherCones410

end Max11DegreeRoutes
