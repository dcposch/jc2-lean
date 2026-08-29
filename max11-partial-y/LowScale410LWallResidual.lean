import LowScale410LWallBoundary

/-!
# Terminal-row elimination of the residual `(3n,4n)` load walls

The denominator-free coordinate `U = A^2 - 4 C0` also makes the terminal
row sparse.  We use the integer numerator `8192 (W C0' - B Z')` and its
three coefficients against `A'`, `B'`, and `U'`.
-/

noncomputable section

set_option maxHeartbeats 6000000

open Polynomial

namespace Max11DegreeRoutes

section LWallResidual410

variable {k : Type*} [Field k] [CharZero k]

def lWallTerminalACoefficient410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (630 * l : k) • A ^ 5 + (1120 * beta : k) • A ^ 4 -
    (1080 * l : k) • (A ^ 3 * U) + (1920 * delta : k) • A ^ 3 -
    (720 * l : k) • (A ^ 2 * B ^ 2) -
    (1344 * beta : k) • (A ^ 2 * U) + (3072 * zeta : k) • A ^ 2 +
    (1280 : k) • (A * B ^ 3) + (360 * l : k) • (A * U ^ 2) -
    (1280 * delta : k) • (A * U) + (4096 * theta : k) • A +
    (1440 * l : k) • (B ^ 2 * U) - (2560 * delta : k) • B ^ 2 -
    (480 : k) • (B * U ^ 2) + (1536 * gamma : k) • (B * U) -
    (4096 * eta : k) • B

def lWallTerminalBCoefficient410
    (l beta gamma delta zeta : k) (A B U : k[X]) : k[X] :=
  -(720 * l : k) • (A ^ 3 * B) - (1344 * beta : k) • (A ^ 2 * B) +
    (1440 * l : k) • (A * B * U) - (2560 * delta : k) • (A * B) -
    (2880 * l : k) • B ^ 3 + (3840 : k) • (B ^ 2 * U) -
    (6144 * gamma : k) • B ^ 2 + (2688 * beta : k) • (B * U) -
    (6144 * zeta : k) • B

def lWallTerminalUCoefficient410
    (l beta delta zeta theta : k) (A B U : k[X]) : k[X] :=
  -(315 * l : k) • A ^ 4 - (560 * beta : k) • A ^ 3 +
    (540 * l : k) • (A ^ 2 * U) - (960 * delta : k) • A ^ 2 +
    (720 * l : k) • (A * B ^ 2) + (672 * beta : k) • (A * U) -
    (1536 * zeta : k) • A + (1280 : k) • B ^ 3 +
    (1344 * beta : k) • B ^ 2 - (180 * l : k) • U ^ 2 +
    (640 * delta : k) • U - C (2048 * theta)

def lWallTerminalNumerator410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  lWallTerminalACoefficient410 l beta gamma delta zeta eta theta A B U *
      derivative A +
    lWallTerminalBCoefficient410 l beta gamma delta zeta A B U * derivative B +
    lWallTerminalUCoefficient410 l beta delta zeta theta A B U * derivative U

/-- Exact bridge from the integrated terminal row.  The formally present
loads `alpha`, `epsilon`, and `iota` cancel, as they must. -/
theorem lowerRow410_discriminantTerminalNumerator
    (l alpha beta gamma delta epsilon zeta eta theta iota : k)
    (A B C0 : k[X]) :
    (8192 : k) • lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 =
      lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B
        (A ^ 2 - (4 : k) • C0) := by
  simp only [lowerRowZeroPolynomial410, integratedWPolynomial410,
    integratedZPolynomial410, lWallTerminalNumerator410,
    lWallTerminalACoefficient410, lWallTerminalBCoefficient410,
    lWallTerminalUCoefficient410, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_neg,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_smul, Polynomial.derivative_C,
    Polynomial.smul_eq_C_mul]
  push_cast
  simp only [Polynomial.C_neg,
    Polynomial.derivative_ofNat, zero_mul, mul_zero, add_zero, sub_zero]
  ring_nf
  have hC (x : k) : Polynomial.C x = x • (1 : k[X]) := by
    simp [Algebra.smul_def, Polynomial.C_eq_algebraMap]
  have h2 : (2 : k[X]) = (2 : k) • (1 : k[X]) := by
    rw [← hC]
    exact (Polynomial.C_ofNat 2).symm
  simp only [hC, pow_two, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, _root_.smul_pow, one_pow]
  rw [h2]
  simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

/-! ## Elimination of the `deg U = 5n` residual -/

def lWallBoundaryTerminalARest410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (1120 * beta : k) • A ^ 4 - (1080 * l : k) • (A ^ 3 * U) +
    (1920 * delta : k) • A ^ 3 - (720 * l : k) • (A ^ 2 * B ^ 2) -
    (1344 * beta : k) • (A ^ 2 * U) + (3072 * zeta : k) • A ^ 2 +
    (360 * l : k) • (A * U ^ 2) - (1280 * delta : k) • (A * U) +
    (4096 * theta : k) • A + (1440 * l : k) • (B ^ 2 * U) -
    (2560 * delta : k) • B ^ 2 - (480 : k) • (B * U ^ 2) +
    (1536 * gamma : k) • (B * U) - (4096 * eta : k) • B

def lWallBoundaryTerminalRest410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  lWallBoundaryTerminalARest410 l beta gamma delta zeta eta theta A B U *
      derivative A +
    lWallTerminalBCoefficient410 l beta gamma delta zeta A B U * derivative B +
    lWallTerminalUCoefficient410 l beta delta zeta theta A B U * derivative U

theorem lWallTerminalACoefficient410_eq_boundaryFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalACoefficient410 l beta gamma delta zeta eta theta A B U =
      (630 * l : k) • A ^ 5 + (1280 : k) • (A * B ^ 3) +
        lWallBoundaryTerminalARest410
          l beta gamma delta zeta eta theta A B U := by
  simp only [lWallTerminalACoefficient410, lWallBoundaryTerminalARest410]
  module

theorem lWallTerminalNumerator410_eq_boundaryFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B U =
      (630 * l : k) • (A ^ 5 * derivative A) +
        (1280 : k) • (A * B ^ 3 * derivative A) +
          lWallBoundaryTerminalRest410
            l beta gamma delta zeta eta theta A B U := by
  simp only [lWallTerminalNumerator410]
  rw [lWallTerminalACoefficient410_eq_boundaryFace_add_rest]
  simp only [lWallBoundaryTerminalRest410]
  simp only [add_mul, smul_mul_assoc]
  abel

theorem lWallBoundaryTerminalRest410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hA : A.natDegree = 3 * n)
    (hB : B.natDegree = 4 * n) (hU : U.natDegree = 5 * n) :
    (lWallBoundaryTerminalRest410 l beta gamma delta zeta eta theta A B U).natDegree <
      18 * n - 1 := by
  simp only [lWallBoundaryTerminalRest410, lWallBoundaryTerminalARest410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410]
  compute_degree
  omega

theorem lWallTerminalNumerator410_boundary_coeff
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree = 5 * n) :
    (lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B U).coeff
        (18 * n - 1) =
      (630 * l : k) *
          (A.leadingCoeff ^ 5 *
            (A.leadingCoeff * (3 * n : ℕ))) +
        (1280 : k) *
          ((A.leadingCoeff * B.leadingCoeff ^ 3) *
            (A.leadingCoeff * (3 * n : ℕ))) := by
  have hAdegne : A.natDegree ≠ 0 := by omega
  have hdAne : derivative A ≠ 0 := derivative_ne_zero.mpr hAdegne
  have hA5ddeg : (A ^ 5 * derivative A).natDegree = 18 * n - 1 := by
    rw [natDegree_mul (pow_ne_zero 5 hAne) hdAne, natDegree_pow,
      natDegree_derivative, hA]
    omega
  have hAB3ddeg : (A * B ^ 3 * derivative A).natDegree = 18 * n - 1 := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hdAne,
      natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow,
      natDegree_derivative, hA, hB]
    omega
  have hA5dcoeff : (A ^ 5 * derivative A).coeff (18 * n - 1) =
      A.leadingCoeff ^ 5 * (A.leadingCoeff * (3 * n : ℕ)) := by
    rw [← hA5ddeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_derivative, hA]
  have hAB3dcoeff : (A * B ^ 3 * derivative A).coeff (18 * n - 1) =
      (A.leadingCoeff * B.leadingCoeff ^ 3) *
        (A.leadingCoeff * (3 * n : ℕ)) := by
    rw [← hAB3ddeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_derivative, hA]
  have hrest := lWallBoundaryTerminalRest410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hn hA hB hU
  rw [lWallTerminalNumerator410_eq_boundaryFace_add_rest,
    coeff_add, coeff_add, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero, hA5dcoeff, hAB3dcoeff]
  simp only [smul_eq_mul]

/-- The terminal row eliminates the `deg U = 5n` scalar residual wall. -/
theorem lWall410_boundary_terminal_impossible
    (l beta gamma delta zeta eta theta k₂ terminal : k) (A B U : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree = 5 * n)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hTerminal : lWallTerminalNumerator410
      l beta gamma delta zeta eta theta A B U = C terminal) : False := by
  have hk₂ : (C k₂ : k[X]).coeff (15 * n) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hTwoCoeff := congrArg (fun P : k[X] => P.coeff (15 * n)) hTwo
  rw [discriminantInvariantTwoNumerator410_boundary_coeff_fifteen
    l beta gamma delta zeta eta theta A B U n hn hAne hBne hA hB hU,
    hk₂] at hTwoCoeff
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBle : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hrel : (63 * l : k) * A.leadingCoeff ^ 4 =
      (1280 : k) * B.leadingCoeff ^ 3 := by
    apply mul_left_cancel₀ hAle
    linear_combination hTwoCoeff
  have hrelTen : (630 * l : k) * A.leadingCoeff ^ 4 =
      (12800 : k) * B.leadingCoeff ^ 3 := by
    linear_combination 10 * hrel
  have hkTerminal : (C terminal : k[X]).coeff (18 * n - 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hTerminalCoeff := congrArg
    (fun P : k[X] => P.coeff (18 * n - 1)) hTerminal
  rw [lWallTerminalNumerator410_boundary_coeff
    l beta gamma delta zeta eta theta A B U n hn hAne hBne hA hB hU,
    hkTerminal] at hTerminalCoeff
  have hzero :
      (14080 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 *
        (3 * n : ℕ) = 0 := by
    linear_combination hTerminalCoeff -
      A.leadingCoeff ^ 2 * (3 * n : ℕ) * hrelTen
  have hncast : ((3 * n : ℕ) : k) ≠ 0 := by
    exact_mod_cast (by omega : (3 * n : ℕ) ≠ 0)
  have hnonzero :
      (14080 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 *
        (3 * n : ℕ) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hAle))
        (pow_ne_zero 3 hBle)) hncast
  exact hnonzero hzero

/-! ## Elimination of the exceptional half-wall -/

def lWallHalfTerminalARest410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (1120 * beta : k) • A ^ 4 - (1080 * l : k) • (A ^ 3 * U) +
    (1920 * delta : k) • A ^ 3 - (720 * l : k) • (A ^ 2 * B ^ 2) -
    (1344 * beta : k) • (A ^ 2 * U) + (3072 * zeta : k) • A ^ 2 +
    (360 * l : k) • (A * U ^ 2) - (1280 * delta : k) • (A * U) +
    (4096 * theta : k) • A + (1440 * l : k) • (B ^ 2 * U) -
    (2560 * delta : k) • B ^ 2 + (1536 * gamma : k) • (B * U) -
    (4096 * eta : k) • B

def lWallHalfTerminalRest410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  lWallHalfTerminalARest410 l beta gamma delta zeta eta theta A B U *
      derivative A +
    lWallTerminalBCoefficient410 l beta gamma delta zeta A B U * derivative B +
    lWallTerminalUCoefficient410 l beta delta zeta theta A B U * derivative U

theorem lWallTerminalACoefficient410_eq_halfFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalACoefficient410 l beta gamma delta zeta eta theta A B U =
      (630 * l : k) • A ^ 5 + (1280 : k) • (A * B ^ 3) -
        (480 : k) • (B * U ^ 2) +
          lWallHalfTerminalARest410
            l beta gamma delta zeta eta theta A B U := by
  simp only [lWallTerminalACoefficient410, lWallHalfTerminalARest410]
  module

theorem lWallTerminalNumerator410_eq_halfFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B U =
      (630 * l : k) • (A ^ 5 * derivative A) +
        (1280 : k) • (A * B ^ 3 * derivative A) -
          (480 : k) • (B * U ^ 2 * derivative A) +
            lWallHalfTerminalRest410
              l beta gamma delta zeta eta theta A B U := by
  simp only [lWallTerminalNumerator410]
  rw [lWallTerminalACoefficient410_eq_halfFace_add_rest]
  simp only [lWallHalfTerminalRest410]
  simp only [add_mul, sub_mul, smul_mul_assoc]
  abel

theorem lWallHalfTerminalRest410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hA : A.natDegree = 3 * n)
    (hB : B.natDegree = 4 * n) (hU : 2 * U.natDegree = 11 * n) :
    (lWallHalfTerminalRest410 l beta gamma delta zeta eta theta A B U).natDegree <
      18 * n - 1 := by
  simp only [lWallHalfTerminalRest410, lWallHalfTerminalARest410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410]
  compute_degree
  omega

theorem lWallTerminalNumerator410_halfWall_coeff
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : 2 * U.natDegree = 11 * n) :
    (lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B U).coeff
        (18 * n - 1) =
      (630 * l : k) *
          (A.leadingCoeff ^ 5 *
            (A.leadingCoeff * (3 * n : ℕ))) +
        (1280 : k) *
          ((A.leadingCoeff * B.leadingCoeff ^ 3) *
            (A.leadingCoeff * (3 * n : ℕ))) -
        (480 : k) *
          ((B.leadingCoeff * U.leadingCoeff ^ 2) *
            (A.leadingCoeff * (3 * n : ℕ))) := by
  have hUpos : 0 < U.natDegree := by omega
  have hUne : U ≠ 0 := by
    intro hzero
    subst U
    simp at hUpos
  have hAdegne : A.natDegree ≠ 0 := by omega
  have hdAne : derivative A ≠ 0 := derivative_ne_zero.mpr hAdegne
  have hA5ddeg : (A ^ 5 * derivative A).natDegree = 18 * n - 1 := by
    rw [natDegree_mul (pow_ne_zero 5 hAne) hdAne, natDegree_pow,
      natDegree_derivative, hA]
    omega
  have hAB3ddeg : (A * B ^ 3 * derivative A).natDegree = 18 * n - 1 := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hdAne,
      natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow,
      natDegree_derivative, hA, hB]
    omega
  have hBU2ddeg : (B * U ^ 2 * derivative A).natDegree = 18 * n - 1 := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hUne)) hdAne,
      natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow,
      natDegree_derivative, hA, hB]
    omega
  have hA5dcoeff : (A ^ 5 * derivative A).coeff (18 * n - 1) =
      A.leadingCoeff ^ 5 * (A.leadingCoeff * (3 * n : ℕ)) := by
    rw [← hA5ddeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_derivative, hA]
  have hAB3dcoeff : (A * B ^ 3 * derivative A).coeff (18 * n - 1) =
      (A.leadingCoeff * B.leadingCoeff ^ 3) *
        (A.leadingCoeff * (3 * n : ℕ)) := by
    rw [← hAB3ddeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_derivative, hA]
  have hBU2dcoeff : (B * U ^ 2 * derivative A).coeff (18 * n - 1) =
      (B.leadingCoeff * U.leadingCoeff ^ 2) *
        (A.leadingCoeff * (3 * n : ℕ)) := by
    rw [← hBU2ddeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_derivative, hA]
  have hrest := lWallHalfTerminalRest410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hn hA hB hU
  rw [lWallTerminalNumerator410_eq_halfFace_add_rest,
    coeff_add, coeff_sub, coeff_add, coeff_smul, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero, hA5dcoeff, hAB3dcoeff,
    hBU2dcoeff]
  simp only [smul_eq_mul]

/-- The terminal row also eliminates the only exceptional high-`U`
half-wall. -/
theorem lWall410_halfWall_terminal_impossible
    (l beta gamma delta zeta eta theta k₂ k₁ terminal : k) (A B U : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : 2 * U.natDegree = 11 * n)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁)
    (hTerminal : lWallTerminalNumerator410
      l beta gamma delta zeta eta theta A B U = C terminal) : False := by
  obtain ⟨hshape, hload⟩ := lWall410_halfWall_leadingCoeff_residual
    l beta gamma delta zeta eta theta k₂ k₁ A B U n hn hAne hBne
      hA hB hU hTwo hOne
  have hloadTen : (630 * l : k) * A.leadingCoeff ^ 4 =
      -(102400 : k) * B.leadingCoeff ^ 3 := by
    linear_combination 10 * hload
  have hkTerminal : (C terminal : k[X]).coeff (18 * n - 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hTerminalCoeff := congrArg
    (fun P : k[X] => P.coeff (18 * n - 1)) hTerminal
  rw [lWallTerminalNumerator410_halfWall_coeff
    l beta gamma delta zeta eta theta A B U n hn hAne hBne hA hB hU,
    hkTerminal] at hTerminalCoeff
  have hzero :
      -(112640 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 *
        (3 * n : ℕ) = 0 := by
    linear_combination hTerminalCoeff -
      A.leadingCoeff ^ 2 * (3 * n : ℕ) * hloadTen -
      480 * A.leadingCoeff * B.leadingCoeff * (3 * n : ℕ) * hshape
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBle : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hncast : ((3 * n : ℕ) : k) ≠ 0 := by
    exact_mod_cast (by omega : (3 * n : ℕ) ≠ 0)
  have hnonzero :
      -(112640 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 *
        (3 * n : ℕ) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hAle))
        (pow_ne_zero 3 hBle)) hncast
  exact hnonzero hzero

/-! ## Source-coordinate wrappers -/

theorem lWall410_boundary_original_terminal_impossible
    (l alpha beta gamma delta epsilon zeta eta theta iota k₂ terminal : k)
    (A B C0 : k[X]) (n : ℕ) (hn : 0 < n)
    (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : (A ^ 2 - (4 : k) • C0).natDegree = 5 * n)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₂)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
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
  exact lWall410_boundary_terminal_impossible
    l beta gamma delta zeta eta theta (2048 * k₂) (8192 * terminal)
      A B (A ^ 2 - (4 : k) • C0) n hn hAne hBne hA hB hU hTwoD hTerminalD

theorem lWall410_halfWall_original_terminal_impossible
    (l alpha beta gamma delta epsilon zeta eta theta iota
      k₂ k₁ terminal : k)
    (A B C0 : k[X]) (n : ℕ) (hn : 0 < n)
    (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : 2 * (A ^ 2 - (4 : k) • C0).natDegree = 11 * n)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₁)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
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
  have hTerminalD :
      lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B
          (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact lWall410_halfWall_terminal_impossible
    l beta gamma delta zeta eta theta (2048 * k₂) (2048 * k₁)
      (8192 * terminal) A B (A ^ 2 - (4 : k) • C0) n hn hAne hBne
        hA hB hU hTwoD hOneD hTerminalD

end LWallResidual410

end Max11DegreeRoutes
