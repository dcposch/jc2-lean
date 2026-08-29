import LowScale410LoadCascade

/-!
# Second effective-load wall for the direct `(4,10)`, H=0 route

Assume `l = 0` and `beta ≠ 0` on the aligned source cone
`deg A ≤ 2n`, `deg B ≤ 3n`, `deg C0 ≤ 4n`, with both first integrals
constant and a nonzero terminal row.  After `l` is removed the remaining
load is beta-leading at radii `8n` (I2), `9n` (I1), and `10n-1`
(terminal).  Every source face that attains at least one of `2n`, `3n`,
`4n` is closed except the dropped-discriminant corner
`deg A = 2n`, `0 < deg B < 3n`, `deg C0 = 4n`, `deg(A^2-4 C0) < 4n`.
-/

noncomputable section

set_option maxHeartbeats 8000000

open Polynomial

namespace Max11DegreeRoutes

section BetaWall410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-! ## Beta / rest splits of the load remainders -/

/-- Beta-leading face of the first invariant after `l = 0`. -/
def betaLoadTwoPolynomial410 (beta : k) (A B C0 : k[X]) : k[X] :=
  (35 / 512 * beta : k) • A ^ 4 -
    (21 / 32 * beta : k) • (A ^ 2 * C0) -
    (21 / 32 * beta : k) • (A * B ^ 2) +
    (21 / 8 * beta : k) • C0 ^ 2

/-- Loads strictly below the I2 beta face: `gamma` through `theta`. -/
def betaLoadTwoRest410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  -(3 / 4 * gamma : k) • (A ^ 2 * B) + (3 * gamma : k) • (B * C0) -
    (5 / 32 * delta : k) • A ^ 3 + (5 / 4 * delta : k) • (A * C0) +
    (5 / 8 * delta : k) • B ^ 2 -
    (3 / 8 * zeta : k) • A ^ 2 + (3 * zeta : k) • C0 +
    (2 * eta : k) • B + theta • A

theorem loadCorrectionTwoPolynomial410_eq_beta_add_rest
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    loadCorrectionTwoPolynomial410 0 beta gamma delta zeta eta theta A B C0 =
      betaLoadTwoPolynomial410 beta A B C0 +
        betaLoadTwoRest410 gamma delta zeta eta theta A B C0 := by
  simp only [loadCorrectionTwoPolynomial410, betaLoadTwoPolynomial410,
    betaLoadTwoRest410, zero_mul, zero_smul, add_zero, sub_zero]
  module

/-- Beta-leading face of the second invariant after `l = 0`. -/
def betaLoadOnePolynomial410 (beta : k) (A B C0 : k[X]) : k[X] :=
  (35 / 128 * beta : k) • (A ^ 3 * B) -
    (21 / 16 * beta : k) • (A * B * C0) -
    (7 / 32 * beta : k) • B ^ 3

/-- Loads strictly below the I1 beta face. -/
def betaLoadOneRest410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  (3 / 32 * gamma : k) • A ^ 4 - (3 / 4 * gamma : k) • (A ^ 2 * C0) -
    (3 / 4 * gamma : k) • (A * B ^ 2) + (3 / 2 * gamma : k) • C0 ^ 2 -
    (15 / 32 * delta : k) • (A ^ 2 * B) + (5 / 4 * delta : k) • (B * C0) -
    (3 / 4 * zeta : k) • (A * B) -
    (1 / 2 * eta : k) • A ^ 2 + (2 * eta : k) • C0 + theta • B

theorem loadCorrectionOnePolynomial410_eq_beta_add_rest
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    loadCorrectionOnePolynomial410 0 beta gamma delta zeta eta theta A B C0 =
      betaLoadOnePolynomial410 beta A B C0 +
        betaLoadOneRest410 gamma delta zeta eta theta A B C0 := by
  simp only [loadCorrectionOnePolynomial410, betaLoadOnePolynomial410,
    betaLoadOneRest410, zero_mul, zero_smul, add_zero, sub_zero]
  module

theorem betaLoadTwoPolynomial410_natDegree_le
    (beta : k) (A B C0 : k[X]) (n : ℕ)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n) :
    (betaLoadTwoPolynomial410 beta A B C0).natDegree ≤ 8 * n := by
  simp only [betaLoadTwoPolynomial410]
  compute_degree
  omega

theorem betaLoadTwoRest410_natDegree_lt
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n) :
    (betaLoadTwoRest410 gamma delta zeta eta theta A B C0).natDegree <
      8 * n := by
  simp only [betaLoadTwoRest410]
  compute_degree
  omega

theorem betaLoadOnePolynomial410_natDegree_le
    (beta : k) (A B C0 : k[X]) (n : ℕ)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n) :
    (betaLoadOnePolynomial410 beta A B C0).natDegree ≤ 9 * n := by
  simp only [betaLoadOnePolynomial410]
  compute_degree
  omega

theorem betaLoadOneRest410_natDegree_lt
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n) :
    (betaLoadOneRest410 gamma delta zeta eta theta A B C0).natDegree <
      9 * n := by
  simp only [betaLoadOneRest410]
  compute_degree
  omega

/-- After `l = 0` the first-invariant load remainder drops from `10n` to
`8n`. -/
theorem loadCorrectionTwoPolynomial410_natDegree_le_eightRadius_of_l
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) (n : ℕ)
    (hn : 0 < n) (hl : l = 0) (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n) (hC0 : C0.natDegree ≤ 4 * n) :
    (loadCorrectionTwoPolynomial410 l beta gamma delta zeta eta theta
      A B C0).natDegree ≤ 8 * n := by
  subst l
  rw [loadCorrectionTwoPolynomial410_eq_beta_add_rest]
  exact (natDegree_add_le _ _).trans <| max_le
    (betaLoadTwoPolynomial410_natDegree_le beta A B C0 n hA hB hC0)
    (le_of_lt (betaLoadTwoRest410_natDegree_lt
      gamma delta zeta eta theta A B C0 n hn hA hB hC0))

/-- After `l = 0` the second-invariant load remainder drops from `11n` to
`9n`. -/
theorem loadCorrectionOnePolynomial410_natDegree_le_nineRadius_of_l
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) (n : ℕ)
    (hn : 0 < n) (hl : l = 0) (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n) (hC0 : C0.natDegree ≤ 4 * n) :
    (loadCorrectionOnePolynomial410 l beta gamma delta zeta eta theta
      A B C0).natDegree ≤ 9 * n := by
  subst l
  rw [loadCorrectionOnePolynomial410_eq_beta_add_rest]
  exact (natDegree_add_le _ _).trans <| max_le
    (betaLoadOnePolynomial410_natDegree_le beta A B C0 n hA hB hC0)
    (le_of_lt (betaLoadOneRest410_natDegree_lt
      gamma delta zeta eta theta A B C0 n hn hA hB hC0))

/-! ## Terminal remainder after `l = 0` -/

/-- Load part of `W` after `l = 0`, excluding the `alpha`/`epsilon` terms
that cancel from the terminal row. -/
def betaWallWRemainder410
    (beta gamma delta zeta theta : k) (A B C0 : k[X]) : k[X] :=
  (-7 / 128 * beta : k) • A ^ 3 + (5 / 32 * delta : k) • A ^ 2 +
    (3 / 4 * gamma : k) • (A * B) + (21 / 16 * beta : k) • (A * C0) +
    (21 / 32 * beta : k) • B ^ 2 + (3 / 4 * zeta : k) • A +
    (5 / 4 * delta : k) • C0 + C theta

/-- Load part of `Z` after `l = 0`, excluding the cancelling
`alpha`/`epsilon`/`iota` terms. -/
def betaWallZRemainder410
    (beta gamma delta zeta eta : k) (A B C0 : k[X]) : k[X] :=
  -(1 / 16 * gamma : k) • A ^ 3 -
    (21 / 128 * beta : k) • (A ^ 2 * B) +
    (5 / 16 * delta : k) • (A * B) + (3 / 4 * gamma : k) • (A * C0) +
    (3 / 8 * gamma : k) • B ^ 2 + (21 / 16 * beta : k) • (B * C0) +
    (1 / 2 * eta : k) • A + (3 / 4 * zeta : k) • B

/-- Beta contribution to the terminal row. -/
def betaTerminalPolynomial410 (beta : k) (A B C0 : k[X]) : k[X] :=
  ((-7 / 128 * beta : k) • A ^ 3 + (21 / 16 * beta : k) • (A * C0) +
      (21 / 32 * beta : k) • B ^ 2) * derivative C0 -
    B * derivative
      ((-21 / 128 * beta : k) • (A ^ 2 * B) +
        (21 / 16 * beta : k) • (B * C0))

theorem integratedWPolynomial410_eq_zeroLoad_add_remainder
    (alpha beta gamma delta epsilon zeta theta : k) (A B C0 : k[X]) :
    integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0 =
      zeroLoadWPolynomial410 A B C0 +
        (2 * alpha : k) • (B * C0) + epsilon • B +
          betaWallWRemainder410 beta gamma delta zeta theta A B C0 := by
  simp only [integratedWPolynomial410, zeroLoadWPolynomial410,
    betaWallWRemainder410, zero_mul, zero_smul, add_zero, sub_zero]
  module

theorem integratedZPolynomial410_eq_zeroLoad_add_remainder
    (alpha beta gamma delta epsilon zeta eta iota : k) (A B C0 : k[X]) :
    integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta iota
        A B C0 =
      zeroLoadZPolynomial410 A B C0 + alpha • C0 ^ 2 + epsilon • C0 +
        C iota +
          betaWallZRemainder410 beta gamma delta zeta eta A B C0 := by
  simp only [integratedZPolynomial410, zeroLoadZPolynomial410,
    betaWallZRemainder410, zero_mul, zero_smul, add_zero, sub_zero]
  module

theorem betaWallWRemainder410_natDegree_le
    (beta gamma delta zeta theta : k) (A B C0 : k[X]) (n : ℕ)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n) :
    (betaWallWRemainder410 beta gamma delta zeta theta A B C0).natDegree ≤
      6 * n := by
  simp only [betaWallWRemainder410]
  compute_degree
  omega

theorem betaWallZRemainder410_natDegree_le
    (beta gamma delta zeta eta : k) (A B C0 : k[X]) (n : ℕ)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n) :
    (betaWallZRemainder410 beta gamma delta zeta eta A B C0).natDegree ≤
      7 * n := by
  simp only [betaWallZRemainder410]
  compute_degree
  omega

theorem lowerRow410_alphaEpsilon_cancel
    (alpha epsilon iota : k) (A B C0 : k[X]) :
    lowerRowZeroPolynomial410
        ((2 * alpha : k) • (B * C0) + epsilon • B)
        (alpha • C0 ^ 2 + epsilon • C0 + C iota) B C0 = 0 := by
  have h := lowerRow410_eq_zeroLoad_of_effectiveLoads_zero
    alpha epsilon iota A B C0
  have hW := integratedWPolynomial410_eq_zeroLoad_add_remainder
    alpha 0 0 0 epsilon 0 0 A B C0
  have hZ := integratedZPolynomial410_eq_zeroLoad_add_remainder
    alpha 0 0 0 epsilon 0 0 iota A B C0
  have hWrem :
      betaWallWRemainder410 0 0 0 0 0 A B C0 = 0 := by
    simp [betaWallWRemainder410]
  have hZrem :
      betaWallZRemainder410 0 0 0 0 0 A B C0 = 0 := by
    simp [betaWallZRemainder410]
  rw [hW, hZ, hWrem, hZrem, add_zero, add_zero] at h
  simp only [lowerRowZeroPolynomial410, derivative_add] at h ⊢
  linear_combination h

theorem lowerRow410_eq_zeroLoad_add_remainder
    (alpha beta gamma delta epsilon zeta eta theta iota : k)
    (A B C0 : k[X]) :
    lowerRowZeroPolynomial410
        (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
          A B C0)
        (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
          iota A B C0) B C0 =
      lowerRowZeroPolynomial410 (zeroLoadWPolynomial410 A B C0)
          (zeroLoadZPolynomial410 A B C0) B C0 +
        (betaWallWRemainder410 beta gamma delta zeta theta A B C0 *
            derivative C0 -
          B * derivative
            (betaWallZRemainder410 beta gamma delta zeta eta A B C0)) := by
  rw [integratedWPolynomial410_eq_zeroLoad_add_remainder,
    integratedZPolynomial410_eq_zeroLoad_add_remainder]
  have hcancel := lowerRow410_alphaEpsilon_cancel alpha epsilon iota A B C0
  simp only [lowerRowZeroPolynomial410, derivative_add] at hcancel ⊢
  linear_combination hcancel

theorem betaWallLoadRow410_natDegree_le
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) (n : ℕ)
    (hn : 0 < n) (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n) :
    (betaWallWRemainder410 beta gamma delta zeta theta A B C0 *
          derivative C0 -
        B * derivative
          (betaWallZRemainder410 beta gamma delta zeta eta
            A B C0)).natDegree ≤ 10 * n - 1 := by
  have hW := betaWallWRemainder410_natDegree_le
    beta gamma delta zeta theta A B C0 n hA hB hC0
  have hZ := betaWallZRemainder410_natDegree_le
    beta gamma delta zeta eta A B C0 n hA hB hC0
  have hdC : (derivative C0).natDegree ≤ 4 * n - 1 :=
    (natDegree_derivative_le C0).trans (by omega)
  have hdZ :
      (derivative (betaWallZRemainder410 beta gamma delta zeta eta
        A B C0)).natDegree ≤ 7 * n - 1 :=
    (natDegree_derivative_le _).trans (by omega)
  have hleft :
      (betaWallWRemainder410 beta gamma delta zeta theta A B C0 *
          derivative C0).natDegree ≤ 10 * n - 1 := by
    refine (natDegree_mul_le).trans ?_
    omega
  have hright :
      (B * derivative
          (betaWallZRemainder410 beta gamma delta zeta eta
            A B C0)).natDegree ≤ 10 * n - 1 := by
    refine (natDegree_mul_le).trans ?_
    omega
  exact (natDegree_sub_le _ _).trans (max_le hleft hright)

/-! ## Zero-load expansions and load-invisible coefficients -/

theorem zeroLoadTwo410_eq (A B C0 : k[X]) :
    firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 =
      (15 / 64 : k) • (A ^ 4 * B) - (15 / 8 : k) • (A ^ 2 * B * C0) -
        (5 / 8 : k) • (A * B ^ 3) + (15 / 4 : k) • (B * C0 ^ 2) := by
  simp [firstIntegralTwoPolynomial410]

theorem zeroLoadOne410_eq (A B C0 : k[X]) :
    firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 =
      -(5 / 256 : k) • A ^ 6 + (15 / 64 : k) • (A ^ 4 * C0) +
        (15 / 32 : k) • (A ^ 3 * B ^ 2) - (15 / 16 : k) • (A ^ 2 * C0 ^ 2) -
        (15 / 8 : k) • (A * B ^ 2 * C0) - (5 / 32 : k) • B ^ 4 +
        (5 / 4 : k) • C0 ^ 3 := by
  simp [firstIntegralOnePolynomial410]

theorem zeroLoadTwo410_coeff_eq_zero_of_l
    (l beta gamma delta zeta eta theta k₂ : k) (A B C0 : k[X])
    (n d : ℕ) (hn : 0 < n) (hd : 8 * n < d) (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n)
    (hTwo : firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
      A B C0 = C k₂) :
    (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0).coeff d = 0 := by
  have hload :
      (loadCorrectionTwoPolynomial410 l beta gamma delta zeta eta theta
        A B C0).natDegree < d :=
    (loadCorrectionTwoPolynomial410_natDegree_le_eightRadius_of_l
      l beta gamma delta zeta eta theta A B C0 n hn hl hA hB hC0).trans_lt hd
  have hconstant : (C k₂ : k[X]).coeff d = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hcoeff := congrArg (fun P : k[X] => P.coeff d) hTwo
  rw [firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection,
    coeff_add, coeff_eq_zero_of_natDegree_lt hload, add_zero,
    hconstant] at hcoeff
  exact hcoeff

theorem zeroLoadOne410_coeff_eq_zero_of_l
    (l beta gamma delta zeta eta theta k₁ : k) (A B C0 : k[X])
    (n d : ℕ) (hn : 0 < n) (hd : 9 * n < d) (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n)
    (hOne : firstIntegralOnePolynomial410 l beta gamma delta zeta eta theta
      A B C0 = C k₁) :
    (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).coeff d = 0 := by
  have hload :
      (loadCorrectionOnePolynomial410 l beta gamma delta zeta eta theta
        A B C0).natDegree < d :=
    (loadCorrectionOnePolynomial410_natDegree_le_nineRadius_of_l
      l beta gamma delta zeta eta theta A B C0 n hn hl hA hB hC0).trans_lt hd
  have hconstant : (C k₁ : k[X]).coeff d = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hcoeff := congrArg (fun P : k[X] => P.coeff d) hOne
  rw [firstIntegralOnePolynomial410_eq_zero_add_loadCorrection,
    coeff_add, coeff_eq_zero_of_natDegree_lt hload, add_zero,
    hconstant] at hcoeff
  exact hcoeff

theorem zeroLoadLowerRow410_coeff_eq_zero_of_l
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (n d : ℕ) (hn : 0 < n) (hd : 10 * n - 1 < d)
    (hl : l = 0) (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) :
    (lowerRowZeroPolynomial410 (zeroLoadWPolynomial410 A B C0)
      (zeroLoadZPolynomial410 A B C0) B C0).coeff d = 0 := by
  subst l
  have hload :
      (betaWallWRemainder410 beta gamma delta zeta theta A B C0 *
            derivative C0 -
          B * derivative
            (betaWallZRemainder410 beta gamma delta zeta eta
              A B C0)).natDegree < d :=
    (betaWallLoadRow410_natDegree_le
      beta gamma delta zeta eta theta A B C0 n hn hA hB hC0).trans_lt hd
  have hconstant : (C terminal : k[X]).coeff d = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hcoeff := congrArg (fun P : k[X] => P.coeff d) hLower
  rw [lowerRow410_eq_zeroLoad_add_remainder, coeff_add,
    coeff_eq_zero_of_natDegree_lt hload, add_zero, hconstant] at hcoeff
  exact hcoeff

/-! ## Cone classification of the beta faces -/

/-- The I2 beta face reaches `8n` only if `deg A = 2n` or `deg C0 = 4n`. -/
theorem betaLoadTwoPolynomial410_natDegree_eq_eightRadius_imp
    (beta : k) (A B C0 : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n)
    (hdeg : (betaLoadTwoPolynomial410 beta A B C0).natDegree = 8 * n) :
    A.natDegree = 2 * n ∨ C0.natDegree = 4 * n := by
  by_contra hfaces
  push_neg at hfaces
  have hA' : A.natDegree ≤ 2 * n - 1 := by omega
  have hC0' : C0.natDegree ≤ 4 * n - 1 := by omega
  have hlt : (betaLoadTwoPolynomial410 beta A B C0).natDegree < 8 * n := by
    simp only [betaLoadTwoPolynomial410]
    compute_degree
    omega
  omega

/-- The I1 beta face reaches `9n` only if `deg B = 3n`. -/
theorem betaLoadOnePolynomial410_natDegree_eq_nineRadius_imp
    (beta : k) (A B C0 : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n)
    (hdeg : (betaLoadOnePolynomial410 beta A B C0).natDegree = 9 * n) :
    B.natDegree = 3 * n := by
  by_contra hBne
  have hB' : B.natDegree ≤ 3 * n - 1 := by omega
  have hlt : (betaLoadOnePolynomial410 beta A B C0).natDegree < 9 * n := by
    simp only [betaLoadOnePolynomial410]
    compute_degree
    omega
  omega

/-! ## The degeneration `B = 0` -/

theorem firstIntegralTwoPolynomial410_of_B
    (l beta gamma delta zeta eta theta : k) (A C0 : k[X]) :
    firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta A 0 C0 =
      loadCorrectionTwoPolynomial410 l beta gamma delta zeta eta theta
        A 0 C0 := by
  rw [firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection]
  have hzero : firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A 0 C0 = 0 := by
    simp [firstIntegralTwoPolynomial410]
  rw [hzero, zero_add]

theorem firstIntegralOnePolynomial410_zeroLoad_of_B (A C0 : k[X]) :
    (256 : k) • firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A 0 C0 =
      -(5 : k) • (A ^ 2 - (4 : k) • C0) ^ 3 := by
  have h := firstIntegralOnePolynomial410_zero_discriminant A 0 C0
  have hcurve :
      alignedZeroCurveOnePolynomial410 A 0 (A ^ 2 - (4 : k) • C0) =
        - (A ^ 2 - (4 : k) • C0) ^ 3 := by
    simp [alignedZeroCurveOnePolynomial410]
  rw [h, hcurve]
  simp [smul_neg, ← neg_smul]

theorem betaLoadTwoPolynomial410_coeff
    (beta : k) (A B C0 : k[X]) (d : ℕ) :
    (betaLoadTwoPolynomial410 beta A B C0).coeff d =
      (35 / 512 * beta : k) * (A ^ 4).coeff d -
        (21 / 32 * beta : k) * (A ^ 2 * C0).coeff d -
        (21 / 32 * beta : k) * (A * B ^ 2).coeff d +
        (21 / 8 * beta : k) * (C0 ^ 2).coeff d := by
  simp only [betaLoadTwoPolynomial410]
  rw [coeff_add, coeff_sub, coeff_sub, coeff_smul, coeff_smul, coeff_smul,
    coeff_smul]
  simp only [smul_eq_mul]

theorem betaLoadTwoPolynomial410_coeff_of_B
    (beta : k) (A C0 : k[X]) (d : ℕ) :
    (betaLoadTwoPolynomial410 beta A 0 C0).coeff d =
      (35 / 512 * beta : k) * (A ^ 4).coeff d -
        (21 / 32 * beta : k) * (A ^ 2 * C0).coeff d +
        (21 / 8 * beta : k) * (C0 ^ 2).coeff d := by
  rw [betaLoadTwoPolynomial410_coeff]
  have hpow : ((0 : k[X]) ^ 2) = 0 :=
    zero_pow (by decide : (2 : ℕ) ≠ 0)
  rw [hpow, mul_zero, coeff_zero, mul_zero, sub_zero]

/-- On `B = 0` a nonconstant `A` with `2 deg A > deg C0` exposes the I2
beta monomial `A^4`. -/
theorem betaWall410_B_eq_zero_A_high_impossible
    (l beta gamma delta zeta eta theta k₂ : k) (A C0 : k[X])
    (hl : l = 0) (hbeta : beta ≠ 0)
    (hApos : 0 < A.natDegree)
    (hrel : C0.natDegree < 2 * A.natDegree)
    (hTwo : firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
      A 0 C0 = C k₂) : False := by
  subst l
  have hAne : A ≠ 0 := by
    intro hA0
    rw [hA0, natDegree_zero] at hApos
    exact lt_irrefl _ hApos
  have hA4 : (A ^ 4).natDegree = 4 * A.natDegree := by
    rw [natDegree_pow]
  have hC0' : C0.natDegree ≤ 2 * A.natDegree - 1 := by omega
  have hA2Cdeg : (A ^ 2 * C0).natDegree < 4 * A.natDegree := by
    compute_degree
    omega
  have hC02deg : (C0 ^ 2).natDegree < 4 * A.natDegree := by
    compute_degree
    omega
  have hrest :
      (betaLoadTwoRest410 gamma delta zeta eta theta A 0 C0).natDegree <
        4 * A.natDegree := by
    simp only [betaLoadTwoRest410, mul_zero, zero_mul, zero_smul, smul_zero,
      add_zero, sub_zero]
    compute_degree
    omega
  have hI2 := congrArg (fun P : k[X] => P.coeff (4 * A.natDegree)) hTwo
  rw [firstIntegralTwoPolynomial410_of_B,
    loadCorrectionTwoPolynomial410_eq_beta_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hI2
  have hA4coeff : (A ^ 4).coeff (4 * A.natDegree) =
      A.leadingCoeff ^ 4 := by
    rw [← hA4, coeff_natDegree, leadingCoeff_pow]
  have hz1 : (A ^ 2 * C0).coeff (4 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt hA2Cdeg
  have hz2 : (C0 ^ 2).coeff (4 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt hC02deg
  have hface :
      (betaLoadTwoPolynomial410 beta A 0 C0).coeff (4 * A.natDegree) =
        (35 / 512 * beta : k) * A.leadingCoeff ^ 4 := by
    rw [betaLoadTwoPolynomial410_coeff_of_B, hA4coeff, hz1, hz2]
    ring
  have hconstant : (C k₂ : k[X]).coeff (4 * A.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  rw [hface, hconstant] at hI2
  have hsc : (35 / 512 * beta : k) ≠ 0 :=
    mul_ne_zero (by norm_num) hbeta
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  exact (mul_ne_zero hsc (pow_ne_zero 4 hAle)) hI2

/-- On `B = 0` a nonconstant `C0` with `deg C0 > 2 deg A` exposes `C0^2`. -/
theorem betaWall410_B_eq_zero_C0_high_impossible
    (l beta gamma delta zeta eta theta k₂ : k) (A C0 : k[X])
    (hl : l = 0) (hbeta : beta ≠ 0)
    (hC0pos : 0 < C0.natDegree)
    (hrel : 2 * A.natDegree < C0.natDegree)
    (hTwo : firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
      A 0 C0 = C k₂) : False := by
  subst l
  have hC0ne : C0 ≠ 0 := by
    intro hC00
    rw [hC00, natDegree_zero] at hC0pos
    exact lt_irrefl _ hC0pos
  have hC02 : (C0 ^ 2).natDegree = 2 * C0.natDegree := by
    rw [natDegree_pow]
  have hA' : 2 * A.natDegree ≤ C0.natDegree - 1 := by omega
  have hA4deg : (A ^ 4).natDegree < 2 * C0.natDegree := by
    compute_degree
    omega
  have hA2Cdeg : (A ^ 2 * C0).natDegree < 2 * C0.natDegree := by
    compute_degree
    omega
  have hrest :
      (betaLoadTwoRest410 gamma delta zeta eta theta A 0 C0).natDegree <
        2 * C0.natDegree := by
    simp only [betaLoadTwoRest410, mul_zero, zero_mul, zero_smul, smul_zero,
      add_zero, sub_zero]
    compute_degree
    omega
  have hI2 := congrArg (fun P : k[X] => P.coeff (2 * C0.natDegree)) hTwo
  rw [firstIntegralTwoPolynomial410_of_B,
    loadCorrectionTwoPolynomial410_eq_beta_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hI2
  have hC02coeff : (C0 ^ 2).coeff (2 * C0.natDegree) =
      C0.leadingCoeff ^ 2 := by
    rw [← hC02, coeff_natDegree, leadingCoeff_pow]
  have hz1 : (A ^ 4).coeff (2 * C0.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt hA4deg
  have hz2 : (A ^ 2 * C0).coeff (2 * C0.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt hA2Cdeg
  have hface :
      (betaLoadTwoPolynomial410 beta A 0 C0).coeff (2 * C0.natDegree) =
        (21 / 8 * beta : k) * C0.leadingCoeff ^ 2 := by
    rw [betaLoadTwoPolynomial410_coeff_of_B, hz1, hz2, hC02coeff]
    ring
  have hconstant : (C k₂ : k[X]).coeff (2 * C0.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  rw [hface, hconstant] at hI2
  have hsc : (21 / 8 * beta : k) ≠ 0 :=
    mul_ne_zero (by norm_num) hbeta
  have hC0le : C0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hC0ne
  exact (mul_ne_zero hsc (pow_ne_zero 2 hC0le)) hI2

theorem betaWall410_B_eq_zero_balanced_drop_impossible
    (l beta gamma delta zeta eta theta k₂ : k) (A C0 : k[X])
    (hl : l = 0) (hbeta : beta ≠ 0) (hApos : 0 < A.natDegree)
    (heq : C0.natDegree = 2 * A.natDegree)
    (hdrop : A.leadingCoeff ^ 2 = 4 * C0.leadingCoeff)
    (hTwo : firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
      A 0 C0 = C k₂) : False := by
  subst l
  have hAne : A ≠ 0 := by
    intro hA0
    rw [hA0, natDegree_zero] at hApos
    exact lt_irrefl _ hApos
  have hC0ne : C0 ≠ 0 := by
    intro hC00
    rw [hC00, natDegree_zero] at heq
    omega
  have hA4 : (A ^ 4).natDegree = 4 * A.natDegree := by rw [natDegree_pow]
  have hA2C : (A ^ 2 * C0).natDegree = 4 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) hC0ne, natDegree_pow, heq]
    omega
  have hC02 : (C0 ^ 2).natDegree = 4 * A.natDegree := by
    rw [natDegree_pow, heq]
    omega
  have hA4coeff : (A ^ 4).coeff (4 * A.natDegree) =
      A.leadingCoeff ^ 4 := by
    rw [← hA4, coeff_natDegree, leadingCoeff_pow]
  have hA2Ccoeff : (A ^ 2 * C0).coeff (4 * A.natDegree) =
      A.leadingCoeff ^ 2 * C0.leadingCoeff := by
    rw [← hA2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hC02coeff : (C0 ^ 2).coeff (4 * A.natDegree) =
      C0.leadingCoeff ^ 2 := by
    rw [← hC02, coeff_natDegree, leadingCoeff_pow]
  have hrestLt :
      (betaLoadTwoRest410 gamma delta zeta eta theta A 0 C0).natDegree <
        4 * A.natDegree := by
    simp only [betaLoadTwoRest410, mul_zero, zero_mul, zero_smul, smul_zero,
      add_zero, sub_zero]
    compute_degree
    omega
  have hI2 := congrArg (fun P : k[X] => P.coeff (4 * A.natDegree)) hTwo
  rw [firstIntegralTwoPolynomial410_of_B,
    loadCorrectionTwoPolynomial410_eq_beta_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrestLt, add_zero] at hI2
  have hbetaFace :
      (betaLoadTwoPolynomial410 beta A 0 C0).coeff (4 * A.natDegree) =
        (35 / 512 * beta : k) * A.leadingCoeff ^ 4 := by
    rw [betaLoadTwoPolynomial410_coeff_of_B, hA4coeff, hA2Ccoeff, hC02coeff]
    have hcancel :
        (21 / 32 * beta : k) *
            (A.leadingCoeff ^ 2 * C0.leadingCoeff) =
          (21 / 8 * beta : k) * C0.leadingCoeff ^ 2 := by
      rw [hdrop]
      have hmul : (4 * C0.leadingCoeff) * C0.leadingCoeff =
          (4 : k) * C0.leadingCoeff ^ 2 := by
        simp [pow_two, mul_assoc]
      rw [hmul, ← mul_assoc]
      have hnum : (21 / 32 * beta : k) * 4 = (21 / 8 * beta : k) := by
        have h : (21 / 32 * 4 : k) = (21 / 8 : k) := by norm_num
        rw [mul_right_comm, h]
      rw [hnum]
    rw [hcancel, sub_add_cancel]
  rw [hbetaFace] at hI2
  have hconstant : (C k₂ : k[X]).coeff (4 * A.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  rw [hconstant] at hI2
  have hsc : (35 / 512 * beta : k) ≠ 0 :=
    mul_ne_zero (by norm_num) hbeta
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  exact (mul_ne_zero hsc (pow_ne_zero 4 hAle)) hI2

theorem betaWall410_B_eq_zero_balanced_nodrop_impossible
    (l beta gamma delta zeta eta theta k₁ : k) (A C0 : k[X])
    (hl : l = 0) (hApos : 0 < A.natDegree)
    (heq : C0.natDegree = 2 * A.natDegree)
    (hnodrop : A.leadingCoeff ^ 2 ≠ 4 * C0.leadingCoeff)
    (hOne : firstIntegralOnePolynomial410 l beta gamma delta zeta eta theta
      A 0 C0 = C k₁) : False := by
  have hAne : A ≠ 0 := by
    intro hA0
    rw [hA0, natDegree_zero] at hApos
    exact lt_irrefl _ hApos
  have hC0ne : C0 ≠ 0 := by
    intro hC00
    rw [hC00, natDegree_zero] at heq
    omega
  have hU :
      (A ^ 2 - (4 : k) • C0).natDegree = 2 * A.natDegree := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · exact (natDegree_sub_le _ _).trans <| max_le
        (by rw [natDegree_pow])
        (by rw [natDegree_smul C0 (by norm_num : (4 : k) ≠ 0), heq])
    · have hA2 : (A ^ 2).coeff (2 * A.natDegree) =
          A.leadingCoeff ^ 2 := by
        have hdeg : (A ^ 2).natDegree = 2 * A.natDegree := by
          rw [natDegree_pow]
        rw [← hdeg, coeff_natDegree, leadingCoeff_pow]
      have h4C : ((4 : k) • C0).coeff (2 * A.natDegree) =
          4 * C0.leadingCoeff := by
        rw [coeff_smul, smul_eq_mul, ← heq, coeff_natDegree]
      rw [coeff_sub, hA2, h4C]
      exact sub_ne_zero.mpr hnodrop
  have hUne : A ^ 2 - (4 : k) • C0 ≠ 0 := by
    intro hU0
    rw [hU0, natDegree_zero] at hU
    omega
  have hload :
      (loadCorrectionOnePolynomial410 l beta gamma delta zeta eta theta
        A 0 C0).natDegree < 3 * (A ^ 2 - (4 : k) • C0).natDegree := by
    subst l
    simp only [loadCorrectionOnePolynomial410, mul_zero, zero_mul,
      zero_smul, smul_zero, add_zero, sub_zero]
    compute_degree
    omega
  have hI1 := congrArg
    (fun P : k[X] => P.coeff (3 * (A ^ 2 - (4 : k) • C0).natDegree)) hOne
  have hconstant :
      (C k₁ : k[X]).coeff (3 * (A ^ 2 - (4 : k) • C0).natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  rw [firstIntegralOnePolynomial410_eq_zero_add_loadCorrection, coeff_add,
    coeff_eq_zero_of_natDegree_lt hload, add_zero, hconstant] at hI1
  have hscale := firstIntegralOnePolynomial410_zeroLoad_of_B A C0
  have hU3 :
      ((A ^ 2 - (4 : k) • C0) ^ 3).natDegree =
        3 * (A ^ 2 - (4 : k) • C0).natDegree := by
    rw [natDegree_pow]
  have hU3coeff :
      ((A ^ 2 - (4 : k) • C0) ^ 3).coeff
        (3 * (A ^ 2 - (4 : k) • C0).natDegree) =
        (A ^ 2 - (4 : k) • C0).leadingCoeff ^ 3 := by
    rw [← hU3, coeff_natDegree, leadingCoeff_pow]
  have h256coeff := congrArg
    (fun P : k[X] => P.coeff (3 * (A ^ 2 - (4 : k) • C0).natDegree)) hscale
  simp only [coeff_smul, hU3coeff, smul_eq_mul] at h256coeff
  rw [hI1, mul_zero] at h256coeff
  have hUle : (A ^ 2 - (4 : k) • C0).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr hUne
  have hsc : -(5 : k) ≠ 0 := by norm_num
  exact (mul_ne_zero hsc (pow_ne_zero 3 hUle)) h256coeff.symm

theorem betaWall410_B_eq_zero_constants_impossible
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A C0 : k[X]) (hA : A.natDegree = 0) (hC0 : C0.natDegree = 0)
    (hterminal : terminal ≠ 0)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A 0 C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A 0 C0) 0 C0 = C terminal) : False := by
  have hterm :
      lowerRowZeroPolynomial410
        (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta
          theta A 0 C0)
        (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
          iota A 0 C0) 0 C0 = 0 := by
    simp only [lowerRowZeroPolynomial410, zero_mul, sub_zero]
    have hdC : derivative C0 = 0 := by
      rw [eq_C_of_natDegree_eq_zero hC0, derivative_C]
    rw [hdC, mul_zero]
  rw [hterm] at hLower
  exact hterminal (C_eq_zero.mp hLower.symm)

theorem betaWall410_B_eq_zero_impossible
    (l alpha beta gamma delta epsilon zeta eta theta iota k₂ k₁
      terminal : k)
    (A C0 : k[X]) (hl : l = 0) (hbeta : beta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
      A 0 C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410 l beta gamma delta zeta eta theta
      A 0 C0 = C k₁)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A 0 C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A 0 C0) 0 C0 = C terminal) : False := by
  rcases lt_trichotomy (2 * A.natDegree) C0.natDegree with hlt | heq | hgt
  · exact betaWall410_B_eq_zero_C0_high_impossible
      l beta gamma delta zeta eta theta k₂ A C0 hl hbeta
      (by omega) hlt hTwo
  · by_cases hApos : 0 < A.natDegree
    · have heq' : C0.natDegree = 2 * A.natDegree := heq.symm
      by_cases hdrop : A.leadingCoeff ^ 2 = 4 * C0.leadingCoeff
      · exact betaWall410_B_eq_zero_balanced_drop_impossible
          l beta gamma delta zeta eta theta k₂ A C0 hl hbeta hApos heq'
          hdrop hTwo
      · exact betaWall410_B_eq_zero_balanced_nodrop_impossible
          l beta gamma delta zeta eta theta k₁ A C0 hl hApos heq' hdrop
          hOne
    · exact betaWall410_B_eq_zero_constants_impossible
        l alpha beta gamma delta epsilon zeta eta theta iota terminal A C0
        (by omega) (by omega) hterminal hLower
  · exact betaWall410_B_eq_zero_A_high_impossible
      l beta gamma delta zeta eta theta k₂ A C0 hl hbeta
      (by omega) hgt hTwo


/-! ## Residual packet -/

/-- After `l = 0` and the degeneration `B = 0`, the beta wall remains on
the aligned source cone with `B ≠ 0`. -/
def BetaWallResidual410 (n : ℕ) (A B C0 : k[X]) : Prop :=
  B ≠ 0 ∧ A.natDegree ≤ 2 * n ∧ B.natDegree ≤ 3 * n ∧ C0.natDegree ≤ 4 * n

theorem constantIntegral410_betaWall_obstruction
    (l alpha beta gamma delta epsilon zeta eta theta iota k₂ k₁
      terminal : k)
    (A B C0 : k[X]) (n : ℕ) (_hn : 0 < n) (hl : l = 0) (hbeta : beta ≠ 0)
    (hterminal : terminal ≠ 0)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n)
    (hTwo : firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
      A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410 l beta gamma delta zeta eta theta
      A B C0 = C k₁)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) :
    BetaWallResidual410 n A B C0 := by
  refine ⟨?_, hA, hB, hC0⟩
  intro hB0
  exact betaWall410_B_eq_zero_impossible
    l alpha beta gamma delta epsilon zeta eta theta iota k₂ k₁ terminal
    A C0 hl hbeta hterminal (by simpa [hB0] using hTwo)
    (by simpa [hB0] using hOne) (by simpa [hB0] using hLower)

end BetaWall410

end Max11DegreeRoutes
