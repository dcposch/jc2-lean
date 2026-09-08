import LowScale410ZeroLoadShiftedFiber

/-!
# Load cascade for the `(4,10)`, scale-zero leaf

On the aligned coefficient cone `deg A ≤ 2n`, `deg B ≤ 3n`,
`deg C0 ≤ 4n`, every integration-constant load lies strictly below the two
zero-load Newton faces.  This file isolates the two load remainders and
proves their sharp bounds `10n` and `11n`; consequently any constant first
integrals have exactly the same coefficients at radii `11n` and `12n` as
the zero-load invariants.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section LoadCascade410

variable {k : Type*} [Field k] [CharZero k]

/-- All terms of the first (`z²`) invariant containing an integration
constant load. -/
def loadCorrectionTwoPolynomial410
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  (63 / 2048 * l : k) • A ^ 5 - (45 / 128 * l : k) • (A ^ 3 * C0) -
    (135 / 256 * l : k) • (A ^ 2 * B ^ 2) +
    (45 / 32 * l : k) • (A * C0 ^ 2) +
    (45 / 32 * l : k) • (B ^ 2 * C0) +
    (35 / 512 * beta : k) • A ^ 4 -
    (21 / 32 * beta : k) • (A ^ 2 * C0) -
    (21 / 32 * beta : k) • (A * B ^ 2) +
    (21 / 8 * beta : k) • C0 ^ 2 -
    (3 / 4 * gamma : k) • (A ^ 2 * B) +
    (3 * gamma : k) • (B * C0) -
    (5 / 32 * delta : k) • A ^ 3 +
    (5 / 4 * delta : k) • (A * C0) +
    (5 / 8 * delta : k) • B ^ 2 -
    (3 / 8 * zeta : k) • A ^ 2 + (3 * zeta : k) • C0 +
    (2 * eta : k) • B + theta • A

/-- All terms of the second (`z`) invariant containing an integration
constant load. -/
def loadCorrectionOnePolynomial410
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  (315 / 2048 * l : k) • (A ^ 4 * B) -
    (135 / 128 * l : k) • (A ^ 2 * B * C0) -
    (45 / 128 * l : k) • (A * B ^ 3) +
    (45 / 32 * l : k) • (B * C0 ^ 2) +
    (35 / 128 * beta : k) • (A ^ 3 * B) -
    (21 / 16 * beta : k) • (A * B * C0) -
    (7 / 32 * beta : k) • B ^ 3 +
    (3 / 32 * gamma : k) • A ^ 4 -
    (3 / 4 * gamma : k) • (A ^ 2 * C0) -
    (3 / 4 * gamma : k) • (A * B ^ 2) +
    (3 / 2 * gamma : k) • C0 ^ 2 -
    (15 / 32 * delta : k) • (A ^ 2 * B) +
    (5 / 4 * delta : k) • (B * C0) -
    (3 / 4 * zeta : k) • (A * B) -
    (1 / 2 * eta : k) • A ^ 2 + (2 * eta : k) • C0 + theta • B

/-- Exact separation of the first invariant into its zero-load Newton
polynomial and its lower load remainder. -/
theorem firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta A B C0 =
      firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 +
        loadCorrectionTwoPolynomial410 l beta gamma delta zeta eta theta
          A B C0 := by
  simp only [firstIntegralTwoPolynomial410, loadCorrectionTwoPolynomial410,
    zero_mul, zero_smul, add_zero, sub_zero]
  module

/-- Exact separation of the second invariant. -/
theorem firstIntegralOnePolynomial410_eq_zero_add_loadCorrection
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    firstIntegralOnePolynomial410 l beta gamma delta zeta eta theta A B C0 =
      firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 +
        loadCorrectionOnePolynomial410 l beta gamma delta zeta eta theta
          A B C0 := by
  simp only [firstIntegralOnePolynomial410, loadCorrectionOnePolynomial410,
    zero_mul, zero_smul, add_zero, sub_zero]
  module

/-- The complete load remainder of the first invariant is at most `10n` on
the aligned `(2,3,4)` coefficient cone. -/
theorem loadCorrectionTwoPolynomial410_natDegree_le
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (n : ℕ) (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n) :
    (loadCorrectionTwoPolynomial410 l beta gamma delta zeta eta theta
      A B C0).natDegree ≤ 10 * n := by
  simp only [loadCorrectionTwoPolynomial410]
  compute_degree
  omega

/-- The complete load remainder of the second invariant is at most `11n` on
the same cone. -/
theorem loadCorrectionOnePolynomial410_natDegree_le
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (n : ℕ) (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n) :
    (loadCorrectionOnePolynomial410 l beta gamma delta zeta eta theta
      A B C0).natDegree ≤ 11 * n := by
  simp only [loadCorrectionOnePolynomial410]
  compute_degree
  omega

/-- At the first Newton radius, arbitrary loads are invisible: a constant
full invariant forces the zero-load face coefficient to vanish. -/
theorem zeroLoadFirstIntegralTwo410_coeff_elevenRadius_eq_zero
    (l beta gamma delta zeta eta theta k₂ : k) (A B C0 : k[X])
    (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n)
    (hInvariant :
      firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
        A B C0 = C k₂) :
    (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0).coeff
      (11 * n) = 0 := by
  have hload :
      (loadCorrectionTwoPolynomial410 l beta gamma delta zeta eta theta
        A B C0).natDegree < 11 * n :=
    (loadCorrectionTwoPolynomial410_natDegree_le
      l beta gamma delta zeta eta theta A B C0 n hA hB hC0).trans_lt (by omega)
  have hconstant : (C k₂ : k[X]).coeff (11 * n) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hcoeff := congrArg (fun P : k[X] => P.coeff (11 * n)) hInvariant
  rw [firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection,
    coeff_add, coeff_eq_zero_of_natDegree_lt hload, add_zero, hconstant] at hcoeff
  exact hcoeff

/-- The analogous load-independence statement at radius `12n`. -/
theorem zeroLoadFirstIntegralOne410_coeff_twelveRadius_eq_zero
    (l beta gamma delta zeta eta theta k₁ : k) (A B C0 : k[X])
    (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC0 : C0.natDegree ≤ 4 * n)
    (hInvariant :
      firstIntegralOnePolynomial410 l beta gamma delta zeta eta theta
        A B C0 = C k₁) :
    (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).coeff
      (12 * n) = 0 := by
  have hload :
      (loadCorrectionOnePolynomial410 l beta gamma delta zeta eta theta
        A B C0).natDegree < 12 * n :=
    (loadCorrectionOnePolynomial410_natDegree_le
      l beta gamma delta zeta eta theta A B C0 n hA hB hC0).trans_lt (by omega)
  have hconstant : (C k₁ : k[X]).coeff (12 * n) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hcoeff := congrArg (fun P : k[X] => P.coeff (12 * n)) hInvariant
  rw [firstIntegralOnePolynomial410_eq_zero_add_loadCorrection,
    coeff_add, coeff_eq_zero_of_natDegree_lt hload, add_zero, hconstant] at hcoeff
  exact hcoeff

/-! ## The exact terminal load wall -/

/-- Polynomial representative of the integrated `W` coefficient, including
all constant loads. -/
def integratedWPolynomial410
    (l alpha beta gamma delta epsilon zeta theta : k)
    (A B C0 : k[X]) : k[X] :=
  (-45 / 2048 * l : k) • A ^ 4 - (5 / 32 : k) • (A ^ 3 * B) -
    (7 / 128 * beta : k) • A ^ 3 +
    (45 / 128 * l : k) • (A ^ 2 * C0) +
    (45 / 128 * l : k) • (A * B ^ 2) +
    (5 / 32 * delta : k) • A ^ 2 + (15 / 8 : k) • (A * B * C0) +
    (3 / 4 * gamma : k) • (A * B) +
    (21 / 16 * beta : k) • (A * C0) + (5 / 16 : k) • B ^ 3 +
    (21 / 32 * beta : k) • B ^ 2 + (2 * alpha : k) • (B * C0) +
    (45 / 32 * l : k) • C0 ^ 2 + (3 / 4 * zeta : k) • A +
    epsilon • B + (5 / 4 * delta : k) • C0 + C theta

/-- Polynomial representative of the integrated `Z` coefficient. -/
def integratedZPolynomial410
    (l alpha beta gamma delta epsilon zeta eta iota : k)
    (A B C0 : k[X]) : k[X] :=
  (3 / 256 : k) • A ^ 5 - (45 / 512 * l : k) • (A ^ 3 * B) -
    (5 / 32 : k) • (A ^ 3 * C0) - (1 / 16 * gamma : k) • A ^ 3 -
    (15 / 64 : k) • (A ^ 2 * B ^ 2) -
    (21 / 128 * beta : k) • (A ^ 2 * B) +
    (45 / 64 * l : k) • (A * B * C0) +
    (15 / 128 * l : k) • B ^ 3 +
    (5 / 16 * delta : k) • (A * B) + (15 / 16 : k) • (A * C0 ^ 2) +
    (3 / 4 * gamma : k) • (A * C0) + (15 / 16 : k) • (B ^ 2 * C0) +
    (3 / 8 * gamma : k) • B ^ 2 +
    (21 / 16 * beta : k) • (B * C0) + alpha • C0 ^ 2 +
    (1 / 2 * eta : k) • A + (3 / 4 * zeta : k) • B +
    epsilon • C0 + C iota

/-- The three loads `alpha`, `epsilon`, and `iota` cancel identically from
the terminal row.  Once the seven effective loads vanish, the row is
literally the zero-load row already excluded above. -/
theorem lowerRow410_eq_zeroLoad_of_effectiveLoads_zero
    (alpha epsilon iota : k) (A B C0 : k[X]) :
    lowerRowZeroPolynomial410
        (integratedWPolynomial410 0 alpha 0 0 0 epsilon 0 0 A B C0)
        (integratedZPolynomial410 0 alpha 0 0 0 epsilon 0 0 iota A B C0)
        B C0 =
      lowerRowZeroPolynomial410 (zeroLoadWPolynomial410 A B C0)
        (zeroLoadZPolynomial410 A B C0) B C0 := by
  have hW :
      integratedWPolynomial410 0 alpha 0 0 0 epsilon 0 0 A B C0 =
        zeroLoadWPolynomial410 A B C0 +
          alpha • (B * C0) + alpha • (B * C0) + epsilon • B := by
    simp [integratedWPolynomial410, zeroLoadWPolynomial410]
    module
  have hZ :
      integratedZPolynomial410 0 alpha 0 0 0 epsilon 0 0 iota A B C0 =
        zeroLoadZPolynomial410 A B C0 + alpha • C0 ^ 2 +
          epsilon • C0 + C iota := by
    simp [integratedZPolynomial410, zeroLoadZPolynomial410]
  rw [hW, hZ]
  simp only [lowerRowZeroPolynomial410, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_smul,
    Polynomial.derivative_C, add_zero, Polynomial.smul_eq_C_mul]
  push_cast
  simp only [Polynomial.C_ofNat]
  ring

/-- Exact first load-cascade split.  Any hypothetical constant-integral
trajectory with nonzero terminal row lies on one of the seven effective load
walls.  There is no wall involving `alpha`, `epsilon`, or `iota`. -/
theorem constantIntegral410_effectiveLoadWall
    (l alpha beta gamma delta epsilon zeta eta theta iota k₂ k₁ terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
      A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410 l beta gamma delta zeta eta theta
      A B C0 = C k₁)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) :
    l ≠ 0 ∨ beta ≠ 0 ∨ gamma ≠ 0 ∨ delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨
      theta ≠ 0 := by
  by_contra hwall
  push_neg at hwall
  obtain ⟨hl, hbeta, hgamma, hdelta, hzeta, heta, htheta⟩ := hwall
  subst l
  subst beta
  subst gamma
  subst delta
  subst zeta
  subst eta
  subst theta
  have hLowerZero :
      lowerRowZeroPolynomial410 (zeroLoadWPolynomial410 A B C0)
        (zeroLoadZPolynomial410 A B C0) B C0 = C terminal := by
    rw [← lowerRow410_eq_zeroLoad_of_effectiveLoads_zero alpha epsilon iota]
    exact hLower
  exact zeroLoad410_allConstantFibers_trajectory_impossible
    A B C0 k₂ k₁ terminal hterminal hTwo hOne hLowerZero

end LoadCascade410

end Max11DegreeRoutes
