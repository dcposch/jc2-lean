import LowScale410FirstIntegrals

/-!
# Polynomial trajectory reductions for the `(4,10)`, scale-zero leaf

The quartic discriminant coordinate `U = A^2 - 4 C0` exposes a particularly
small aligned-zero terminal system.  This module proves the zero-first-
invariant branch impossible and records the exact finite system used by the
remaining scalar branches.
-/

noncomputable section

set_option maxHeartbeats 2000000

open Polynomial

namespace Max11DegreeRoutes

section AlignedZeroTrajectory410

variable {k : Type*} [Field k] [CharZero k]

/-- Scaled first invariant in discriminant coordinates when all load
constants vanish. -/
def alignedZeroCurveTwoPolynomial410 (A B U : k[X]) : k[X] :=
  B * ((3 : k) • U ^ 2 - (8 : k) • (A * B ^ 2))

/-- Scaled second invariant in the same zero-load branch. -/
def alignedZeroCurveOnePolynomial410 (A B U : k[X]) : k[X] :=
  (24 : k) • (A * B ^ 2 * U) - (8 : k) • B ^ 4 - U ^ 3

/-- Scaled terminal one-form in discriminant coordinates. -/
def alignedZeroEtaPolynomial410 (A B U : k[X]) : k[X] :=
  B * ((8 : k) • (A * B ^ 2) - (3 : k) • U ^ 2) * derivative A +
    (24 : k) • (B ^ 2 * U * derivative B) +
    (8 : k) • (B ^ 3 * derivative U)

/-- The first zero-load invariant is the factored polynomial displayed
above in the denominator-free coordinate `U = A^2 - 4 C0`. -/
theorem firstIntegralTwoPolynomial410_zero_discriminant
    (A B C0 : k[X]) :
    (64 : k) • firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 =
      (5 : k) • alignedZeroCurveTwoPolynomial410 A B
        (A ^ 2 - (4 : k) • C0) := by
  simp [firstIntegralTwoPolynomial410, alignedZeroCurveTwoPolynomial410,
    Polynomial.smul_eq_C_mul, Polynomial.C_eq_natCast]
  ring_nf
  simp only [← Polynomial.C_mul]
  norm_num
  have h15 : C (15 : k) = C (5 : k) * C (3 : k) := by
    norm_num [← Polynomial.C_mul]
  have h58 : C (64 : k) * C (5 / 8 : k) =
      C (5 : k) * C (8 : k) := by
    norm_num [← Polynomial.C_mul]
  have h158 : C (64 : k) * C (15 / 8 : k) =
      C (5 : k) * C (3 : k) * C (4 : k) * C (2 : k) := by
    norm_num [← Polynomial.C_mul, ← Polynomial.C_pow]
  have h154 : C (64 : k) * C (15 / 4 : k) =
      C (5 : k) * C (3 : k) * C (4 : k) ^ 2 := by
    norm_num [← Polynomial.C_mul, ← Polynomial.C_pow]
  have hC2 : (2 : k[X]) = C (2 : k) := (Polynomial.C_ofNat 2).symm
  rw [hC2]
  linear_combination A ^ 4 * B * h15 - A * B ^ 3 * h58 -
    A ^ 2 * B * C0 * h158 + B * C0 ^ 2 * h154

/-- The corresponding exact identity for the second invariant. -/
theorem firstIntegralOnePolynomial410_zero_discriminant
    (A B C0 : k[X]) :
    (256 : k) • firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 =
      (5 : k) • alignedZeroCurveOnePolynomial410 A B
        (A ^ 2 - (4 : k) • C0) := by
  simp [firstIntegralOnePolynomial410, alignedZeroCurveOnePolynomial410,
    Polynomial.smul_eq_C_mul, Polynomial.C_eq_natCast]
  ring_nf
  simp only [← Polynomial.C_mul]
  norm_num
  have h158 : C (256 : k) * C (15 / 8 : k) =
      C (5 : k) * C (24 : k) * C (4 : k) := by
    norm_num [← Polynomial.C_mul]
  have h1516 : C (256 : k) * C (15 / 16 : k) =
      C (5 : k) * C (4 : k) ^ 2 * C (3 : k) := by
    norm_num [← Polynomial.C_mul, ← Polynomial.C_pow]
  have h1532 : C (256 : k) * C (15 / 32 : k) =
      C (5 : k) * C (24 : k) := by
    norm_num [← Polynomial.C_mul]
  have h1564 : C (256 : k) * C (15 / 64 : k) =
      C (5 : k) * C (4 : k) * C (3 : k) := by
    norm_num [← Polynomial.C_mul]
  have h54 : C (256 : k) * C (5 / 4 : k) =
      C (5 : k) * C (4 : k) ^ 3 := by
    norm_num [← Polynomial.C_mul, ← Polynomial.C_pow]
  have h532 : C (256 : k) * C (5 / 32 : k) =
      C (5 : k) * C (8 : k) := by
    norm_num [← Polynomial.C_mul]
  have hC3 : (3 : k[X]) = C (3 : k) := (Polynomial.C_ofNat 3).symm
  rw [hC3]
  linear_combination -A * C0 * B ^ 2 * h158 -
    A ^ 2 * C0 ^ 2 * h1516 + A ^ 3 * B ^ 2 * h1532 +
    A ^ 4 * C0 * h1564 + C0 ^ 3 * h54 - B ^ 4 * h532

/-- The zero-load specialization of the integrated coefficient `W`. -/
def zeroLoadWPolynomial410 (A B C0 : k[X]) : k[X] :=
  -(5 / 32 : k) • (A ^ 3 * B) + (15 / 8 : k) • (A * B * C0) +
    (5 / 16 : k) • B ^ 3

/-- The zero-load specialization of the integrated coefficient `Z`. -/
def zeroLoadZPolynomial410 (A B C0 : k[X]) : k[X] :=
  (3 / 256 : k) • A ^ 5 - (5 / 32 : k) • (A ^ 3 * C0) -
    (15 / 64 : k) • (A ^ 2 * B ^ 2) +
    (15 / 16 : k) • (A * C0 ^ 2) + (15 / 16 : k) • (B ^ 2 * C0)

/-- Integer-coefficient numerator of `zeroLoadWPolynomial410`. -/
def scaledZeroLoadWPolynomial410 (A B C0 : k[X]) : k[X] :=
  -(40 : k) • (A ^ 3 * B) + (480 : k) • (A * B * C0) +
    (80 : k) • B ^ 3

/-- Integer-coefficient numerator of `zeroLoadZPolynomial410`. -/
def scaledZeroLoadZPolynomial410 (A B C0 : k[X]) : k[X] :=
  (3 : k) • A ^ 5 - (40 : k) • (A ^ 3 * C0) -
    (60 : k) • (A ^ 2 * B ^ 2) + (240 : k) • (A * C0 ^ 2) +
    (240 : k) • (B ^ 2 * C0)

theorem scaled_zeroLoadWPolynomial410 (A B C0 : k[X]) :
    (256 : k) • zeroLoadWPolynomial410 A B C0 =
      scaledZeroLoadWPolynomial410 A B C0 := by
  simp only [zeroLoadWPolynomial410, scaledZeroLoadWPolynomial410]
  module

theorem scaled_zeroLoadZPolynomial410 (A B C0 : k[X]) :
    (256 : k) • zeroLoadZPolynomial410 A B C0 =
      scaledZeroLoadZPolynomial410 A B C0 := by
  simp only [zeroLoadZPolynomial410, scaledZeroLoadZPolynomial410]
  module

/-- Exact bridge from the surviving lower row `W C0' - B Z'` to the
discriminant-coordinate terminal form. -/
theorem zeroLoadLowerRow410_discriminant (A B C0 : k[X]) :
    (256 : k) • lowerRowZeroPolynomial410
        (zeroLoadWPolynomial410 A B C0) (zeroLoadZPolynomial410 A B C0)
        B C0 =
      (5 : k) • alignedZeroEtaPolynomial410 A B
        (A ^ 2 - (4 : k) • C0) := by
  have hdZ := congrArg derivative (scaled_zeroLoadZPolynomial410 A B C0)
  simp only [Polynomial.derivative_smul] at hdZ
  have hrow :
      (256 : k) • lowerRowZeroPolynomial410
          (zeroLoadWPolynomial410 A B C0) (zeroLoadZPolynomial410 A B C0)
          B C0 =
        ((256 : k) • zeroLoadWPolynomial410 A B C0) * derivative C0 -
          B * ((256 : k) • derivative (zeroLoadZPolynomial410 A B C0)) := by
    simp only [lowerRowZeroPolynomial410, Polynomial.smul_eq_C_mul]
    ring
  rw [hrow, scaled_zeroLoadWPolynomial410, hdZ]
  simp only [scaledZeroLoadWPolynomial410, scaledZeroLoadZPolynomial410,
    alignedZeroEtaPolynomial410, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_neg,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_smul, Polynomial.smul_eq_C_mul]
  push_cast
  simp only [Polynomial.C_neg, Polynomial.C_ofNat,
    Polynomial.derivative_ofNat, zero_mul,
    mul_zero, add_zero, sub_zero]
  ring

/-- On the zero locus of the first invariant, the remaining invariant is a
polynomial Catalan equation and the terminal row is the derivative of the
single monomial `B^3 U`. -/
theorem alignedZero410_reducedFermatSystem
    (A B U : k[X]) (hB : B ≠ 0)
    (hTwo : alignedZeroCurveTwoPolynomial410 A B U = 0) :
    alignedZeroCurveOnePolynomial410 A B U =
        (8 : k) • (U ^ 3 - B ^ 4) ∧
      alignedZeroEtaPolynomial410 A B U =
        (8 : k) • derivative (B ^ 3 * U) := by
  have hcore : (3 : k) • U ^ 2 - (8 : k) • (A * B ^ 2) = 0 := by
    apply mul_left_cancel₀ hB
    simpa only [alignedZeroCurveTwoPolynomial410, mul_zero] using hTwo
  constructor
  · simp only [alignedZeroCurveOnePolynomial410,
      Polynomial.smul_eq_C_mul] at hcore ⊢
    simp only [Polynomial.C_ofNat] at hcore ⊢
    ring_nf at hcore ⊢
    linear_combination -3 * U * hcore
  · simp only [alignedZeroEtaPolynomial410,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.smul_eq_C_mul] at hcore ⊢
    push_cast
    simp only [Polynomial.C_ofNat] at hcore ⊢
    ring_nf at hcore ⊢
    linear_combination -B * derivative A * hcore

/-- A nonzero constant derivative forces its polynomial primitive to have
exact degree one. -/
theorem natDegree_eq_one_of_scaledDerivative_eq_nonzero_C410
    (P : k[X]) (j : k) (hj : j ≠ 0)
    (h : (8 : k) • derivative P = C j) :
    P.natDegree = 1 := by
  have hder : derivative P ≠ 0 := by
    intro hz
    rw [hz, smul_zero] at h
    exact hj (C_eq_zero.mp h.symm)
  have hdegder : (derivative P).natDegree = 0 := by
    have hd := congrArg Polynomial.natDegree h
    simpa only [Polynomial.smul_eq_C_mul,
      natDegree_C_mul (show (8 : k) ≠ 0 by norm_num), natDegree_C] using hd
  have hpositive : 0 < P.natDegree :=
    Nat.pos_of_ne_zero (derivative_ne_zero.mp hder)
  rw [natDegree_derivative] at hdegder
  omega

/-- The zero value of the first invariant cannot support a polynomial
trajectory with nonzero constant terminal row.  The proof is a short degree
cascade: the two curve rows reduce to `U^3-B^4 = const`, while the terminal
row forces `deg(B^3 U)=1`. -/
theorem alignedZero410_zeroFirstInvariant_trajectory_impossible
    (A B U : k[X]) (k1 j : k) (hj : j ≠ 0)
    (hTwo : alignedZeroCurveTwoPolynomial410 A B U = 0)
    (hOne : alignedZeroCurveOnePolynomial410 A B U = C k1)
    (hEta : alignedZeroEtaPolynomial410 A B U = C j) : False := by
  by_cases hB : B = 0
  · subst B
    simp [alignedZeroEtaPolynomial410] at hEta
    exact hj (C_eq_zero.mp hEta.symm)
  obtain ⟨hFermat, hDerivative⟩ :=
    alignedZero410_reducedFermatSystem A B U hB hTwo
  have hscaledDerivative : (8 : k) • derivative (B ^ 3 * U) = C j := by
    rw [← hDerivative]
    exact hEta
  have hproductDegree : (B ^ 3 * U).natDegree = 1 :=
    natDegree_eq_one_of_scaledDerivative_eq_nonzero_C410
      (B ^ 3 * U) j hj hscaledDerivative
  by_cases hU : U = 0
  · subst U
    simp at hproductDegree
  have hproductDegree' : 3 * B.natDegree + U.natDegree = 1 := by
    rw [natDegree_mul (pow_ne_zero 3 hB) hU, natDegree_pow] at hproductDegree
    exact hproductDegree
  have hBdegree : B.natDegree = 0 := by omega
  obtain ⟨b, hb⟩ := natDegree_eq_zero.mp hBdegree
  have hb0 : b ≠ 0 := by
    intro hbzero
    apply hB
    rw [← hb, hbzero, C_0]
  have hUdegree : U.natDegree = 1 := by omega
  have hU3 : (U ^ 3).natDegree = 3 := by
    rw [natDegree_pow, hUdegree]
  have hB4 : (B ^ 4).natDegree = 0 := by
    rw [← hb]
    simp
  have hleftDegree : (U ^ 3 - B ^ 4).natDegree = 3 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · exact hU3
    · rw [hU3, hB4]
      omega
  have hscaledDegree :
      ((8 : k) • (U ^ 3 - B ^ 4)).natDegree = 3 := by
    simpa only [Polynomial.smul_eq_C_mul,
      natDegree_C_mul (show (8 : k) ≠ 0 by norm_num)] using hleftDegree
  rw [← hFermat, hOne, natDegree_C] at hscaledDegree
  omega

/-- Packaged zero-load contradiction in the original integrated
coordinates.  Thus the branch where the first conserved polynomial is zero
is already excluded by the nonzero Jacobian terminal constant. -/
theorem zeroLoad410_zeroFirstInvariant_trajectory_impossible
    (A B C0 : k[X]) (k1 terminal : k) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 = 0)
    (hOne : firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
        (zeroLoadWPolynomial410 A B C0) (zeroLoadZPolynomial410 A B C0)
        B C0 = C terminal) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hTwoBridge := firstIntegralTwoPolynomial410_zero_discriminant A B C0
  rw [hTwo, smul_zero] at hTwoBridge
  have hTwoAligned : alignedZeroCurveTwoPolynomial410 A B U = 0 := by
    have hs : (5 : k) • alignedZeroCurveTwoPolynomial410 A B U = 0 := by
      simpa only [U] using hTwoBridge.symm
    exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  have hOneBridge := firstIntegralOnePolynomial410_zero_discriminant A B C0
  rw [hOne] at hOneBridge
  have hOneAligned : alignedZeroCurveOnePolynomial410 A B U =
      C ((256 / 5 : k) * k1) := by
    calc
      alignedZeroCurveOnePolynomial410 A B U =
          (1 / 5 : k) • ((5 : k) • alignedZeroCurveOnePolynomial410 A B U) := by
            module
      _ = (1 / 5 : k) • ((256 : k) • C k1) := by
        rw [← hOneBridge]
      _ = C ((256 / 5 : k) * k1) := by
        simp only [smul_smul, Polynomial.smul_C]
        congr 1
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
        ring
  have hterminal' : (256 / 5 : k) * terminal ≠ 0 := by
    exact mul_ne_zero (by norm_num) hterminal
  exact alignedZero410_zeroFirstInvariant_trajectory_impossible
    A B U ((256 / 5 : k) * k1) ((256 / 5 : k) * terminal)
    hterminal' hTwoAligned hOneAligned hEtaAligned

end AlignedZeroTrajectory410

end Max11DegreeRoutes
