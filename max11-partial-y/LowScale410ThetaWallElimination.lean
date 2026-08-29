import LowScale410DeltaWallElimination

/-!
# The final effective loads for the `(4,10)`, scale-zero leaf

We begin at the terminal `theta` wall.  Its terminal one-form is exact
modulo the first invariant, and the three resulting Newton constraints have
the unique nondegenerate degree ray `(8,3,7)`.  The two invariant faces on
that ray are incompatible.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section LaterEffectiveLoads410

variable {k : Type*} [Field k] [CharZero k]

def thetaTerminalPrimitive410 (theta : k) (A B U : k[X]) : k[X] :=
  (3072 * theta : k) • A ^ 2 + (1280 : k) • (B ^ 3 * U) -
    (2048 * theta : k) • U

def thetaFiberPrimitive410
    (theta k2 : k) (A B U : k[X]) : k[X] :=
  thetaTerminalPrimitive410 theta A B U - k2 • A

theorem lWallTerminalNumerator410_theta_eq_derivative_sub
    (theta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 0 0 0 0 0 theta A B U =
      derivative (thetaTerminalPrimitive410 theta A B U) -
        discriminantInvariantTwoNumerator410 0 0 0 0 0 0 theta A B U *
          derivative A := by
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    discriminantInvariantTwoNumerator410, thetaTerminalPrimitive410,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_smul, Polynomial.derivative_C,
    Polynomial.smul_eq_C_mul, zero_mul, mul_zero, zero_smul, add_zero,
    sub_zero, neg_zero, Polynomial.C_0]
  push_cast
  simp only [Polynomial.C_ofNat, Polynomial.C_neg,
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

theorem lWallTerminalNumerator410_theta_eq_fiberDerivative
    (theta k2 : k) (A B U : k[X])
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 0 0 theta A B U = C k2) :
    lWallTerminalNumerator410 0 0 0 0 0 0 theta A B U =
      derivative (thetaFiberPrimitive410 theta k2 A B U) := by
  rw [lWallTerminalNumerator410_theta_eq_derivative_sub, hTwo]
  simp only [thetaFiberPrimitive410, Polynomial.derivative_sub,
    Polynomial.derivative_smul, Polynomial.C_mul']

private def threeDegreeTie410 (d1 d2 d3 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨ (d2 = m ∧ d3 = m)

private theorem threeTerm_degree_tie410
    (P1 P2 P3 : k[X]) (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0)
    (hbelow : (P1 + P2 + P3).natDegree <
      max P1.natDegree (max P2.natDegree P3.natDegree)) :
    threeDegreeTie410 P1.natDegree P2.natDegree P3.natDegree
      (max P1.natDegree (max P2.natDegree P3.natDegree)) := by
  let m := max P1.natDegree (max P2.natDegree P3.natDegree)
  have h1le : P1.natDegree ≤ m := by dsimp [m]; omega
  have h2le : P2.natDegree ≤ m := by dsimp [m]; omega
  have h3le : P3.natDegree ≤ m := by dsimp [m]; omega
  have hcases : P1.natDegree = m ∨ P2.natDegree = m ∨ P3.natDegree = m := by
    dsimp [m]
    omega
  have hcoeff : (P1 + P2 + P3).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [m] using hbelow
  by_contra hnot
  change ¬ threeDegreeTie410 P1.natDegree P2.natDegree P3.natDegree m at hnot
  rcases hcases with h1 | h2 | h3
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTie410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTie410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTie410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTie410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTie410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTie410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree]] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hcoeff)

private def fourDegreeTie410 (d1 d2 d3 d4 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
  (d1 = m ∧ d4 = m) ∨ (d2 = m ∧ d3 = m) ∨
  (d2 = m ∧ d4 = m) ∨ (d3 = m ∧ d4 = m)

private theorem fourTerm_degree_tie410
    (P1 P2 P3 P4 : k[X])
    (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0) (hP4 : P4 ≠ 0)
    (hbelow : (P1 + P2 + P3 + P4).natDegree <
      max P1.natDegree (max P2.natDegree (max P3.natDegree P4.natDegree))) :
    fourDegreeTie410 P1.natDegree P2.natDegree P3.natDegree P4.natDegree
      (max P1.natDegree (max P2.natDegree (max P3.natDegree P4.natDegree))) := by
  let m := max P1.natDegree (max P2.natDegree (max P3.natDegree P4.natDegree))
  have h1le : P1.natDegree ≤ m := by dsimp [m]; omega
  have h2le : P2.natDegree ≤ m := by dsimp [m]; omega
  have h3le : P3.natDegree ≤ m := by dsimp [m]; omega
  have h4le : P4.natDegree ≤ m := by dsimp [m]; omega
  have hcases : P1.natDegree = m ∨ P2.natDegree = m ∨
      P3.natDegree = m ∨ P4.natDegree = m := by
    dsimp [m]
    omega
  have hcoeff : (P1 + P2 + P3 + P4).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [m] using hbelow
  by_contra hnot
  change ¬ fourDegreeTie410 P1.natDegree P2.natDegree P3.natDegree
    P4.natDegree m at hnot
  rcases hcases with h1 | h2 | h3 | h4
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h1, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h2, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h3, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h4lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h4, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h4, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTie410, h4, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      show P4.coeff m = P4.leadingCoeff by rw [← h4, coeff_natDegree]] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP4) (by simpa using hcoeff)

private def thetaLowerTwo410 (theta : k) (A : k[X]) : k[X] :=
  (2048 * theta : k) • A

private def thetaLowerOne410 (theta : k) (B : k[X]) : k[X] :=
  -(320 : k) • B ^ 4 + (2048 * theta : k) • B

private theorem thetaOnly410_nonzero_polynomials_impossible
    (theta k2 k1 terminal : k) (A B U : k[X]) (a b u : ℕ)
    (htheta : theta ≠ 0) (hterminal : terminal ≠ 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b)
    (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 0 0 theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 0 0 theta A B U = C k1)
    (hDegree : (thetaFiberPrimitive410 theta k2 A B U).natDegree = 1) : False := by
  have hpositive : 0 < a ∨ 0 < b ∨ 0 < u := by
    by_contra hnone
    push_neg at hnone
    have hle : (thetaFiberPrimitive410 theta k2 A B U).natDegree ≤ 0 := by
      simp only [thetaFiberPrimitive410, thetaTerminalPrimitive410]
      compute_degree
      omega
    omega
  have hsmul {c : k} {P : k[X]} (hc : c ≠ 0) (hP : P ≠ 0) : c • P ≠ 0 := by
    intro hz
    exact hP ((smul_eq_zero.mp hz).resolve_left hc)
  have hcTheta : (2048 * theta : k) ≠ 0 := mul_ne_zero (by norm_num) htheta
  have hsumTwo : (-(1280 : k)) • (A * B ^ 3) +
      (480 : k) • (B * U ^ 2) + (2048 * theta : k) • A = C k2 := by
    have hs := hTwo
    simp only [discriminantInvariantTwoNumerator410, zero_mul, mul_zero,
      zero_smul, add_zero, zero_add, sub_zero, neg_zero, sub_eq_add_neg,
      neg_smul] at hs
    calc
      (-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
          (2048 * theta : k) • A =
        -((1280 : k) • (A * B ^ 3)) + (2048 * theta : k) • A +
          (480 : k) • (B * U ^ 2) := by module
      _ = C k2 := hs
  have hmTwoPos : 0 < max (a + 3 * b) (max (b + 2 * u) a) := by omega
  have hbelowTwo :
      ((-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
        (2048 * theta : k) • A).natDegree <
          max (a + 3 * b) (max (b + 2 * u) a) := by
    rw [hsumTwo, natDegree_C]
    exact hmTwoPos
  have hTieTwo := threeTerm_degree_tie410
    ((-(1280 : k)) • (A * B ^ 3)) ((480 : k) • (B * U ^ 2))
    ((2048 * theta : k) • A)
    (hsmul (by norm_num) (mul_ne_zero hAne (pow_ne_zero 3 hBne)))
    (hsmul (by norm_num) (mul_ne_zero hBne (pow_ne_zero 2 hUne)))
    (hsmul hcTheta hAne)
    (by
      simpa only [natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
        natDegree_smul _ (by norm_num : (480 : k) ≠ 0),
        natDegree_smul _ hcTheta, natDegree_mul hAne (pow_ne_zero 3 hBne),
        natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hA, hB, hU]
        using hbelowTwo)
  have hsumOne : (960 : k) • (A * B ^ 2 * U) +
      (-(320 : k)) • B ^ 4 + (-(40 : k)) • U ^ 3 +
        (2048 * theta : k) • B = C k1 := by
    have hs := hOne
    simp only [discriminantInvariantOneNumerator410, zero_mul, mul_zero,
      zero_smul, add_zero, zero_add, sub_zero, neg_zero, sub_eq_add_neg,
      neg_smul] at hs
    calc
      (960 : k) • (A * B ^ 2 * U) + (-(320 : k)) • B ^ 4 +
          (-(40 : k)) • U ^ 3 + (2048 * theta : k) • B =
        (960 : k) • (A * B ^ 2 * U) - (320 : k) • B ^ 4 +
          (2048 * theta : k) • B - (40 : k) • U ^ 3 := by module
      _ = C k1 := hs
  have hmOnePos : 0 < max (a + 2 * b + u)
      (max (4 * b) (max (3 * u) b)) := by omega
  have hbelowOne :
      ((960 : k) • (A * B ^ 2 * U) + (-(320 : k)) • B ^ 4 +
        (-(40 : k)) • U ^ 3 + (2048 * theta : k) • B).natDegree <
          max (a + 2 * b + u) (max (4 * b) (max (3 * u) b)) := by
    rw [hsumOne, natDegree_C]
    exact hmOnePos
  have hTieOne := fourTerm_degree_tie410
    ((960 : k) • (A * B ^ 2 * U)) ((-(320 : k)) • B ^ 4)
    ((-(40 : k)) • U ^ 3) ((2048 * theta : k) • B)
    (hsmul (by norm_num)
      (mul_ne_zero (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne))
    (hsmul (by norm_num) (pow_ne_zero 4 hBne))
    (hsmul (by norm_num) (pow_ne_zero 3 hUne))
    (hsmul hcTheta hBne)
    (by
      simpa only [natDegree_smul _ (by norm_num : (960 : k) ≠ 0),
        natDegree_smul _ (by norm_num : (-(320 : k)) ≠ 0),
        natDegree_smul _ (by norm_num : (-(40 : k)) ≠ 0),
        natDegree_smul _ hcTheta,
        natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
        natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, hA, hB, hU]
        using hbelowOne)
  simp only [threeDegreeTie410,
    natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (480 : k) ≠ 0), natDegree_smul _ hcTheta,
    natDegree_mul hAne (pow_ne_zero 3 hBne),
    natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hA, hB, hU]
    at hTieTwo
  simp only [fourDegreeTie410,
    natDegree_smul _ (by norm_num : (960 : k) ≠ 0),
    natDegree_smul _ (by norm_num : (-(320 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (-(40 : k)) ≠ 0),
    natDegree_smul _ hcTheta,
    natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
    natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, hA, hB, hU]
    at hTieOne
  have hPrimitiveForm : thetaTerminalPrimitive410 theta A B U =
      thetaFiberPrimitive410 theta k2 A B U + k2 • A := by
    simp only [thetaFiberPrimitive410]
    abel
  have hPrimitiveLe :
      (thetaTerminalPrimitive410 theta A B U).natDegree ≤ max 1 a := by
    rw [hPrimitiveForm]
    compute_degree
    omega
  have hmPrimitivePos : max 1 a < max (2 * a) (max (3 * b + u) u) := by
    omega
  have hbelowPrimitive :
      ((3072 * theta : k) • A ^ 2 + (1280 : k) • (B ^ 3 * U) +
        (-(2048 * theta) : k) • U).natDegree <
          max (2 * a) (max (3 * b + u) u) := by
    have hform :
        (3072 * theta : k) • A ^ 2 + (1280 : k) • (B ^ 3 * U) +
            (-(2048 * theta) : k) • U = thetaTerminalPrimitive410 theta A B U := by
      simp only [thetaTerminalPrimitive410, sub_eq_add_neg, neg_smul]
    rw [hform]
    exact hPrimitiveLe.trans_lt hmPrimitivePos
  have hc3072 : (3072 * theta : k) ≠ 0 := mul_ne_zero (by norm_num) htheta
  have hTiePrimitive := threeTerm_degree_tie410
    ((3072 * theta : k) • A ^ 2) ((1280 : k) • (B ^ 3 * U))
    ((-(2048 * theta) : k) • U)
    (hsmul hc3072 (pow_ne_zero 2 hAne))
    (hsmul (by norm_num) (mul_ne_zero (pow_ne_zero 3 hBne) hUne))
    (hsmul (neg_ne_zero.mpr hcTheta) hUne)
    (by
      simpa only [natDegree_smul _ hc3072,
        natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
        natDegree_smul _ (neg_ne_zero.mpr hcTheta), natDegree_pow,
        natDegree_mul (pow_ne_zero 3 hBne) hUne, hA, hB, hU]
        using hbelowPrimitive)
  simp only [threeDegreeTie410, natDegree_smul _ hc3072,
    natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
    natDegree_smul _ (neg_ne_zero.mpr hcTheta), natDegree_pow,
    natDegree_mul (pow_ne_zero 3 hBne) hUne, hA, hB, hU] at hTiePrimitive
  have hplane : a + 2 * b = 2 * u := by omega
  have hab : 3 * a = 8 * b := by omega
  have hau : 7 * a = 8 * u := by omega
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  have hu : 0 < u := by omega
  have hLowerTwo : (thetaLowerTwo410 theta A).natDegree < a + 3 * b := by
    simp only [thetaLowerTwo410]
    compute_degree
    omega
  have hLowerOne : (thetaLowerOne410 theta B).natDegree < 3 * u := by
    simp only [thetaLowerOne410]
    compute_degree
    omega
  have hTwoFace : discriminantInvariantTwoNumerator410
      0 0 0 0 0 0 theta A B U =
        (-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
          thetaLowerTwo410 theta A := by
    simp only [discriminantInvariantTwoNumerator410, thetaLowerTwo410,
      zero_mul, mul_zero, zero_smul, add_zero, sub_zero, sub_eq_add_neg,
      neg_smul]
    module
  have hOneFace : discriminantInvariantOneNumerator410
      0 0 0 0 0 0 theta A B U =
        (960 : k) • (A * B ^ 2 * U) + (-(40 : k)) • U ^ 3 +
          thetaLowerOne410 theta B := by
    simp only [discriminantInvariantOneNumerator410, thetaLowerOne410,
      zero_mul, mul_zero, zero_smul, add_zero, sub_zero, sub_eq_add_neg,
      neg_smul]
    module
  have hAB3deg : (A * B ^ 3).natDegree = a + 3 * b := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow, hA, hB]
  have hBU2deg : (B * U ^ 2).natDegree = a + 3 * b := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hB, hU]
    omega
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 3 * u := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, hA, hB, hU]
    omega
  have hU3deg : (U ^ 3).natDegree = 3 * u := by rw [natDegree_pow, hU]
  have hTwoCoeff := congrArg (fun P : k[X] => P.coeff (a + 3 * b)) hTwo
  rw [hTwoFace, coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A * B ^ 3).coeff (a + 3 * b) =
        A.leadingCoeff * B.leadingCoeff ^ 3 by
      rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    show (B * U ^ 2).coeff (a + 3 * b) =
        B.leadingCoeff * U.leadingCoeff ^ 2 by
      rw [← hBU2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hLowerTwo, add_zero,
    show (C k2 : k[X]).coeff (a + 3 * b) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hTwoCoeff
  simp only [smul_eq_mul] at hTwoCoeff
  have hOneCoeff := congrArg (fun P : k[X] => P.coeff (3 * u)) hOne
  rw [hOneFace, coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A * B ^ 2 * U).coeff (3 * u) =
        A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff by
      rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow],
    show (U ^ 3).coeff (3 * u) = U.leadingCoeff ^ 3 by
      rw [← hU3deg, coeff_natDegree, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hLowerOne, add_zero,
    show (C k1 : k[X]).coeff (3 * u) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hOneCoeff
  simp only [smul_eq_mul] at hOneCoeff
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBle : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hUle : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hUne
  have hFaceTwo :
      -(1280 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) +
        480 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hBle)
    linear_combination hTwoCoeff
  have hFaceOne :
      960 * (A.leadingCoeff * B.leadingCoeff ^ 2) -
        40 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hUle)
    linear_combination hOneCoeff
  have hzero : (10240 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) = 0 := by
    linear_combination hFaceTwo + 12 * hFaceOne
  exact (mul_ne_zero (by norm_num)
    (mul_ne_zero hAle (pow_ne_zero 2 hBle))) hzero

private theorem thetaFiber_degree_one_impossible_of_degrees_zero
    (theta k2 : k) (A B U : k[X])
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hU : U.natDegree = 0)
    (hDegree : (thetaFiberPrimitive410 theta k2 A B U).natDegree = 1) : False := by
  have hle : (thetaFiberPrimitive410 theta k2 A B U).natDegree ≤ 0 := by
    simp only [thetaFiberPrimitive410, thetaTerminalPrimitive410]
    compute_degree
    omega
  omega

private theorem thetaOnly410_zeroA_impossible
    (theta k2 k1 : k) (A B U : k[X]) (hAzero : A = 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 0 0 theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 0 0 theta A B U = C k1)
    (hDegree : (thetaFiberPrimitive410 theta k2 A B U).natDegree = 1) : False := by
  subst A
  by_cases hBzero : B = 0
  · subst B
    have hUeq : (-(40 : k)) • U ^ 3 = C k1 := by
      simpa [discriminantInvariantOneNumerator410] using hOne
    have hd := congrArg Polynomial.natDegree hUeq
    rw [natDegree_smul _ (by norm_num), natDegree_pow, natDegree_C] at hd
    exact thetaFiber_degree_one_impossible_of_degrees_zero
      theta k2 0 0 U (by simp) (by simp) (by omega) hDegree
  · by_cases hUzero : U = 0
    · subst U
      simp [thetaFiberPrimitive410, thetaTerminalPrimitive410] at hDegree
    · have hProduct : (480 : k) • (B * U ^ 2) = C k2 := by
        simpa [discriminantInvariantTwoNumerator410] using hTwo
      have hd := congrArg Polynomial.natDegree hProduct
      rw [natDegree_smul _ (by norm_num),
        natDegree_mul hBzero (pow_ne_zero 2 hUzero), natDegree_pow,
        natDegree_C] at hd
      exact thetaFiber_degree_one_impossible_of_degrees_zero
        theta k2 0 B U (by simp) (by omega) (by omega) hDegree

private theorem thetaOnly410_zeroB_impossible
    (theta k2 k1 : k) (A B U : k[X]) (htheta : theta ≠ 0) (hBzero : B = 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 0 0 theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 0 0 theta A B U = C k1)
    (hDegree : (thetaFiberPrimitive410 theta k2 A B U).natDegree = 1) : False := by
  subst B
  have hcTheta : (2048 * theta : k) ≠ 0 := mul_ne_zero (by norm_num) htheta
  have hAeq : (2048 * theta : k) • A = C k2 := by
    simpa [discriminantInvariantTwoNumerator410] using hTwo
  have hUeq : (-(40 : k)) • U ^ 3 = C k1 := by
    simpa [discriminantInvariantOneNumerator410] using hOne
  have hdA := congrArg Polynomial.natDegree hAeq
  have hdU := congrArg Polynomial.natDegree hUeq
  rw [natDegree_smul _ hcTheta, natDegree_C] at hdA
  rw [natDegree_smul _ (by norm_num), natDegree_pow, natDegree_C] at hdU
  exact thetaFiber_degree_one_impossible_of_degrees_zero
    theta k2 A 0 U (by omega) (by simp) (by omega) hDegree

private theorem thetaOnly410_zeroU_impossible
    (theta k2 k1 : k) (A B U : k[X]) (htheta : theta ≠ 0) (hUzero : U = 0)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 0 0 theta A B U = C k1)
    (hDegree : (thetaFiberPrimitive410 theta k2 A B U).natDegree = 1) : False := by
  subst U
  have hBdegree : B.natDegree = 0 := by
    by_contra hb0
    have hbpos : 0 < B.natDegree := by omega
    have hBne : B ≠ 0 := by
      intro hz
      subst B
      exact hb0 natDegree_zero
    let R : k[X] := (2048 * theta : k) • B
    have hOneForm : (-(320 : k)) • B ^ 4 + R = C k1 := by
      have hs := hOne
      simp [discriminantInvariantOneNumerator410] at hs
      calc
        (-(320 : k)) • B ^ 4 + R =
            -((320 : k) • B ^ 4) + (2048 * theta : k) • B := by
              dsimp only [R]
              rw [neg_smul]
        _ = C k1 := hs
    have hRdegree : R.natDegree < 4 * B.natDegree := by
      dsimp only [R]
      compute_degree
      omega
    exact smul_add_lower_ne_C410 (-(320 : k)) k1 (B ^ 4) R
      (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hBne) (by omega)
      (by rw [natDegree_pow]) hRdegree hOneForm
  by_cases hAdegree : A.natDegree = 0
  · exact thetaFiber_degree_one_impossible_of_degrees_zero
      theta k2 A B 0 hAdegree hBdegree (by simp) hDegree
  · have hApos : 0 < A.natDegree := by omega
    have hAne : A ≠ 0 := by
      intro hz
      subst A
      exact hAdegree natDegree_zero
    have hcTheta : (3072 * theta : k) ≠ 0 := mul_ne_zero (by norm_num) htheta
    have hForm : thetaFiberPrimitive410 theta k2 A B 0 =
        (3072 * theta : k) • A ^ 2 - k2 • A := by
      simp [thetaFiberPrimitive410, thetaTerminalPrimitive410]
    have hFirstDegree : ((3072 * theta : k) • A ^ 2).natDegree =
        2 * A.natDegree := by
      rw [natDegree_smul _ hcTheta, natDegree_pow]
    have hSecondDegree : (k2 • A).natDegree < 2 * A.natDegree := by
      compute_degree
      omega
    have hFiberDegree : (thetaFiberPrimitive410 theta k2 A B 0).natDegree =
        2 * A.natDegree := by
      rw [hForm, natDegree_sub_eq_left_of_natDegree_lt]
      · exact hFirstDegree
      · rw [hFirstDegree]
        exact hSecondDegree
    omega

/-- The pure terminal `theta` wall is impossible in discriminant
coordinates. -/
theorem thetaOnly410_discriminant_trajectory_impossible
    (theta k2 k1 terminal : k) (A B U : k[X])
    (htheta : theta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 0 0 theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 0 0 theta A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 0 0 0 theta A B U = C terminal) : False := by
  have hDerivative : derivative (thetaFiberPrimitive410 theta k2 A B U) =
      C terminal := by
    rw [← lWallTerminalNumerator410_theta_eq_fiberDerivative
      theta k2 A B U hTwo]
    exact hTerminal
  have hDegree : (thetaFiberPrimitive410 theta k2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (thetaFiberPrimitive410 theta k2 A B U) terminal hterminal hDerivative
  by_cases hAzero : A = 0
  · exact thetaOnly410_zeroA_impossible theta k2 k1 A B U hAzero
      hTwo hOne hDegree
  · by_cases hBzero : B = 0
    · exact thetaOnly410_zeroB_impossible theta k2 k1 A B U htheta hBzero
        hTwo hOne hDegree
    · by_cases hUzero : U = 0
      · exact thetaOnly410_zeroU_impossible theta k2 k1 A B U htheta hUzero
          hOne hDegree
      · exact thetaOnly410_nonzero_polynomials_impossible theta k2 k1 terminal
          A B U A.natDegree B.natDegree U.natDegree htheta hterminal
          hAzero hBzero hUzero rfl rfl rfl hTwo hOne hDegree

/-- Original-coordinate closure of the pure `theta` wall. -/
theorem thetaOnly410_original_trajectory_impossible
    (alpha epsilon theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (htheta : theta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 0 0 theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 0 0 theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon 0 theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon 0 0 iota A B C0)
      B C0 = C terminal) : False := by
  have hTwoD : discriminantInvariantTwoNumerator410 0 0 0 0 0 0 theta A B
      (A ^ 2 - (4 : k) • C0) = C (2048 * k2) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD : discriminantInvariantOneNumerator410 0 0 0 0 0 0 theta A B
      (A ^ 2 - (4 : k) • C0) = C (2048 * k1) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410 0 0 0 0 0 0 theta A B
      (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact thetaOnly410_discriminant_trajectory_impossible theta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) htheta (mul_ne_zero (by norm_num) hterminal)
      hTwoD hOneD hTerminalD

/-- Closing the terminal wall shrinks the final effective-load residual to
`zeta` or `eta`. -/
theorem thetaWall410_earlierEffectiveLoad_residual
    (alpha epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
      B C0 = C terminal) : zeta ≠ 0 ∨ eta ≠ 0 := by
  by_contra hearlier
  push_neg at hearlier
  obtain ⟨hzeta, heta⟩ := hearlier
  subst zeta
  subst eta
  have hresidual := deltaWall410_laterEffectiveLoad_residual
    (k := k) alpha 0 epsilon 0 0 theta iota k2 k1 terminal A B C0
      hterminal hTwo hOne hLower
  rcases hresidual with hzeta | heta | htheta
  · exact hzeta rfl
  · exact heta rfl
  · exact thetaOnly410_original_trajectory_impossible alpha epsilon theta iota
      k2 k1 terminal A B C0 htheta hterminal hTwo hOne hLower

end LaterEffectiveLoads410

end Max11DegreeRoutes
