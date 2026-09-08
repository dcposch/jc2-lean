import LowScale410ZetaEtaWalls

/-!
# Mixed effective-load walls for (4,10), scale zero

The zeta Newton polygon is stable under arbitrary eta and theta loads away
from the three discriminant coordinate faces. This isolates the eta-theta
cone and the coordinate-degenerate faces as the exact first mixed packet.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section MixedEffectiveWalls410

variable {k : Type*} [Field k] [CharZero k]

def mixedEffectiveTerminalPrimitive410
    (zeta theta : k) (A B U : k[X]) : k[X] :=
  (1280 * zeta : k) • A ^ 3 - (1536 * zeta : k) • (A * U) +
    (3072 * theta : k) • A ^ 2 + (1280 : k) • (B ^ 3 * U) -
    (3072 * zeta : k) • B ^ 2 - (2048 * theta : k) • U

def mixedEffectiveFiberPrimitive410
    (zeta theta k2 : k) (A B U : k[X]) : k[X] :=
  mixedEffectiveTerminalPrimitive410 zeta theta A B U - k2 • A

def mixedEffectiveLowerTwo410
    (zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (768 * zeta : k) • A ^ 2 - (1536 * zeta : k) • U +
    (4096 * eta : k) • B + (2048 * theta : k) • A

def mixedEffectiveLowerOne410
    (zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(320 : k) • B ^ 4 - (1536 * zeta : k) • (A * B) -
    (1024 * eta : k) • U + (2048 * theta : k) • B

theorem lWallTerminalNumerator410_mixedEffective_eq_derivative_sub
    (zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 0 0 0 zeta eta theta A B U =
      derivative (mixedEffectiveTerminalPrimitive410 zeta theta A B U) -
        discriminantInvariantTwoNumerator410 0 0 0 0 zeta eta theta A B U *
          derivative A := by
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    discriminantInvariantTwoNumerator410, mixedEffectiveTerminalPrimitive410,
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
  have h3 : (3 : k[X]) = (3 : k) • (1 : k[X]) := by
    rw [← hC]
    exact (Polynomial.C_ofNat 3).symm
  simp only [hC, pow_two, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, _root_.smul_pow, one_pow]
  rw [h2, h3]
  simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

theorem lWallTerminalNumerator410_mixedEffective_eq_fiberDerivative
    (zeta eta theta k2 : k) (A B U : k[X])
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta eta theta A B U = C k2) :
    lWallTerminalNumerator410 0 0 0 0 zeta eta theta A B U =
      derivative (mixedEffectiveFiberPrimitive410 zeta theta k2 A B U) := by
  rw [lWallTerminalNumerator410_mixedEffective_eq_derivative_sub, hTwo]
  simp only [mixedEffectiveFiberPrimitive410, Polynomial.derivative_sub,
    Polynomial.derivative_smul, Polynomial.C_mul']
private def fourDegreeTieMixed410 (d1 d2 d3 d4 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
  (d1 = m ∧ d4 = m) ∨ (d2 = m ∧ d3 = m) ∨
  (d2 = m ∧ d4 = m) ∨ (d3 = m ∧ d4 = m)

private theorem fourTerm_degree_tie_mixed410
    (P1 P2 P3 P4 : k[X])
    (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0) (hP4 : P4 ≠ 0)
    (hbelow : (P1 + P2 + P3 + P4).natDegree <
      max P1.natDegree (max P2.natDegree (max P3.natDegree P4.natDegree))) :
    fourDegreeTieMixed410 P1.natDegree P2.natDegree P3.natDegree P4.natDegree
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
  change ¬ fourDegreeTieMixed410 P1.natDegree P2.natDegree P3.natDegree
    P4.natDegree m at hnot
  rcases hcases with h1 | h2 | h3 | h4
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h1, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h1, heq])
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
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h2, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h3, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h4lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h4, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h4, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieMixed410, h4, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      show P4.coeff m = P4.leadingCoeff by rw [← h4, coeff_natDegree]] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP4) (by simpa using hcoeff)


private theorem zetaMixed410_nonzero_polynomials_impossible
    (zeta eta theta k2 k1 terminal : k) (A B U : k[X]) (a b u : ℕ)
    (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b)
    (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta eta theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 zeta eta theta A B U = C k1)
    (hDegree : (mixedEffectiveFiberPrimitive410 zeta theta k2 A B U).natDegree = 1) : False := by
  have hpositive : 0 < a ∨ 0 < b ∨ 0 < u := by
    by_contra hnone
    push_neg at hnone
    have hle : (mixedEffectiveFiberPrimitive410 zeta theta k2 A B U).natDegree ≤ 0 := by
      simp only [mixedEffectiveFiberPrimitive410, mixedEffectiveTerminalPrimitive410]
      compute_degree
      omega
    omega
  have hsmul {c : k} {P : k[X]} (hc : c ≠ 0) (hP : P ≠ 0) : c • P ≠ 0 := by
    intro hzero
    exact hP ((smul_eq_zero.mp hzero).resolve_left hc)
  have hc768 : (768 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
  have hc1536 : (1536 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
  have hc1280 : (1280 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
  have hc3072 : (3072 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hzeta
  have hsumTwo : (-(1280 : k)) • (A * B ^ 3) +
      (480 : k) • (B * U ^ 2) + (768 * zeta : k) • A ^ 2 +
        (-(1536 * zeta) : k) • U =
      C k2 - ((4096 * eta : k) • B + (2048 * theta : k) • A) := by
    have hs := hTwo
    simp only [discriminantInvariantTwoNumerator410, zero_mul, mul_zero,
      zero_smul, add_zero, zero_add, sub_zero, neg_zero, sub_eq_add_neg,
      neg_smul] at hs
    rw [neg_smul, neg_smul]
    rw [← hs]
    abel
  have hmTwoPos : 0 < max (a + 3 * b)
      (max (b + 2 * u) (max (2 * a) u)) := by omega
  have hbelowTwo :
      ((-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
        (768 * zeta : k) • A ^ 2 + (-(1536 * zeta) : k) • U).natDegree <
          max (a + 3 * b) (max (b + 2 * u) (max (2 * a) u)) := by
    rw [hsumTwo]
    compute_degree
    omega
  have hTieTwo := fourTerm_degree_tie_mixed410
    ((-(1280 : k)) • (A * B ^ 3)) ((480 : k) • (B * U ^ 2))
    ((768 * zeta : k) • A ^ 2) ((-(1536 * zeta) : k) • U)
    (hsmul (by norm_num) (mul_ne_zero hAne (pow_ne_zero 3 hBne)))
    (hsmul (by norm_num) (mul_ne_zero hBne (pow_ne_zero 2 hUne)))
    (hsmul hc768 (pow_ne_zero 2 hAne))
    (hsmul (neg_ne_zero.mpr hc1536) hUne)
    (by
      simpa only [natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
        natDegree_smul _ (by norm_num : (480 : k) ≠ 0),
        natDegree_smul _ hc768, natDegree_smul _ (neg_ne_zero.mpr hc1536),
        natDegree_mul hAne (pow_ne_zero 3 hBne),
        natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hA, hB, hU]
        using hbelowTwo)
  have hsumOne : (960 : k) • (A * B ^ 2 * U) +
      (-(320 : k)) • B ^ 4 + (-(40 : k)) • U ^ 3 +
        (-(1536 * zeta) : k) • (A * B) =
      C k1 - ((-(1024 * eta) : k) • U + (2048 * theta : k) • B) := by
    have hs := hOne
    simp only [discriminantInvariantOneNumerator410, zero_mul, mul_zero,
      zero_smul, add_zero, zero_add, sub_zero, neg_zero, sub_eq_add_neg,
      neg_smul] at hs
    rw [neg_smul, neg_smul, neg_smul, neg_smul]
    rw [← hs]
    abel
  have hmOnePos : 0 < max (a + 2 * b + u)
      (max (4 * b) (max (3 * u) (a + b))) := by omega
  have hbelowOne :
      ((960 : k) • (A * B ^ 2 * U) + (-(320 : k)) • B ^ 4 +
        (-(40 : k)) • U ^ 3 + (-(1536 * zeta) : k) • (A * B)).natDegree <
          max (a + 2 * b + u) (max (4 * b) (max (3 * u) (a + b))) := by
    rw [hsumOne]
    compute_degree
    omega
  have hTieOne := fourTerm_degree_tie_mixed410
    ((960 : k) • (A * B ^ 2 * U)) ((-(320 : k)) • B ^ 4)
    ((-(40 : k)) • U ^ 3) ((-(1536 * zeta) : k) • (A * B))
    (hsmul (by norm_num)
      (mul_ne_zero (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne))
    (hsmul (by norm_num) (pow_ne_zero 4 hBne))
    (hsmul (by norm_num) (pow_ne_zero 3 hUne))
    (hsmul (neg_ne_zero.mpr hc1536) (mul_ne_zero hAne hBne))
    (by
      simpa only [natDegree_smul _ (by norm_num : (960 : k) ≠ 0),
        natDegree_smul _ (by norm_num : (-(320 : k)) ≠ 0),
        natDegree_smul _ (by norm_num : (-(40 : k)) ≠ 0),
        natDegree_smul _ (neg_ne_zero.mpr hc1536),
        natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
        natDegree_mul hAne (pow_ne_zero 2 hBne),
        natDegree_mul hAne hBne, natDegree_pow, hA, hB, hU]
        using hbelowOne)
  simp only [fourDegreeTieMixed410,
    natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (480 : k) ≠ 0),
    natDegree_smul _ hc768, natDegree_smul _ (neg_ne_zero.mpr hc1536),
    natDegree_mul hAne (pow_ne_zero 3 hBne),
    natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hA, hB, hU]
    at hTieTwo
  simp only [fourDegreeTieMixed410,
    natDegree_smul _ (by norm_num : (960 : k) ≠ 0),
    natDegree_smul _ (by norm_num : (-(320 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (-(40 : k)) ≠ 0),
    natDegree_smul _ (neg_ne_zero.mpr hc1536),
    natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
    natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_mul hAne hBne,
    natDegree_pow, hA, hB, hU] at hTieOne
  have hPrimitiveForm : mixedEffectiveTerminalPrimitive410 zeta theta A B U =
      mixedEffectiveFiberPrimitive410 zeta theta k2 A B U + k2 • A := by
    simp only [mixedEffectiveFiberPrimitive410]
    abel
  have hPrimitiveLe : (mixedEffectiveTerminalPrimitive410 zeta theta A B U).natDegree ≤
      max 1 a := by
    rw [hPrimitiveForm]
    compute_degree
    omega
  have hmPrimitivePos : max 1 a < max (3 * a)
      (max (a + u) (max (3 * b + u) (2 * b))) := by omega
  have hbelowPrimitive :
      ((1280 * zeta : k) • A ^ 3 + (-(1536 * zeta) : k) • (A * U) +
        (1280 : k) • (B ^ 3 * U) + (-(3072 * zeta) : k) • B ^ 2).natDegree <
          max (3 * a) (max (a + u) (max (3 * b + u) (2 * b))) := by
    have hform :
        (1280 * zeta : k) • A ^ 3 + (-(1536 * zeta) : k) • (A * U) +
            (1280 : k) • (B ^ 3 * U) + (-(3072 * zeta) : k) • B ^ 2 =
          mixedEffectiveTerminalPrimitive410 zeta theta A B U -
            ((3072 * theta : k) • A ^ 2 - (2048 * theta : k) • U) := by
      simp only [mixedEffectiveTerminalPrimitive410, sub_eq_add_neg, neg_smul]
      module
    have hThetaLower : ((3072 * theta : k) • A ^ 2 -
        (2048 * theta : k) • U).natDegree <
          max (3 * a) (max (a + u) (max (3 * b + u) (2 * b))) := by
      compute_degree
      omega
    rw [hform]
    compute_degree
    omega
  have hTiePrimitive := fourTerm_degree_tie_mixed410
    ((1280 * zeta : k) • A ^ 3) ((-(1536 * zeta) : k) • (A * U))
    ((1280 : k) • (B ^ 3 * U)) ((-(3072 * zeta) : k) • B ^ 2)
    (hsmul hc1280 (pow_ne_zero 3 hAne))
    (hsmul (neg_ne_zero.mpr hc1536) (mul_ne_zero hAne hUne))
    (hsmul (by norm_num) (mul_ne_zero (pow_ne_zero 3 hBne) hUne))
    (hsmul (neg_ne_zero.mpr hc3072) (pow_ne_zero 2 hBne))
    (by
      simpa only [natDegree_smul _ hc1280,
        natDegree_smul _ (neg_ne_zero.mpr hc1536),
        natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
        natDegree_smul _ (neg_ne_zero.mpr hc3072),
        natDegree_mul hAne hUne, natDegree_mul (pow_ne_zero 3 hBne) hUne,
        natDegree_pow, hA, hB, hU] using hbelowPrimitive)
  simp only [fourDegreeTieMixed410, natDegree_smul _ hc1280,
    natDegree_smul _ (neg_ne_zero.mpr hc1536),
    natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
    natDegree_smul _ (neg_ne_zero.mpr hc3072),
    natDegree_mul hAne hUne, natDegree_mul (pow_ne_zero 3 hBne) hUne,
    natDegree_pow, hA, hB, hU] at hTiePrimitive
  have hplane : a + 2 * b = 2 * u := by omega
  have hab : 5 * a = 8 * b := by omega
  have hau : 9 * a = 8 * u := by omega
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  have hu : 0 < u := by omega
  have hLowerTwo : (mixedEffectiveLowerTwo410 zeta eta theta A B U).natDegree <
      a + 3 * b := by
    simp only [mixedEffectiveLowerTwo410]
    compute_degree
    omega
  have hLowerOne : (mixedEffectiveLowerOne410 zeta eta theta A B U).natDegree <
      3 * u := by
    simp only [mixedEffectiveLowerOne410]
    compute_degree
    omega
  have hTwoFace : discriminantInvariantTwoNumerator410 0 0 0 0 zeta eta theta
      A B U = (-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
        mixedEffectiveLowerTwo410 zeta eta theta A B U := by
    simp only [discriminantInvariantTwoNumerator410, mixedEffectiveLowerTwo410,
      zero_mul, mul_zero, zero_smul, add_zero, sub_zero, sub_eq_add_neg,
      neg_smul]
    module
  have hOneFace : discriminantInvariantOneNumerator410 0 0 0 0 zeta eta theta
      A B U = (960 : k) • (A * B ^ 2 * U) + (-(40 : k)) • U ^ 3 +
        mixedEffectiveLowerOne410 zeta eta theta A B U := by
    simp only [discriminantInvariantOneNumerator410, mixedEffectiveLowerOne410,
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
  have hFaceTwo : -(1280 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) +
      480 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hBle)
    linear_combination hTwoCoeff
  have hFaceOne : 960 * (A.leadingCoeff * B.leadingCoeff ^ 2) -
      40 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hUle)
    linear_combination hOneCoeff
  have hzero : (10240 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) = 0 := by
    linear_combination hFaceTwo + 12 * hFaceOne
  exact (mul_ne_zero (by norm_num)
    (mul_ne_zero hAle (pow_ne_zero 2 hBle))) hzero

/-- With `zeta ≠ 0`, a mixed effective-load trajectory can survive only on
one of the three discriminant coordinate faces. -/
theorem zetaMixed410_discriminant_coordinate_selector
    (zeta eta theta k2 k1 terminal : k) (A B U : k[X])
    (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta eta theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 zeta eta theta A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 0 zeta eta theta A B U = C terminal) :
    A = 0 ∨ B = 0 ∨ U = 0 := by
  have hDerivative : derivative
      (mixedEffectiveFiberPrimitive410 zeta theta k2 A B U) = C terminal := by
    rw [← lWallTerminalNumerator410_mixedEffective_eq_fiberDerivative
      zeta eta theta k2 A B U hTwo]
    exact hTerminal
  have hDegree :
      (mixedEffectiveFiberPrimitive410 zeta theta k2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (mixedEffectiveFiberPrimitive410 zeta theta k2 A B U)
      terminal hterminal hDerivative
  by_cases hAzero : A = 0
  · exact Or.inl hAzero
  · by_cases hBzero : B = 0
    · exact Or.inr (Or.inl hBzero)
    · by_cases hUzero : U = 0
      · exact Or.inr (Or.inr hUzero)
      · exact (zetaMixed410_nonzero_polynomials_impossible
          zeta eta theta k2 k1 terminal A B U
          A.natDegree B.natDegree U.natDegree hzeta hterminal
          hAzero hBzero hUzero rfl rfl rfl hTwo hOne hDegree).elim

theorem zetaMixed410_original_coordinate_selector
    (alpha epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
      B C0 = C terminal) :
    A = 0 ∨ B = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 := by
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta eta theta A B (A ^ 2 - (4 : k) • C0) =
        C (2048 * k2) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD : discriminantInvariantOneNumerator410
      0 0 0 0 zeta eta theta A B (A ^ 2 - (4 : k) • C0) =
        C (2048 * k1) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410
      0 0 0 0 zeta eta theta A B (A ^ 2 - (4 : k) • C0) =
        C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact zetaMixed410_discriminant_coordinate_selector zeta eta theta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) hzeta
      (mul_ne_zero (by norm_num) hterminal) hTwoD hOneD hTerminalD

/-- Exact first mixed packet: outside the three coordinate faces, the only
remaining effective-load cone is the pure pair `eta ≠ 0`, `theta ≠ 0` with
`zeta = 0`. -/
theorem mixedEffective410_finite_residual_packet
    (alpha epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
      B C0 = C terminal) :
    (zeta = 0 ∧ eta ≠ 0 ∧ theta ≠ 0) ∨
      A = 0 ∨ B = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 := by
  have hpair := zetaEtaTheta410_pairwise_nonzero_residual
    (k := k) alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
      hterminal hTwo hOne hLower
  by_cases hzeta : zeta = 0
  · left
    refine ⟨hzeta, ?_⟩
    rcases hpair with hze | hzt | het
    · exact (hze.1 hzeta).elim
    · exact (hzt.1 hzeta).elim
    · exact het
  · right
    exact zetaMixed410_original_coordinate_selector alpha epsilon zeta eta
      theta iota k2 k1 terminal A B C0 hzeta hterminal hTwo hOne hLower


end MixedEffectiveWalls410

end Max11DegreeRoutes
