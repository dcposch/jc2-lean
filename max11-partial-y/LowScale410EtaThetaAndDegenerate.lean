import LowScale410MixedEffectiveWalls

/-!
# The eta-theta cone and coordinate faces for (4,10), scale zero

The theta Newton polygon is stable under the eta perturbation away from
the discriminant coordinate faces. We then reduce those faces directly.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section EtaThetaAndDegenerate410

variable {k : Type*} [Field k] [CharZero k]

def etaThetaLowerTwo410 (eta theta : k) (A B : k[X]) : k[X] :=
  (2048 * theta : k) • A + (4096 * eta : k) • B

def etaThetaLowerOne410 (eta theta : k) (B U : k[X]) : k[X] :=
  -(320 : k) • B ^ 4 + (2048 * theta : k) • B -
    (1024 * eta : k) • U

theorem lWallTerminalNumerator410_etaTheta_eq_fiberDerivative
    (eta theta k2 : k) (A B U : k[X])
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 0 eta theta A B U = C k2) :
    lWallTerminalNumerator410 0 0 0 0 0 eta theta A B U =
      derivative (thetaFiberPrimitive410 theta k2 A B U) := by
  rw [lWallTerminalNumerator410_mixedEffective_eq_fiberDerivative
    0 eta theta k2 A B U hTwo]
  congr 1
  simp [mixedEffectiveFiberPrimitive410, mixedEffectiveTerminalPrimitive410,
    thetaFiberPrimitive410, thetaTerminalPrimitive410]
private def threeDegreeTieEtaTheta410 (d1 d2 d3 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨ (d2 = m ∧ d3 = m)

private theorem threeTerm_degree_tie_etaTheta410
    (P1 P2 P3 : k[X]) (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0)
    (hbelow : (P1 + P2 + P3).natDegree <
      max P1.natDegree (max P2.natDegree P3.natDegree)) :
    threeDegreeTieEtaTheta410 P1.natDegree P2.natDegree P3.natDegree
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
  change ¬ threeDegreeTieEtaTheta410 P1.natDegree P2.natDegree P3.natDegree m at hnot
  rcases hcases with h1 | h2 | h3
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTieEtaTheta410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTieEtaTheta410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTieEtaTheta410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTieEtaTheta410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTieEtaTheta410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [threeDegreeTieEtaTheta410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree]] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hcoeff)

private def fourDegreeTieEtaTheta410 (d1 d2 d3 d4 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
  (d1 = m ∧ d4 = m) ∨ (d2 = m ∧ d3 = m) ∨
  (d2 = m ∧ d4 = m) ∨ (d3 = m ∧ d4 = m)

private theorem fourTerm_degree_tie_etaTheta410
    (P1 P2 P3 P4 : k[X])
    (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0) (hP4 : P4 ≠ 0)
    (hbelow : (P1 + P2 + P3 + P4).natDegree <
      max P1.natDegree (max P2.natDegree (max P3.natDegree P4.natDegree))) :
    fourDegreeTieEtaTheta410 P1.natDegree P2.natDegree P3.natDegree P4.natDegree
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
  change ¬ fourDegreeTieEtaTheta410 P1.natDegree P2.natDegree P3.natDegree
    P4.natDegree m at hnot
  rcases hcases with h1 | h2 | h3 | h4
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h1, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h1, heq])
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
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h2, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h3, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h3, heq])
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
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h4, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h4, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fourDegreeTieEtaTheta410, h4, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      show P4.coeff m = P4.leadingCoeff by rw [← h4, coeff_natDegree]] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP4) (by simpa using hcoeff)

private theorem twoTerm_degree_eq_etaTheta410 (P Q : k[X])
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hbelow : (P + Q).natDegree < max P.natDegree Q.natDegree) :
    P.natDegree = Q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt] at hbelow
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt] at hbelow
    omega

private theorem etaTheta410_nonzero_polynomials_impossible
    (eta theta k2 k1 terminal : k) (A B U : k[X]) (a b u : ℕ)
    (htheta : theta ≠ 0) (hterminal : terminal ≠ 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b)
    (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 0 eta theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 0 eta theta A B U = C k1)
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
      (480 : k) • (B * U ^ 2) + (2048 * theta : k) • A =
        C k2 - (4096 * eta : k) • B := by
    have hs := hTwo
    simp only [discriminantInvariantTwoNumerator410, zero_mul, mul_zero,
      zero_smul, add_zero, zero_add, sub_zero, neg_zero, sub_eq_add_neg,
      neg_smul] at hs
    rw [neg_smul]
    rw [← hs]
    abel
  have hmTwoPos : 0 < max (a + 3 * b) (max (b + 2 * u) a) := by omega
  have hbelowTwo :
      ((-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
        (2048 * theta : k) • A).natDegree <
          max (a + 3 * b) (max (b + 2 * u) a) := by
    rw [hsumTwo]
    compute_degree
    omega
  have hTieTwo := threeTerm_degree_tie_etaTheta410
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
        (2048 * theta : k) • B =
      C k1 - (-(1024 * eta) : k) • U := by
    have hs := hOne
    simp only [discriminantInvariantOneNumerator410, zero_mul, mul_zero,
      zero_smul, add_zero, zero_add, sub_zero, neg_zero, sub_eq_add_neg,
      neg_smul] at hs
    rw [neg_smul, neg_smul, neg_smul]
    rw [← hs]
    abel
  have hmOnePos : 0 < max (a + 2 * b + u)
      (max (4 * b) (max (3 * u) b)) := by omega
  have hbelowOne :
      ((960 : k) • (A * B ^ 2 * U) + (-(320 : k)) • B ^ 4 +
        (-(40 : k)) • U ^ 3 + (2048 * theta : k) • B).natDegree <
          max (a + 2 * b + u) (max (4 * b) (max (3 * u) b)) := by
    rw [hsumOne]
    compute_degree
    omega
  have hTieOne := fourTerm_degree_tie_etaTheta410
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
  simp only [threeDegreeTieEtaTheta410,
    natDegree_smul _ (by norm_num : (-(1280 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (480 : k) ≠ 0), natDegree_smul _ hcTheta,
    natDegree_mul hAne (pow_ne_zero 3 hBne),
    natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hA, hB, hU]
    at hTieTwo
  simp only [fourDegreeTieEtaTheta410,
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
  have hTiePrimitive := threeTerm_degree_tie_etaTheta410
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
  simp only [threeDegreeTieEtaTheta410, natDegree_smul _ hc3072,
    natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
    natDegree_smul _ (neg_ne_zero.mpr hcTheta), natDegree_pow,
    natDegree_mul (pow_ne_zero 3 hBne) hUne, hA, hB, hU] at hTiePrimitive
  have hplane : a + 2 * b = 2 * u := by omega
  have hab : 3 * a = 8 * b := by omega
  have hau : 7 * a = 8 * u := by omega
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  have hu : 0 < u := by omega
  have hLowerTwo : (etaThetaLowerTwo410 eta theta A B).natDegree < a + 3 * b := by
    simp only [etaThetaLowerTwo410]
    compute_degree
    omega
  have hLowerOne : (etaThetaLowerOne410 eta theta B U).natDegree < 3 * u := by
    simp only [etaThetaLowerOne410]
    compute_degree
    omega
  have hTwoFace : discriminantInvariantTwoNumerator410
      0 0 0 0 0 eta theta A B U =
        (-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
          etaThetaLowerTwo410 eta theta A B := by
    simp only [discriminantInvariantTwoNumerator410, etaThetaLowerTwo410,
      zero_mul, mul_zero, zero_smul, add_zero, sub_zero, sub_eq_add_neg,
      neg_smul]
    module
  have hOneFace : discriminantInvariantOneNumerator410
      0 0 0 0 0 eta theta A B U =
        (960 : k) • (A * B ^ 2 * U) + (-(40 : k)) • U ^ 3 +
          etaThetaLowerOne410 eta theta B U := by
    simp only [discriminantInvariantOneNumerator410, etaThetaLowerOne410,
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

theorem etaTheta410_discriminant_coordinate_selector
    (eta theta k2 k1 terminal : k) (A B U : k[X])
    (htheta : theta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 0 eta theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 0 eta theta A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 0 0 eta theta A B U = C terminal) :
    A = 0 ∨ B = 0 ∨ U = 0 := by
  have hDerivative : derivative (thetaFiberPrimitive410 theta k2 A B U) =
      C terminal := by
    rw [← lWallTerminalNumerator410_etaTheta_eq_fiberDerivative
      eta theta k2 A B U hTwo]
    exact hTerminal
  have hDegree : (thetaFiberPrimitive410 theta k2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (thetaFiberPrimitive410 theta k2 A B U) terminal hterminal hDerivative
  by_cases hAzero : A = 0
  · exact Or.inl hAzero
  · by_cases hBzero : B = 0
    · exact Or.inr (Or.inl hBzero)
    · by_cases hUzero : U = 0
      · exact Or.inr (Or.inr hUzero)
      · exact (etaTheta410_nonzero_polynomials_impossible eta theta k2 k1
          terminal A B U A.natDegree B.natDegree U.natDegree htheta hterminal
          hAzero hBzero hUzero rfl rfl rfl hTwo hOne hDegree).elim

theorem etaTheta410_original_coordinate_selector
    (alpha epsilon eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (htheta : theta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 0 eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 0 eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon 0 theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon 0 eta iota A B C0)
      B C0 = C terminal) :
    A = 0 ∨ B = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 := by
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 0 0 0 eta theta A B (A ^ 2 - (4 : k) • C0) =
        C (2048 * k2) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD : discriminantInvariantOneNumerator410
      0 0 0 0 0 eta theta A B (A ^ 2 - (4 : k) • C0) =
        C (2048 * k1) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410
      0 0 0 0 0 eta theta A B (A ^ 2 - (4 : k) • C0) =
        C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact etaTheta410_discriminant_coordinate_selector eta theta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) htheta
      (mul_ne_zero (by norm_num) hterminal) hTwoD hOneD hTerminalD

/-- All nondegenerate effective-load cones are closed. -/
theorem mixedEffective410_coordinate_residual
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
    A = 0 ∨ B = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 := by
  have hpacket := mixedEffective410_finite_residual_packet
    (k := k) alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
      hterminal hTwo hOne hLower
  rcases hpacket with hetaTheta | hcoordinate
  · rcases hetaTheta with ⟨hzeta, heta, htheta⟩
    subst zeta
    exact etaTheta410_original_coordinate_selector alpha epsilon eta theta iota
      k2 k1 terminal A B C0 htheta hterminal hTwo hOne hLower
  · exact hcoordinate

theorem mixedEffective410_zeroB_discriminant_impossible
    (zeta eta theta k2 k1 terminal : k) (A B U : k[X])
    (hload : zeta ≠ 0 ∨ theta ≠ 0) (hterminal : terminal ≠ 0)
    (hBzero : B = 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta eta theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 zeta eta theta A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 0 zeta eta theta A B U = C terminal) : False := by
  subst B
  have hDerivative : derivative
      (mixedEffectiveFiberPrimitive410 zeta theta k2 A 0 U) = C terminal := by
    rw [← lWallTerminalNumerator410_mixedEffective_eq_fiberDerivative
      zeta eta theta k2 A 0 U hTwo]
    exact hTerminal
  have hDegree :
      (mixedEffectiveFiberPrimitive410 zeta theta k2 A 0 U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (mixedEffectiveFiberPrimitive410 zeta theta k2 A 0 U)
      terminal hterminal hDerivative
  have hUdegree : U.natDegree = 0 := by
    by_contra hUzero
    have hUpos : 0 < U.natDegree := by omega
    have hUne : U ≠ 0 := by
      intro hz
      subst U
      exact hUzero natDegree_zero
    let R : k[X] := -((1024 * eta : k) • U)
    have hOneForm : (-(40 : k)) • U ^ 3 + R = C k1 := by
      have hs := hOne
      simp [discriminantInvariantOneNumerator410] at hs
      rw [neg_smul]
      dsimp only [R]
      simpa only [sub_eq_add_neg] using hs
    have hRdegree : R.natDegree < 3 * U.natDegree := by
      dsimp only [R]
      compute_degree
      omega
    exact (smul_add_lower_ne_C410 (-(40 : k)) k1 (U ^ 3) R
      (3 * U.natDegree) (by norm_num) (pow_ne_zero 3 hUne) (by omega)
      (by rw [natDegree_pow]) hRdegree) hOneForm
  have hAdegree : A.natDegree = 0 := by
    by_cases hzeta : zeta = 0
    · have htheta : theta ≠ 0 := hload.resolve_left (by simpa using hzeta)
      subst zeta
      have hAeq : (2048 * theta : k) • A = C k2 := by
        have hs := hTwo
        simp [discriminantInvariantTwoNumerator410] at hs
        simpa using hs
      have hd := congrArg Polynomial.natDegree hAeq
      rw [natDegree_smul A (mul_ne_zero (by norm_num) htheta), natDegree_C] at hd
      exact hd
    · by_contra hAzero
      have hApos : 0 < A.natDegree := by omega
      have hAne : A ≠ 0 := by
        intro hz
        subst A
        exact hAzero natDegree_zero
      let R : k[X] := (2048 * theta : k) • A - (1536 * zeta : k) • U
      have hTwoForm : (768 * zeta : k) • A ^ 2 + R = C k2 := by
        have hs := hTwo
        simp [discriminantInvariantTwoNumerator410] at hs
        calc
          (768 * zeta : k) • A ^ 2 + R =
              (768 * zeta : k) • A ^ 2 + (2048 * theta : k) • A -
                (1536 * zeta : k) • U := by
            dsimp only [R]
            abel
          _ = C k2 := hs
      have hRdegree : R.natDegree < 2 * A.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      exact (smul_add_lower_ne_C410 (768 * zeta) k2 (A ^ 2) R
        (2 * A.natDegree) (mul_ne_zero (by norm_num) hzeta)
        (pow_ne_zero 2 hAne) (by omega) (by rw [natDegree_pow])
        hRdegree) hTwoForm
  have hle :
      (mixedEffectiveFiberPrimitive410 zeta theta k2 A 0 U).natDegree ≤ 0 := by
    simp only [mixedEffectiveFiberPrimitive410, mixedEffectiveTerminalPrimitive410]
    compute_degree
    omega
  omega

theorem mixedEffective410_zeroU_discriminant_impossible
    (zeta eta theta k2 k1 terminal : k) (A B U : k[X])
    (hload : zeta ≠ 0 ∨ theta ≠ 0) (hterminal : terminal ≠ 0)
    (hUzero : U = 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta eta theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 zeta eta theta A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 0 zeta eta theta A B U = C terminal) : False := by
  subst U
  have hDerivative : derivative
      (mixedEffectiveFiberPrimitive410 zeta theta k2 A B 0) = C terminal := by
    rw [← lWallTerminalNumerator410_mixedEffective_eq_fiberDerivative
      zeta eta theta k2 A B 0 hTwo]
    exact hTerminal
  have hDegree :
      (mixedEffectiveFiberPrimitive410 zeta theta k2 A B 0).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (mixedEffectiveFiberPrimitive410 zeta theta k2 A B 0)
      terminal hterminal hDerivative
  by_cases hzeta : zeta = 0
  · have htheta : theta ≠ 0 := hload.resolve_left (by simpa using hzeta)
    subst zeta
    have hBdegree : B.natDegree = 0 := by
      by_contra hBzero
      have hBpos : 0 < B.natDegree := by omega
      have hBne : B ≠ 0 := by
        intro hz
        subst B
        exact hBzero natDegree_zero
      let R : k[X] := (2048 * theta : k) • B
      have hOneForm : (-(320 : k)) • B ^ 4 + R = C k1 := by
        have hs := hOne
        simp [discriminantInvariantOneNumerator410] at hs
        rw [neg_smul]
        dsimp only [R]
        simpa only [sub_eq_add_neg, add_comm] using hs
      have hRdegree : R.natDegree < 4 * B.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      exact (smul_add_lower_ne_C410 (-(320 : k)) k1 (B ^ 4) R
        (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hBne) (by omega)
        (by rw [natDegree_pow]) hRdegree) hOneForm
    by_cases hAdegree : A.natDegree = 0
    · have hle :
          (mixedEffectiveFiberPrimitive410 0 theta k2 A B 0).natDegree ≤ 0 := by
        simp only [mixedEffectiveFiberPrimitive410,
          mixedEffectiveTerminalPrimitive410]
        compute_degree
        omega
      omega
    · have hApos : 0 < A.natDegree := by omega
      have hAne : A ≠ 0 := by
        intro hz
        subst A
        exact hAdegree natDegree_zero
      let R : k[X] := -(k2 • A)
      have hFiberForm : mixedEffectiveFiberPrimitive410 0 theta k2 A B 0 =
          (3072 * theta : k) • A ^ 2 + R := by
        have hTerminalZero : mixedEffectiveTerminalPrimitive410 0 theta A B 0 =
            (3072 * theta : k) • A ^ 2 := by
          simp [mixedEffectiveTerminalPrimitive410]
        rw [mixedEffectiveFiberPrimitive410, hTerminalZero]
        dsimp only [R]
        abel
      have hRdegree : R.natDegree < 2 * A.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      have hMainDegree : ((3072 * theta : k) • A ^ 2).natDegree =
          2 * A.natDegree := by
        rw [natDegree_smul _ (mul_ne_zero (by norm_num) htheta), natDegree_pow]
      have hFiberDegree :
          (mixedEffectiveFiberPrimitive410 0 theta k2 A B 0).natDegree =
            2 * A.natDegree := by
        rw [hFiberForm, natDegree_add_eq_left_of_natDegree_lt]
        · exact hMainDegree
        · rw [hMainDegree]
          exact hRdegree
      omega
  · by_cases hAzero : A = 0
    · subst A
      have hBdegree : B.natDegree = 0 := by
        by_contra hBzero
        have hBpos : 0 < B.natDegree := by omega
        have hBne : B ≠ 0 := by
          intro hz
          subst B
          exact hBzero natDegree_zero
        let R : k[X] := (2048 * theta : k) • B
        have hOneForm : (-(320 : k)) • B ^ 4 + R = C k1 := by
          have hs := hOne
          simp [discriminantInvariantOneNumerator410] at hs
          rw [neg_smul]
          dsimp only [R]
          simpa only [sub_eq_add_neg, add_comm] using hs
        have hRdegree : R.natDegree < 4 * B.natDegree := by
          dsimp only [R]
          compute_degree
          omega
        exact (smul_add_lower_ne_C410 (-(320 : k)) k1 (B ^ 4) R
          (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hBne) (by omega)
          (by rw [natDegree_pow]) hRdegree) hOneForm
      have hle :
          (mixedEffectiveFiberPrimitive410 zeta theta k2 0 B 0).natDegree ≤ 0 := by
        simp only [mixedEffectiveFiberPrimitive410,
          mixedEffectiveTerminalPrimitive410]
        compute_degree
        omega
      omega
    · by_cases hBzero : B = 0
      · exact mixedEffective410_zeroB_discriminant_impossible zeta eta theta
          k2 k1 terminal A B 0 (Or.inl hzeta) hterminal hBzero
          hTwo hOne hTerminal
      · have hpositive : 0 < A.natDegree ∨ 0 < B.natDegree := by
          by_contra hnone
          push_neg at hnone
          have hle :
              (mixedEffectiveFiberPrimitive410 zeta theta k2 A B 0).natDegree ≤
                0 := by
            simp only [mixedEffectiveFiberPrimitive410,
              mixedEffectiveTerminalPrimitive410]
            compute_degree
            omega
          omega
        have hsumOne : (-(1536 * zeta) : k) • (A * B) +
            (-(320 : k)) • B ^ 4 = C k1 - (2048 * theta : k) • B := by
          have hs := hOne
          simp [discriminantInvariantOneNumerator410] at hs
          rw [neg_smul, neg_smul]
          rw [← hs]
          abel
        have hmpos : 0 < max (A.natDegree + B.natDegree)
            (4 * B.natDegree) := by omega
        have hbelow : ((-(1536 * zeta) : k) • (A * B) +
            (-(320 : k)) • B ^ 4).natDegree <
              max (A.natDegree + B.natDegree) (4 * B.natDegree) := by
          rw [hsumOne]
          compute_degree
          omega
        have htie := twoTerm_degree_eq_etaTheta410
          ((-(1536 * zeta) : k) • (A * B)) ((-(320 : k)) • B ^ 4)
          (by
            intro hz
            exact (mul_ne_zero hAzero hBzero)
              ((smul_eq_zero.mp hz).resolve_left
                (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hzeta))))
          (by
            intro hz
            exact (pow_ne_zero 4 hBzero)
              ((smul_eq_zero.mp hz).resolve_left (by norm_num)))
          (by
            simpa only [natDegree_smul _ (neg_ne_zero.mpr
                (mul_ne_zero (by norm_num : (1536 : k) ≠ 0) hzeta)),
              natDegree_smul _ (by norm_num : (-(320 : k)) ≠ 0),
              natDegree_mul hAzero hBzero, natDegree_pow] using hbelow)
        have hplane : A.natDegree = 3 * B.natDegree := by
          have heq : A.natDegree + B.natDegree = 4 * B.natDegree := by
            simpa only [natDegree_smul _ (neg_ne_zero.mpr
                (mul_ne_zero (by norm_num : (1536 : k) ≠ 0) hzeta)),
              natDegree_smul _ (by norm_num : (-(320 : k)) ≠ 0),
              natDegree_mul hAzero hBzero, natDegree_pow] using htie
          omega
        have hBpos : 0 < B.natDegree := by omega
        have hApos : 0 < A.natDegree := by omega
        let R : k[X] := (3072 * theta : k) • A ^ 2 -
          (3072 * zeta : k) • B ^ 2 - k2 • A
        have hFiberForm : mixedEffectiveFiberPrimitive410 zeta theta k2 A B 0 =
            (1280 * zeta : k) • A ^ 3 + R := by
          have hTerminalZero : mixedEffectiveTerminalPrimitive410
              zeta theta A B 0 =
                (1280 * zeta : k) • A ^ 3 + (3072 * theta : k) • A ^ 2 -
                  (3072 * zeta : k) • B ^ 2 := by
            simp [mixedEffectiveTerminalPrimitive410]
          rw [mixedEffectiveFiberPrimitive410, hTerminalZero]
          dsimp only [R]
          abel
        have hRdegree : R.natDegree < 3 * A.natDegree := by
          dsimp only [R]
          compute_degree
          omega
        have hMainDegree : ((1280 * zeta : k) • A ^ 3).natDegree =
            3 * A.natDegree := by
          rw [natDegree_smul _ (mul_ne_zero (by norm_num) hzeta), natDegree_pow]
        have hFiberDegree :
            (mixedEffectiveFiberPrimitive410 zeta theta k2 A B 0).natDegree =
              3 * A.natDegree := by
          rw [hFiberForm, natDegree_add_eq_left_of_natDegree_lt]
          · exact hMainDegree
          · rw [hMainDegree]
            exact hRdegree
        omega

theorem mixedEffective410_zeroA_discriminant_impossible
    (zeta eta theta k2 k1 terminal : k) (A B U : k[X])
    (hload : zeta ≠ 0 ∨ theta ≠ 0) (hterminal : terminal ≠ 0)
    (hAzero : A = 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 0 zeta eta theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 0 zeta eta theta A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 0 zeta eta theta A B U = C terminal) : False := by
  subst A
  have hDerivative : derivative
      (mixedEffectiveFiberPrimitive410 zeta theta k2 0 B U) = C terminal := by
    rw [← lWallTerminalNumerator410_mixedEffective_eq_fiberDerivative
      zeta eta theta k2 0 B U hTwo]
    exact hTerminal
  have hDegree :
      (mixedEffectiveFiberPrimitive410 zeta theta k2 0 B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (mixedEffectiveFiberPrimitive410 zeta theta k2 0 B U)
      terminal hterminal hDerivative
  by_cases hBzero : B = 0
  · exact mixedEffective410_zeroB_discriminant_impossible zeta eta theta
      k2 k1 terminal 0 B U hload hterminal hBzero hTwo hOne hTerminal
  · have hUdegree : U.natDegree = 0 := by
      by_contra hUzero
      have hUpos : 0 < U.natDegree := by omega
      have hUne : U ≠ 0 := by
        intro hz
        subst U
        exact hUzero natDegree_zero
      let R : k[X] := (4096 * eta : k) • B - (1536 * zeta : k) • U
      have hTwoForm : (480 : k) • (B * U ^ 2) + R = C k2 := by
        have hs := hTwo
        simp [discriminantInvariantTwoNumerator410] at hs
        calc
          (480 : k) • (B * U ^ 2) + R =
              (480 : k) • (B * U ^ 2) + (4096 * eta : k) • B -
                (1536 * zeta : k) • U := by
            dsimp only [R]
            abel
          _ = C k2 := hs
      have hMainDegree : (B * U ^ 2).natDegree =
          B.natDegree + 2 * U.natDegree := by
        rw [natDegree_mul hBzero (pow_ne_zero 2 hUne), natDegree_pow]
      have hRdegree : R.natDegree < B.natDegree + 2 * U.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      exact (smul_add_lower_ne_C410 (480 : k) k2 (B * U ^ 2) R
        (B.natDegree + 2 * U.natDegree) (by norm_num)
        (mul_ne_zero hBzero (pow_ne_zero 2 hUne)) (by omega)
        hMainDegree hRdegree) hTwoForm
    have hBdegree : B.natDegree = 0 := by
      by_contra hBconstant
      have hBpos : 0 < B.natDegree := by omega
      let R : k[X] := (-(40 : k)) • U ^ 3 +
        (2048 * theta : k) • B - (1024 * eta : k) • U
      have hOneForm : (-(320 : k)) • B ^ 4 + R = C k1 := by
        have hs := hOne
        simp [discriminantInvariantOneNumerator410] at hs
        rw [neg_smul]
        rw [← hs]
        dsimp only [R]
        rw [neg_smul]
        abel
      have hRdegree : R.natDegree < 4 * B.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      exact (smul_add_lower_ne_C410 (-(320 : k)) k1 (B ^ 4) R
        (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hBzero) (by omega)
        (by rw [natDegree_pow]) hRdegree) hOneForm
    have hle :
        (mixedEffectiveFiberPrimitive410 zeta theta k2 0 B U).natDegree ≤ 0 := by
      simp only [mixedEffectiveFiberPrimitive410,
        mixedEffectiveTerminalPrimitive410]
      compute_degree
      omega
    omega

theorem mixedEffective410_zeroA_original_impossible
    (alpha epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hload : zeta ≠ 0 ∨ theta ≠ 0)
    (hterminal : terminal ≠ 0) (hAzero : A = 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
      B C0 = C terminal) : False := by
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
  exact mixedEffective410_zeroA_discriminant_impossible zeta eta theta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) hload (mul_ne_zero (by norm_num) hterminal)
      hAzero hTwoD hOneD hTerminalD

theorem mixedEffective410_zeroU_original_impossible
    (alpha epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hload : zeta ≠ 0 ∨ theta ≠ 0)
    (hterminal : terminal ≠ 0)
    (hUzero : A ^ 2 - (4 : k) • C0 = 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
      B C0 = C terminal) : False := by
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
  exact mixedEffective410_zeroU_discriminant_impossible zeta eta theta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) hload (mul_ne_zero (by norm_num) hterminal)
      hUzero hTwoD hOneD hTerminalD

theorem mixedEffective410_zeroB_original_impossible
    (alpha epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hload : zeta ≠ 0 ∨ theta ≠ 0)
    (hterminal : terminal ≠ 0) (hBzero : B = 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
      B C0 = C terminal) : False := by
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
  exact mixedEffective410_zeroB_discriminant_impossible zeta eta theta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) hload (mul_ne_zero (by norm_num) hterminal)
      hBzero hTwoD hOneD hTerminalD

/-- The sharp residual after closing the nondegenerate cones and the `B = 0`
face consists of the `A = 0` and discriminant-zero faces. -/
theorem mixedEffective410_two_face_residual
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
    A = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 := by
  have hcoordinate := mixedEffective410_coordinate_residual
    (k := k) alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
      hterminal hTwo hOne hLower
  rcases hcoordinate with hA | hB | hU
  · exact Or.inl hA
  · have hpair := zetaEtaTheta410_pairwise_nonzero_residual
      (k := k) alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
        hterminal hTwo hOne hLower
    have hload : zeta ≠ 0 ∨ theta ≠ 0 := by
      rcases hpair with hze | hzt | het
      · exact Or.inl hze.1
      · exact Or.inl hzt.1
      · exact Or.inr het.2
    exact (mixedEffective410_zeroB_original_impossible alpha epsilon zeta eta
      theta iota k2 k1 terminal A B C0 hload hterminal hB hTwo hOne hLower).elim
  · exact Or.inr hU

/-- After eliminating the discriminant-zero face, every remaining trajectory
lies on the single face `A = 0`. -/
theorem mixedEffective410_single_face_residual
    (alpha epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
      B C0 = C terminal) : A = 0 := by
  have hfaces := mixedEffective410_two_face_residual
    (k := k) alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
      hterminal hTwo hOne hLower
  rcases hfaces with hA | hU
  · exact hA
  · have hpair := zetaEtaTheta410_pairwise_nonzero_residual
      (k := k) alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
        hterminal hTwo hOne hLower
    have hload : zeta ≠ 0 ∨ theta ≠ 0 := by
      rcases hpair with hze | hzt | het
      · exact Or.inl hze.1
      · exact Or.inl hzt.1
      · exact Or.inr het.2
    exact (mixedEffective410_zeroU_original_impossible alpha epsilon zeta eta
      theta iota k2 k1 terminal A B C0 hload hterminal hU hTwo hOne hLower).elim

/-- All effective-load trajectories remaining after the earlier load cascade
are impossible. -/
theorem mixedEffective410_original_trajectory_impossible
    (alpha epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 0 zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 0 epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 0 epsilon zeta eta iota A B C0)
      B C0 = C terminal) : False := by
  have hAzero := mixedEffective410_single_face_residual
    (k := k) alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
      hterminal hTwo hOne hLower
  have hpair := zetaEtaTheta410_pairwise_nonzero_residual
    (k := k) alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
      hterminal hTwo hOne hLower
  have hload : zeta ≠ 0 ∨ theta ≠ 0 := by
    rcases hpair with hze | hzt | het
    · exact Or.inl hze.1
    · exact Or.inl hzt.1
    · exact Or.inr het.2
  exact mixedEffective410_zeroA_original_impossible alpha epsilon zeta eta
    theta iota k2 k1 terminal A B C0 hload hterminal hAzero hTwo hOne hLower

end EtaThetaAndDegenerate410

end Max11DegreeRoutes
