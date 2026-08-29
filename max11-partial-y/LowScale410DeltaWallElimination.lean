import LowScale410DeltaWall

/-!
# Elimination of the pure delta wall

The two constant invariant curves and the degree-one terminal primitive have
only one possible nondegenerate Newton ray.  Its degree ratio is
`(deg A, deg B, deg U) = (8,7,11)` up to scale.  The two invariant faces on
that ray give incompatible leading-coefficient equations.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section DeltaWallElimination410

variable {k : Type*} [Field k] [CharZero k]

private def fiveDegreeTie410 (d1 d2 d3 d4 d5 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
  (d1 = m ∧ d4 = m) ∨ (d1 = m ∧ d5 = m) ∨
  (d2 = m ∧ d3 = m) ∨ (d2 = m ∧ d4 = m) ∨
  (d2 = m ∧ d5 = m) ∨ (d3 = m ∧ d4 = m) ∨
  (d3 = m ∧ d5 = m) ∨ (d4 = m ∧ d5 = m)

/-- If five nonzero summands add to a polynomial of degree below the largest
summand degree, at least two summands lie on the largest face. -/
private theorem fiveTerm_degree_tie410
    (P1 P2 P3 P4 P5 : k[X])
    (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0)
    (hP4 : P4 ≠ 0) (hP5 : P5 ≠ 0)
    (hbelow : (P1 + P2 + P3 + P4 + P5).natDegree <
      max P1.natDegree (max P2.natDegree
        (max P3.natDegree (max P4.natDegree P5.natDegree)))) :
    fiveDegreeTie410 P1.natDegree P2.natDegree P3.natDegree
      P4.natDegree P5.natDegree
      (max P1.natDegree (max P2.natDegree
        (max P3.natDegree (max P4.natDegree P5.natDegree)))) := by
  let m := max P1.natDegree (max P2.natDegree
    (max P3.natDegree (max P4.natDegree P5.natDegree)))
  have h1le : P1.natDegree ≤ m := by dsimp [m]; omega
  have h2le : P2.natDegree ≤ m := by dsimp [m]; omega
  have h3le : P3.natDegree ≤ m := by dsimp [m]; omega
  have h4le : P4.natDegree ≤ m := by dsimp [m]; omega
  have h5le : P5.natDegree ≤ m := by dsimp [m]; omega
  have hcases : P1.natDegree = m ∨ P2.natDegree = m ∨
      P3.natDegree = m ∨ P4.natDegree = m ∨ P5.natDegree = m := by
    dsimp [m]
    omega
  have hsumcoeff :
      (P1 + P2 + P3 + P4 + P5).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [m] using hbelow
  by_contra hnot
  change ¬ fiveDegreeTie410 P1.natDegree P2.natDegree P3.natDegree
    P4.natDegree P5.natDegree m at hnot
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h1, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h1, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt,
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h2, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h2, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt,
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h3, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h3, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h4lt,
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h4, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h4, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h4, heq])
    have h5ne : P5.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h4, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h5lt : P5.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      show P4.coeff m = P4.leadingCoeff by rw [← h4, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h5lt] at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP4) (by simpa using hsumcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h5, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h5, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h5, heq])
    have h4ne : P4.natDegree ≠ m := by
      intro heq; exact hnot (by simp [fiveDegreeTie410, h5, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    have h4lt : P4.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_add, coeff_add,
      coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt,
      coeff_eq_zero_of_natDegree_lt h4lt,
      show P5.coeff m = P5.leadingCoeff by rw [← h5, coeff_natDegree]]
      at hsumcoeff
    exact (leadingCoeff_ne_zero.mpr hP5) (by simpa using hsumcoeff)

private theorem twoTerm_degree_eq410 (P Q : k[X])
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hbelow : (P + Q).natDegree < max P.natDegree Q.natDegree) :
    P.natDegree = Q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt] at hbelow
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt] at hbelow
    omega

private def deltaLowerTwo410 (delta : k) (A B U : k[X]) : k[X] :=
  (2 * delta : k) • A ^ 3 - (4 * delta : k) • (A * U) +
    (8 * delta : k) • B ^ 2

private def deltaLowerOne410 (delta : k) (A B U : k[X]) : k[X] :=
  -(8 * delta : k) • (A ^ 2 * B) -
    (16 * delta : k) • (B * U) - (8 : k) • B ^ 4

private theorem deltaCurveTwo410_face
    (delta : k) (A B U : k[X]) :
    deltaCurveTwo410 delta A B U =
      -(8 : k) • (A * B ^ 3) + (3 : k) • (B * U ^ 2) +
        deltaLowerTwo410 delta A B U := by
  simp only [deltaCurveTwo410, deltaLowerTwo410]
  module

private theorem deltaCurveOne410_face
    (delta : k) (A B U : k[X]) :
    deltaCurveOne410 delta A B U =
      (24 : k) • (A * B ^ 2 * U) - U ^ 3 +
        deltaLowerOne410 delta A B U := by
  simp only [deltaCurveOne410, deltaLowerOne410]
  module

private theorem deltaOnly410_nonzero_polynomials_impossible
    (delta k2 k1 terminal : k) (A B U : k[X]) (a b u : ℕ)
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b)
    (hU : U.natDegree = u)
    (hTwo : deltaCurveTwo410 delta A B U = C k2)
    (hOne : deltaCurveOne410 delta A B U = C k1)
    (hDegree : (deltaFiberPrimitive410 delta (160 * k2) A B U).natDegree = 1) :
    False := by
  have hpositive : 0 < a ∨ 0 < b ∨ 0 < u := by
    by_contra hnone
    push_neg at hnone
    have hle :
        (deltaFiberPrimitive410 delta (160 * k2) A B U).natDegree ≤ 0 := by
      simp only [deltaFiberPrimitive410, deltaTerminalPrimitive410]
      compute_degree
      omega
    omega
  have hsmul {c : k} {P : k[X]} (hc : c ≠ 0) (hP : P ≠ 0) : c • P ≠ 0 := by
    intro hz
    exact hP ((smul_eq_zero.mp hz).resolve_left hc)
  have hc2 : (2 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc4 : (4 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc8 : (8 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc16 : (16 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc560 : (560 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc960 : (960 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc1280d : (1280 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc320 : (320 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hsumTwo :
      (2 * delta : k) • A ^ 3 + (-(4 * delta) : k) • (A * U) +
          (8 * delta : k) • B ^ 2 + (-(8 : k)) • (A * B ^ 3) +
            (3 : k) • (B * U ^ 2) = C k2 := by
    simpa only [deltaCurveTwo410, sub_eq_add_neg, neg_smul] using hTwo
  have hmTwoPos : 0 < max (3 * a)
      (max (a + u) (max (2 * b) (max (a + 3 * b) (b + 2 * u)))) := by
    omega
  have hbelowTwo :
      ((2 * delta : k) • A ^ 3 + (-(4 * delta) : k) • (A * U) +
          (8 * delta : k) • B ^ 2 + (-(8 : k)) • (A * B ^ 3) +
            (3 : k) • (B * U ^ 2)).natDegree <
        max (3 * a)
          (max (a + u) (max (2 * b) (max (a + 3 * b) (b + 2 * u)))) := by
    rw [hsumTwo, natDegree_C]
    exact hmTwoPos
  have hTieTwo := fiveTerm_degree_tie410
    ((2 * delta : k) • A ^ 3) ((-(4 * delta) : k) • (A * U))
    ((8 * delta : k) • B ^ 2) ((-(8 : k)) • (A * B ^ 3))
    ((3 : k) • (B * U ^ 2))
    (hsmul hc2 (pow_ne_zero 3 hAne))
    (hsmul (neg_ne_zero.mpr hc4) (mul_ne_zero hAne hUne))
    (hsmul hc8 (pow_ne_zero 2 hBne))
    (hsmul (by norm_num) (mul_ne_zero hAne (pow_ne_zero 3 hBne)))
    (hsmul (by norm_num) (mul_ne_zero hBne (pow_ne_zero 2 hUne)))
    (by
      simpa only [natDegree_smul _ hc2, natDegree_smul _ (neg_ne_zero.mpr hc4),
        natDegree_smul _ hc8, natDegree_smul _ (by norm_num : (-(8 : k)) ≠ 0),
        natDegree_smul _ (by norm_num : (3 : k) ≠ 0), natDegree_pow,
        natDegree_mul hAne hUne,
        natDegree_mul hAne (pow_ne_zero 3 hBne),
        natDegree_mul hBne (pow_ne_zero 2 hUne), hA, hB, hU] using hbelowTwo)
  have hsumOne :
      (-(8 * delta) : k) • (A ^ 2 * B) +
          (-(16 * delta) : k) • (B * U) +
          (24 : k) • (A * B ^ 2 * U) + (-(8 : k)) • B ^ 4 +
            (-(1 : k)) • U ^ 3 = C k1 := by
    simpa only [deltaCurveOne410, sub_eq_add_neg, neg_smul, one_smul]
      using hOne
  have hmOnePos : 0 < max (2 * a + b)
      (max (b + u) (max (a + 2 * b + u) (max (4 * b) (3 * u)))) := by
    omega
  have hbelowOne :
      ((-(8 * delta) : k) • (A ^ 2 * B) +
          (-(16 * delta) : k) • (B * U) +
          (24 : k) • (A * B ^ 2 * U) + (-(8 : k)) • B ^ 4 +
            (-(1 : k)) • U ^ 3).natDegree <
        max (2 * a + b)
          (max (b + u) (max (a + 2 * b + u) (max (4 * b) (3 * u)))) := by
    rw [hsumOne, natDegree_C]
    exact hmOnePos
  have hTieOne := fiveTerm_degree_tie410
    ((-(8 * delta) : k) • (A ^ 2 * B))
    ((-(16 * delta) : k) • (B * U))
    ((24 : k) • (A * B ^ 2 * U)) ((-(8 : k)) • B ^ 4)
    ((-(1 : k)) • U ^ 3)
    (hsmul (neg_ne_zero.mpr hc8) (mul_ne_zero (pow_ne_zero 2 hAne) hBne))
    (hsmul (neg_ne_zero.mpr hc16) (mul_ne_zero hBne hUne))
    (hsmul (by norm_num)
      (mul_ne_zero (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne))
    (hsmul (by norm_num) (pow_ne_zero 4 hBne))
    (hsmul (by norm_num) (pow_ne_zero 3 hUne))
    (by
      simpa only [natDegree_smul _ (neg_ne_zero.mpr hc8),
        natDegree_smul _ (neg_ne_zero.mpr hc16),
        natDegree_smul _ (by norm_num : (24 : k) ≠ 0),
        natDegree_smul _ (by norm_num : (-(8 : k)) ≠ 0),
        natDegree_smul _ (by norm_num : (-(1 : k)) ≠ 0), natDegree_pow,
        natDegree_mul (pow_ne_zero 2 hAne) hBne,
        natDegree_mul hBne hUne,
        natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
        natDegree_mul hAne (pow_ne_zero 2 hBne), hA, hB, hU] using hbelowOne)
  have hPrimitiveForm : deltaTerminalPrimitive410 delta A B U =
      deltaFiberPrimitive410 delta (160 * k2) A B U + (160 * k2) • A := by
    simp only [deltaFiberPrimitive410]
    abel
  have hPrimitiveLe :
      (deltaTerminalPrimitive410 delta A B U).natDegree ≤ max 1 a := by
    rw [hPrimitiveForm]
    compute_degree
    omega
  have hmPrimitivePos : max 1 a < max (4 * a)
      (max (2 * a + u) (max (a + 2 * b) (max (3 * b + u) (2 * u)))) := by
    omega
  have hbelowPrimitive :
      ((560 * delta : k) • A ^ 4 + (-(960 * delta) : k) • (A ^ 2 * U) +
          (-(1280 * delta) : k) • (A * B ^ 2) +
          (1280 : k) • (B ^ 3 * U) + (320 * delta : k) • U ^ 2).natDegree <
        max (4 * a)
          (max (2 * a + u) (max (a + 2 * b) (max (3 * b + u) (2 * u)))) := by
    have hrewrite :
        (560 * delta : k) • A ^ 4 + (-(960 * delta) : k) • (A ^ 2 * U) +
            (-(1280 * delta) : k) • (A * B ^ 2) +
            (1280 : k) • (B ^ 3 * U) + (320 * delta : k) • U ^ 2 =
          deltaTerminalPrimitive410 delta A B U := by
      simp only [deltaTerminalPrimitive410, sub_eq_add_neg, neg_smul]
    rw [hrewrite]
    exact hPrimitiveLe.trans_lt hmPrimitivePos
  have hTiePrimitive := fiveTerm_degree_tie410
    ((560 * delta : k) • A ^ 4)
    ((-(960 * delta) : k) • (A ^ 2 * U))
    ((-(1280 * delta) : k) • (A * B ^ 2))
    ((1280 : k) • (B ^ 3 * U)) ((320 * delta : k) • U ^ 2)
    (hsmul hc560 (pow_ne_zero 4 hAne))
    (hsmul (neg_ne_zero.mpr hc960) (mul_ne_zero (pow_ne_zero 2 hAne) hUne))
    (hsmul (neg_ne_zero.mpr hc1280d) (mul_ne_zero hAne (pow_ne_zero 2 hBne)))
    (hsmul (by norm_num) (mul_ne_zero (pow_ne_zero 3 hBne) hUne))
    (hsmul hc320 (pow_ne_zero 2 hUne))
    (by
      simpa only [natDegree_smul _ hc560,
        natDegree_smul _ (neg_ne_zero.mpr hc960),
        natDegree_smul _ (neg_ne_zero.mpr hc1280d),
        natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
        natDegree_smul _ hc320, natDegree_pow,
        natDegree_mul (pow_ne_zero 2 hAne) hUne,
        natDegree_mul hAne (pow_ne_zero 2 hBne),
        natDegree_mul (pow_ne_zero 3 hBne) hUne, hA, hB, hU]
        using hbelowPrimitive)
  simp only [fiveDegreeTie410, natDegree_smul _ hc2,
    natDegree_smul _ (neg_ne_zero.mpr hc4), natDegree_smul _ hc8,
    natDegree_smul _ (by norm_num : (-(8 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (3 : k) ≠ 0), natDegree_pow,
    natDegree_mul hAne hUne,
    natDegree_mul hAne (pow_ne_zero 3 hBne),
    natDegree_mul hBne (pow_ne_zero 2 hUne), hA, hB, hU] at hTieTwo
  simp only [fiveDegreeTie410,
    natDegree_smul _ (neg_ne_zero.mpr hc8),
    natDegree_smul _ (neg_ne_zero.mpr hc16),
    natDegree_smul _ (by norm_num : (24 : k) ≠ 0),
    natDegree_smul _ (by norm_num : (-(8 : k)) ≠ 0),
    natDegree_smul _ (by norm_num : (-(1 : k)) ≠ 0), natDegree_pow,
    natDegree_mul (pow_ne_zero 2 hAne) hBne,
    natDegree_mul hBne hUne,
    natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
    natDegree_mul hAne (pow_ne_zero 2 hBne), hA, hB, hU] at hTieOne
  simp only [fiveDegreeTie410, natDegree_smul _ hc560,
    natDegree_smul _ (neg_ne_zero.mpr hc960),
    natDegree_smul _ (neg_ne_zero.mpr hc1280d),
    natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
    natDegree_smul _ hc320, natDegree_pow,
    natDegree_mul (pow_ne_zero 2 hAne) hUne,
    natDegree_mul hAne (pow_ne_zero 2 hBne),
    natDegree_mul (pow_ne_zero 3 hBne) hUne, hA, hB, hU] at hTiePrimitive
  have hplane : a + 2 * b = 2 * u := by omega
  have hab : 7 * a = 8 * b := by omega
  have hau : 11 * a = 8 * u := by omega
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  have hu : 0 < u := by omega
  have hLowerTwo : (deltaLowerTwo410 delta A B U).natDegree < a + 3 * b := by
    simp only [deltaLowerTwo410]
    compute_degree
    omega
  have hLowerOne : (deltaLowerOne410 delta A B U).natDegree < 3 * u := by
    simp only [deltaLowerOne410]
    compute_degree
    omega
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
  have hTwoCoeff := congrArg
    (fun P : k[X] => P.coeff (a + 3 * b)) hTwo
  rw [deltaCurveTwo410_face, coeff_add, coeff_add, coeff_smul, coeff_smul,
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
  rw [deltaCurveOne410_face, coeff_add, coeff_sub, coeff_smul,
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
      -(8 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) +
        3 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hBle)
    linear_combination hTwoCoeff
  have hFaceOne :
      24 * (A.leadingCoeff * B.leadingCoeff ^ 2) -
        U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hUle)
    linear_combination hOneCoeff
  have hzero : (64 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) = 0 := by
    linear_combination hFaceTwo + 3 * hFaceOne
  exact (mul_ne_zero (by norm_num)
    (mul_ne_zero hAle (pow_ne_zero 2 hBle))) hzero

private theorem deltaFiber_degree_one_impossible_of_degrees_zero
    (delta k2 : k) (A B U : k[X])
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hU : U.natDegree = 0)
    (hDegree : (deltaFiberPrimitive410 delta k2 A B U).natDegree = 1) :
    False := by
  have hle : (deltaFiberPrimitive410 delta k2 A B U).natDegree ≤ 0 := by
    simp only [deltaFiberPrimitive410, deltaTerminalPrimitive410]
    compute_degree
    omega
  omega

private theorem deltaOnly410_zeroA_impossible
    (delta k2raw k2 k1 : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hAzero : A = 0)
    (hTwo : deltaCurveTwo410 delta A B U = C k2)
    (hOne : deltaCurveOne410 delta A B U = C k1)
    (hDegree : (deltaFiberPrimitive410 delta k2raw A B U).natDegree = 1) :
    False := by
  subst A
  by_cases hBzero : B = 0
  · subst B
    have hUdegree : U.natDegree = 0 := by
      have hUeq : -(U ^ 3) = C k1 := by
        simpa [deltaCurveOne410] using hOne
      have hd := congrArg Polynomial.natDegree hUeq
      rw [natDegree_neg, natDegree_pow, natDegree_C] at hd
      omega
    exact deltaFiber_degree_one_impossible_of_degrees_zero
      delta k2raw 0 0 U (by simp) (by simp) hUdegree hDegree
  · by_cases hUzero : U = 0
    · subst U
      simp [deltaFiberPrimitive410, deltaTerminalPrimitive410] at hDegree
    · let b := B.natDegree
      let u := U.natDegree
      have hpositive : 0 < b ∨ 0 < u := by
        by_contra hnone
        push_neg at hnone
        exact deltaFiber_degree_one_impossible_of_degrees_zero
          delta k2raw 0 B U (by simp) (by omega) (by omega) hDegree
      have hc8 : (8 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
      have hsum : (8 * delta : k) • B ^ 2 +
          (3 : k) • (B * U ^ 2) = C k2 := by
        simpa [deltaCurveTwo410] using hTwo
      have hmpos : 0 < max (2 * b) (b + 2 * u) := by omega
      have hbelow : ((8 * delta : k) • B ^ 2 +
          (3 : k) • (B * U ^ 2)).natDegree < max (2 * b) (b + 2 * u) := by
        rw [hsum, natDegree_C]
        exact hmpos
      have htie := twoTerm_degree_eq410 ((8 * delta : k) • B ^ 2)
        ((3 : k) • (B * U ^ 2))
        (by
          intro hz
          exact (pow_ne_zero 2 hBzero)
            ((smul_eq_zero.mp hz).resolve_left hc8))
        (by
          intro hz
          exact (mul_ne_zero hBzero (pow_ne_zero 2 hUzero))
            ((smul_eq_zero.mp hz).resolve_left (by norm_num)))
        (by
          simpa only [natDegree_smul _ hc8,
            natDegree_smul _ (by norm_num : (3 : k) ≠ 0), natDegree_pow,
            natDegree_mul hBzero (pow_ne_zero 2 hUzero)] using hbelow)
      have hdegreePlane : b = 2 * u := by
        have heq : 2 * b = b + 2 * u := by
          simpa only [natDegree_smul _ hc8,
          natDegree_smul _ (by norm_num : (3 : k) ≠ 0), natDegree_pow,
          natDegree_mul hBzero (pow_ne_zero 2 hUzero)] using htie
        omega
      have hu : 0 < u := by
        by_contra hu0
        have hu' : u = 0 := by omega
        have hb' : b = 0 := by omega
        exact deltaFiber_degree_one_impossible_of_degrees_zero
          delta k2raw 0 B U (by simp) (by simpa [b] using hb')
            (by simpa [u] using hu') hDegree
      let R : k[X] := (-(16 * delta) : k) • (B * U) +
        (-(1 : k)) • U ^ 3
      have hOneForm : (-(8 : k)) • B ^ 4 + R = C k1 := by
        simp [deltaCurveOne410] at hOne
        calc
          (-(8 : k)) • B ^ 4 + R =
              -((16 * delta : k) • (B * U)) - (8 : k) • B ^ 4 - U ^ 3 := by
                dsimp only [R]
                module
          _ = C k1 := hOne
      have hRdegree : R.natDegree < 4 * b := by
        dsimp only [R]
        compute_degree
        omega
      exact smul_add_lower_ne_C410 (-(8 : k)) k1 (B ^ 4) R (4 * b)
        (by norm_num) (pow_ne_zero 4 hBzero) (by omega)
        (by rw [natDegree_pow]) hRdegree hOneForm

private theorem deltaOnly410_zeroB_impossible
    (delta k2raw k2 k1 : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hBzero : B = 0)
    (hTwo : deltaCurveTwo410 delta A B U = C k2)
    (hOne : deltaCurveOne410 delta A B U = C k1)
    (hDegree : (deltaFiberPrimitive410 delta k2raw A B U).natDegree = 1) :
    False := by
  subst B
  have hUdegree : U.natDegree = 0 := by
    have hUeq : -(U ^ 3) = C k1 := by
      simpa [deltaCurveOne410] using hOne
    have hd := congrArg Polynomial.natDegree hUeq
    rw [natDegree_neg, natDegree_pow, natDegree_C] at hd
    omega
  by_cases ha : A.natDegree = 0
  · exact deltaFiber_degree_one_impossible_of_degrees_zero
      delta k2raw A 0 U ha (by simp) hUdegree hDegree
  · have hAne : A ≠ 0 := by
      intro hz
      subst A
      exact ha natDegree_zero
    have hapos : 0 < A.natDegree := by omega
    let R : k[X] := (-(4 * delta) : k) • (A * U)
    have hTwoForm : (2 * delta : k) • A ^ 3 + R = C k2 := by
      simp [deltaCurveTwo410] at hTwo
      calc
        (2 * delta : k) • A ^ 3 + R =
            (2 * delta : k) • A ^ 3 - (4 * delta : k) • (A * U) := by
              dsimp only [R]
              module
        _ = C k2 := hTwo
    have hRdegree : R.natDegree < 3 * A.natDegree := by
      dsimp only [R]
      compute_degree
      omega
    exact smul_add_lower_ne_C410 (2 * delta) k2 (A ^ 3) R
      (3 * A.natDegree) (mul_ne_zero (by norm_num) hdelta)
      (pow_ne_zero 3 hAne) (by omega) (by rw [natDegree_pow])
      hRdegree hTwoForm

private theorem deltaOnly410_zeroU_impossible
    (delta k2raw k2 k1 : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hUzero : U = 0)
    (hTwo : deltaCurveTwo410 delta A B U = C k2)
    (hOne : deltaCurveOne410 delta A B U = C k1)
    (hDegree : (deltaFiberPrimitive410 delta k2raw A B U).natDegree = 1) :
    False := by
  subst U
  by_cases hAzero : A = 0
  · subst A
    simp [deltaFiberPrimitive410, deltaTerminalPrimitive410] at hDegree
  · by_cases hBzero : B = 0
    · subst B
      exact deltaOnly410_zeroB_impossible delta k2raw k2 k1 A 0 0 hdelta rfl
        hTwo hOne hDegree
    · let a := A.natDegree
      let b := B.natDegree
      have hpositive : 0 < a ∨ 0 < b := by
        by_contra hnone
        push_neg at hnone
        exact deltaFiber_degree_one_impossible_of_degrees_zero
          delta k2raw A B 0 (by omega) (by omega) (by simp) hDegree
      have hc8d : (8 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
      have hOneForm : (-(8 * delta) : k) • (A ^ 2 * B) +
          (-(8 : k)) • B ^ 4 = C k1 := by
        simp [deltaCurveOne410] at hOne
        calc
          (-(8 * delta) : k) • (A ^ 2 * B) + (-(8 : k)) • B ^ 4 =
              -((8 * delta : k) • (A ^ 2 * B)) - (8 : k) • B ^ 4 := by
                module
          _ = C k1 := hOne
      have hmOnePos : 0 < max (2 * a + b) (4 * b) := by omega
      have hOneBelow : ((-(8 * delta) : k) • (A ^ 2 * B) +
          (-(8 : k)) • B ^ 4).natDegree < max (2 * a + b) (4 * b) := by
        rw [hOneForm, natDegree_C]
        exact hmOnePos
      have hOneTie := twoTerm_degree_eq410
        ((-(8 * delta) : k) • (A ^ 2 * B)) ((-(8 : k)) • B ^ 4)
        (by
          intro hz
          exact (mul_ne_zero (pow_ne_zero 2 hAzero) hBzero)
            ((smul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hc8d)))
        (by
          intro hz
          exact (pow_ne_zero 4 hBzero)
            ((smul_eq_zero.mp hz).resolve_left (by norm_num)))
        (by
          simpa only [natDegree_smul _ (neg_ne_zero.mpr hc8d),
            natDegree_smul _ (by norm_num : (-(8 : k)) ≠ 0),
            natDegree_mul (pow_ne_zero 2 hAzero) hBzero, natDegree_pow]
            using hOneBelow)
      have hOnePlane : 2 * a + b = 4 * b := by
        simpa only [natDegree_smul _ (neg_ne_zero.mpr hc8d),
          natDegree_smul _ (by norm_num : (-(8 : k)) ≠ 0),
          natDegree_mul (pow_ne_zero 2 hAzero) hBzero, natDegree_pow]
          using hOneTie
      have hPrimitiveForm :
          (560 * delta : k) • A ^ 4 + (-(1280 * delta) : k) • (A * B ^ 2) =
            deltaTerminalPrimitive410 delta A B 0 := by
        rw [neg_smul]
        simp [deltaTerminalPrimitive410]
        module
      have hTerminalForm : deltaTerminalPrimitive410 delta A B 0 =
          deltaFiberPrimitive410 delta k2raw A B 0 + k2raw • A := by
        simp only [deltaFiberPrimitive410]
        abel
      have hPrimitiveLe :
          ((560 * delta : k) • A ^ 4 +
            (-(1280 * delta) : k) • (A * B ^ 2)).natDegree ≤ max 1 a := by
        rw [hPrimitiveForm, hTerminalForm]
        compute_degree
        omega
      have hmPrimitivePos : max 1 a < max (4 * a) (a + 2 * b) := by omega
      have hPrimitiveBelow :
          ((560 * delta : k) • A ^ 4 +
            (-(1280 * delta) : k) • (A * B ^ 2)).natDegree <
              max (4 * a) (a + 2 * b) :=
        hPrimitiveLe.trans_lt hmPrimitivePos
      have hc560 : (560 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
      have hc1280 : (1280 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
      have hPrimitiveTie := twoTerm_degree_eq410
        ((560 * delta : k) • A ^ 4)
        ((-(1280 * delta) : k) • (A * B ^ 2))
        (by
          intro hz
          exact (pow_ne_zero 4 hAzero)
            ((smul_eq_zero.mp hz).resolve_left hc560))
        (by
          intro hz
          exact (mul_ne_zero hAzero (pow_ne_zero 2 hBzero))
            ((smul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hc1280)))
        (by
          simpa only [natDegree_smul _ hc560,
            natDegree_smul _ (neg_ne_zero.mpr hc1280), natDegree_pow,
            natDegree_mul hAzero (pow_ne_zero 2 hBzero)]
            using hPrimitiveBelow)
      have hPrimitivePlane : 4 * a = a + 2 * b := by
        simpa only [natDegree_smul _ hc560,
          natDegree_smul _ (neg_ne_zero.mpr hc1280), natDegree_pow,
          natDegree_mul hAzero (pow_ne_zero 2 hBzero)] using hPrimitiveTie
      omega

/-- The exact pure-`delta` constant-fiber system is impossible.  The proof
also covers all three degenerate coordinate cases. -/
theorem deltaOnly410_discriminant_trajectory_impossible
    (delta k2 k1 terminal : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta 0 0 0 A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 delta 0 0 0 A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 delta 0 0 0 A B U = C terminal) : False := by
  obtain ⟨hTwoCurve, hOneCurve, hDerivative, hDegree⟩ :=
    deltaOnly410_discriminant_residual_packet delta k2 k1 terminal A B U
      hdelta hterminal hTwo hOne hTerminal
  by_cases hAzero : A = 0
  · exact deltaOnly410_zeroA_impossible delta k2 (k2 / 160) (k1 / 40)
      A B U hdelta hAzero hTwoCurve hOneCurve hDegree
  · by_cases hBzero : B = 0
    · exact deltaOnly410_zeroB_impossible delta k2 (k2 / 160) (k1 / 40)
        A B U hdelta hBzero hTwoCurve hOneCurve hDegree
    · by_cases hUzero : U = 0
      · exact deltaOnly410_zeroU_impossible delta k2 (k2 / 160) (k1 / 40)
          A B U hdelta hUzero hTwoCurve hOneCurve hDegree
      · have hscale : (160 : k) * (k2 / 160) = k2 := by ring
        have hDegree' :
            (deltaFiberPrimitive410 delta (160 * (k2 / 160)) A B U).natDegree =
              1 := by
          rw [hscale]
          exact hDegree
        exact deltaOnly410_nonzero_polynomials_impossible
          delta (k2 / 160) (k1 / 40) terminal A B U
            A.natDegree B.natDegree U.natDegree hdelta hterminal
            hAzero hBzero hUzero rfl rfl rfl hTwoCurve hOneCurve hDegree'

/-- Original-coordinate closure of the pure `delta` wall. -/
theorem deltaOnly410_original_trajectory_impossible
    (alpha delta epsilon iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 delta 0 0 0 A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 delta 0 0 0 A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 delta epsilon 0 0 A B C0)
      (integratedZPolynomial410 0 alpha 0 0 delta epsilon 0 0 iota A B C0)
      B C0 = C terminal) : False := by
  have hTwoD :
      discriminantInvariantTwoNumerator410 0 0 0 delta 0 0 0 A B
          (A ^ 2 - (4 : k) • C0) = C (2048 * k2) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD :
      discriminantInvariantOneNumerator410 0 0 0 delta 0 0 0 A B
          (A ^ 2 - (4 : k) • C0) = C (2048 * k1) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD :
      lWallTerminalNumerator410 0 0 0 delta 0 0 0 A B
          (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact deltaOnly410_discriminant_trajectory_impossible delta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) hdelta
      (mul_ne_zero (by norm_num) hterminal) hTwoD hOneD hTerminalD

/-- After closing `l`, `beta`, `gamma`, and `delta`, a nonzero terminal row
must carry one of the three final effective loads. -/
theorem deltaWall410_laterEffectiveLoad_residual
    (alpha delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 delta epsilon zeta theta A B C0)
      (integratedZPolynomial410 0 alpha 0 0 delta epsilon zeta eta iota A B C0)
      B C0 = C terminal) :
    zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0 := by
  by_contra hlater
  push_neg at hlater
  obtain ⟨hzeta, heta, htheta⟩ := hlater
  subst zeta
  subst eta
  subst theta
  have hwall := constantIntegral410_effectiveLoadWall
    (k := k) 0 alpha 0 0 delta epsilon 0 0 0 iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  rcases hwall with hl | hbeta | hgamma | hdelta | hzeta | heta | htheta
  · exact hl rfl
  · exact hbeta rfl
  · exact hgamma rfl
  · exact deltaOnly410_original_trajectory_impossible
      alpha delta epsilon iota k2 k1 terminal A B C0 hdelta hterminal
        hTwo hOne hLower
  · exact hzeta rfl
  · exact heta rfl
  · exact htheta rfl


end DeltaWallElimination410

end Max11DegreeRoutes
