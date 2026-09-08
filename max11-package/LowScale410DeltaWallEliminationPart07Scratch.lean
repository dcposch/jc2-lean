import LowScale410DeltaWallEliminationPart06Scratch

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

open private fiveDegreeTie410 from LowScale410DeltaWallEliminationPart00Scratch in
open private fiveTerm_degree_tie410 from LowScale410DeltaWallEliminationPart01Scratch in
open private deltaLowerTwo410 from LowScale410DeltaWallEliminationPart03Scratch in
open private deltaLowerOne410 from LowScale410DeltaWallEliminationPart04Scratch in
open private deltaCurveTwo410_face from LowScale410DeltaWallEliminationPart05Scratch in
open private deltaCurveOne410_face from LowScale410DeltaWallEliminationPart06Scratch in
set_option maxHeartbeats 64000000 in
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
      clear * - hA hB hU hnone
      simp only [deltaFiberPrimitive410, deltaTerminalPrimitive410]
      compute_degree
      omega
    clear * - hDegree hle
    omega
  have hsmul {c : k} {P : k[X]} (hc : c ≠ 0) (hP : P ≠ 0) : c • P ≠ 0 := by
    intro hz
    exact hP ((smul_eq_zero.mp hz).resolve_left hc)
  have hc2 : (2 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc4 : (4 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
  have hc8 : (8 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hdelta
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
    clear * - hpositive
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
  have hPrimitiveForm : deltaTerminalPrimitive410 delta A B U =
      deltaFiberPrimitive410 delta (160 * k2) A B U + (160 * k2) • A := by
    simp only [deltaFiberPrimitive410]
    abel
  have hPrimitiveLe :
      (deltaTerminalPrimitive410 delta A B U).natDegree ≤ max 1 a := by
    rw [hPrimitiveForm]
    clear * - hDegree hA
    compute_degree
    omega
  have hmPrimitivePos : max 1 a < max (4 * a)
      (max (2 * a + u) (max (a + 2 * b) (max (3 * b + u) (2 * u)))) := by
    clear * - hpositive
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
  simp only [fiveDegreeTie410, natDegree_smul _ hc560,
    natDegree_smul _ (neg_ne_zero.mpr hc960),
    natDegree_smul _ (neg_ne_zero.mpr hc1280d),
    natDegree_smul _ (by norm_num : (1280 : k) ≠ 0),
    natDegree_smul _ hc320, natDegree_pow,
    natDegree_mul (pow_ne_zero 2 hAne) hUne,
    natDegree_mul hAne (pow_ne_zero 2 hBne),
    natDegree_mul (pow_ne_zero 3 hBne) hUne, hA, hB, hU] at hTiePrimitive
  have hplane : a + 2 * b = 2 * u := by
    clear * - hTieTwo hTiePrimitive
    omega
  have hab : 7 * a = 8 * b := by
    clear * - hplane hTiePrimitive
    omega
  have hau : 11 * a = 8 * u := by
    clear * - hplane hab
    omega
  have ha : 0 < a := by
    clear * - hpositive hplane hab
    omega
  have hb : 0 < b := by
    clear * - ha hab
    omega
  have hu : 0 < u := by
    clear * - ha hau
    omega
  clear hTieTwo hTiePrimitive
  have hLowerTwo : (deltaLowerTwo410 delta A B U).natDegree < a + 3 * b := by
    clear * - hA hB hU hab hau hb
    simp only [deltaLowerTwo410]
    compute_degree
    omega
  have hLowerOne : (deltaLowerOne410 delta A B U).natDegree < 3 * u := by
    clear * - hA hB hU hab hau hu
    simp only [deltaLowerOne410]
    compute_degree
    omega
  have hAB3deg : (A * B ^ 3).natDegree = a + 3 * b := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow, hA, hB]
  have hBU2deg : (B * U ^ 2).natDegree = a + 3 * b := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hB, hU]
    clear * - hplane
    omega
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 3 * u := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, hA, hB, hU]
    clear * - hplane
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
      clear * - ha
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
      clear * - hu
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

end DeltaWallElimination410

end Max11DegreeRoutes
