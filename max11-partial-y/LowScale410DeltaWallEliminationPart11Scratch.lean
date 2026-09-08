import LowScale410DeltaWallEliminationPart10Scratch

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

open private twoTerm_degree_eq410 from LowScale410DeltaWallEliminationPart02Scratch in
open private deltaFiber_degree_one_impossible_of_degrees_zero from LowScale410DeltaWallEliminationPart08Scratch in
open private deltaOnly410_zeroB_impossible from LowScale410DeltaWallEliminationPart10Scratch in
set_option maxHeartbeats 64000000 in
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

end DeltaWallElimination410

end Max11DegreeRoutes
