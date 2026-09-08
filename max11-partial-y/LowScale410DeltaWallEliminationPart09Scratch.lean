import LowScale410DeltaWallEliminationPart08Scratch

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
set_option maxHeartbeats 64000000 in
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

end DeltaWallElimination410

end Max11DegreeRoutes
