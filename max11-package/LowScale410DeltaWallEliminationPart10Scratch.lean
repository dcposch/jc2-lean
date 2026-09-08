import LowScale410DeltaWallEliminationPart09Scratch

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

open private deltaFiber_degree_one_impossible_of_degrees_zero from LowScale410DeltaWallEliminationPart08Scratch in
set_option maxHeartbeats 64000000 in
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

end DeltaWallElimination410

end Max11DegreeRoutes
