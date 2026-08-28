import LowScale46Depression
import Mathlib.FieldTheory.RatFunc.Basic

/-! # Integrality and unit-product closure for the aligned `(4,6)` branch

The two polynomial boundary values on the final aligned component give a
monic quartic for `q`; on the line component they give a monic octic for `r`.
This module turns those identities into exact `RatFunc` integrality statements
and records the square and nonsquare unit-product contradictions used in the
reviewed closure.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section BoundaryIntegrality

variable {k : Type*} [Field k]

/-- The monic quartic over `k[x]` supplied by the nonlinear aligned boundary
component. -/
def alignedBoundaryQuarticOver46 (P E : k[X]) (theta : k) : (k[X])[X] :=
  X ^ 4 + (-C (6 * P) * X ^ 2 + C (8 * E) * X -
    C (3 * P ^ 2 + C ((3 / 2 : k) * theta)))

theorem alignedBoundaryQuarticOver46_monic (P E : k[X]) (theta : k) :
    (alignedBoundaryQuarticOver46 P E theta).Monic := by
  apply monic_X_pow_add
  compute_degree
  norm_num

/-- A rational function satisfying the aligned monic quartic is a polynomial.
This is the integral-closure step after the two boundary equations have been
eliminated. -/
theorem ratFunc_isPolynomial_of_alignedBoundaryQuartic46
    [CharZero k]
    (q : RatFunc k) (P E : k[X]) (theta : k)
    (hq : q ^ 4 - 6 * algebraMap k[X] (RatFunc k) P * q ^ 2 +
        8 * algebraMap k[X] (RatFunc k) E * q -
        3 * (algebraMap k[X] (RatFunc k) P) ^ 2 -
        (3 / 2 : RatFunc k) * algebraMap k (RatFunc k) theta = 0) :
    ∃ Q : k[X], algebraMap k[X] (RatFunc k) Q = q := by
  apply IsIntegrallyClosed.algebraMap_eq_of_integral
  refine ⟨alignedBoundaryQuarticOver46 P E theta,
    alignedBoundaryQuarticOver46_monic P E theta, ?_⟩
  have h32 : algebraMap k (RatFunc k) (3 / 2 : k) =
      (3 / 2 : RatFunc k) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have hC32 : RatFunc.C (3 / 2 : k) = (3 / 2 : RatFunc k) := by
    calc
      RatFunc.C (3 / 2 : k) = algebraMap k (RatFunc k) (3 / 2 : k) := by
        rw [RatFunc.algebraMap_eq_C]
      _ = _ := h32
  have hCtheta : RatFunc.C theta = algebraMap k (RatFunc k) theta := by
    rw [RatFunc.algebraMap_eq_C]
  simp only [alignedBoundaryQuarticOver46, eval₂_add, eval₂_sub, eval₂_neg,
    eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_add, map_mul, map_pow,
    map_ofNat, eval₂_ofNat, RatFunc.algebraMap_C]
  rw [hC32, hCtheta]
  convert hq using 1
  all_goals ring

/-- The monic octic over `k[x]` supplied by the aligned `A=0` line. -/
def alignedBoundaryOcticOver46 (P E : k[X]) : (k[X])[X] :=
  X ^ 8 + (-C (6 * P) * X ^ 4 + C (8 * E) * X ^ 2 - C (3 * P ^ 2))

theorem alignedBoundaryOcticOver46_monic (P E : k[X]) :
    (alignedBoundaryOcticOver46 P E).Monic := by
  apply monic_X_pow_add
  compute_degree
  norm_num

/-- A rational function satisfying the aligned line's monic octic is a
polynomial. -/
theorem ratFunc_isPolynomial_of_alignedBoundaryOctic46
    [CharZero k]
    (r : RatFunc k) (P E : k[X])
    (hr : r ^ 8 - 6 * algebraMap k[X] (RatFunc k) P * r ^ 4 +
        8 * algebraMap k[X] (RatFunc k) E * r ^ 2 -
        3 * (algebraMap k[X] (RatFunc k) P) ^ 2 = 0) :
    ∃ R : k[X], algebraMap k[X] (RatFunc k) R = r := by
  apply IsIntegrallyClosed.algebraMap_eq_of_integral
  refine ⟨alignedBoundaryOcticOver46 P E,
    alignedBoundaryOcticOver46_monic P E, ?_⟩
  simp only [alignedBoundaryOcticOver46, eval₂_add, eval₂_sub, eval₂_neg,
    eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_mul, map_pow,
    map_ofNat, eval₂_ofNat]
  convert hr using 1
  all_goals ring

/-- Once `q` is polynomial, the second aligned boundary explicitly makes
`K=B²` polynomial. -/
theorem ratFunc_K_isPolynomial_of_alignedBoundaryE46
    [CharZero k]
    (q K : RatFunc k) (P E Q : k[X])
    (hq : algebraMap k[X] (RatFunc k) Q = q)
    (hE : algebraMap k[X] (RatFunc k) E =
      (-1 / 2 : RatFunc k) * q ^ 3 +
        (3 / 2 : RatFunc k) * algebraMap k[X] (RatFunc k) P * q +
        (3 / 8 : RatFunc k) * K) :
    ∃ K0 : k[X], algebraMap k[X] (RatFunc k) K0 = K := by
  refine ⟨C (8 / 3 : k) * E + C (4 / 3 : k) * Q ^ 3 -
    C (4 : k) * P * Q, ?_⟩
  simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C, hq]
  have h83 : RatFunc.C (8 / 3 : k) = (8 / 3 : RatFunc k) := by
    calc
      RatFunc.C (8 / 3 : k) = algebraMap k (RatFunc k) (8 / 3 : k) := by
        rw [RatFunc.algebraMap_eq_C]
      _ = algebraMap k (RatFunc k) (8 : k) /
          algebraMap k (RatFunc k) (3 : k) := by rw [map_div₀]
      _ = (8 / 3 : RatFunc k) := by rw [map_ofNat, map_ofNat]
  have h43 : RatFunc.C (4 / 3 : k) = (4 / 3 : RatFunc k) := by
    calc
      RatFunc.C (4 / 3 : k) = algebraMap k (RatFunc k) (4 / 3 : k) := by
        rw [RatFunc.algebraMap_eq_C]
      _ = algebraMap k (RatFunc k) (4 : k) /
          algebraMap k (RatFunc k) (3 : k) := by rw [map_div₀]
      _ = (4 / 3 : RatFunc k) := by rw [map_ofNat, map_ofNat]
  have h4 : RatFunc.C (4 : k) = (4 : RatFunc k) := by
    calc
      RatFunc.C (4 : k) = algebraMap k (RatFunc k) (4 : k) := by
        rw [RatFunc.algebraMap_eq_C]
      _ = (4 : RatFunc k) := by rw [map_ofNat]
  rw [h83, h43, h4]
  linear_combination (8 / 3 : RatFunc k) * hE

/-- A rational square which is polynomial already has a polynomial square
root, by normality of `k[x]`. -/
theorem ratFunc_isPolynomial_of_sq_isPolynomial46
    (B : RatFunc k) (K : k[X])
    (hB : B ^ 2 = algebraMap k[X] (RatFunc k) K) :
    ∃ B0 : k[X], algebraMap k[X] (RatFunc k) B0 = B := by
  apply IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (n := 2)
  · norm_num
  · rw [hB]
    exact isIntegral_algebraMap

/-- The full nonlinear boundary-integrality handoff: the monic quartic makes
`q` polynomial, the second boundary then makes `K` polynomial, and `B²=K`
makes `B` polynomial. -/
theorem alignedBoundaryNonlinear_forces_polynomial46
    [CharZero k]
    (q B K : RatFunc k) (P E : k[X]) (theta : k)
    (hquartic : q ^ 4 - 6 * algebraMap k[X] (RatFunc k) P * q ^ 2 +
        8 * algebraMap k[X] (RatFunc k) E * q -
        3 * (algebraMap k[X] (RatFunc k) P) ^ 2 -
        (3 / 2 : RatFunc k) * algebraMap k (RatFunc k) theta = 0)
    (hE : algebraMap k[X] (RatFunc k) E =
      (-1 / 2 : RatFunc k) * q ^ 3 +
        (3 / 2 : RatFunc k) * algebraMap k[X] (RatFunc k) P * q +
        (3 / 8 : RatFunc k) * K)
    (hB : B ^ 2 = K) :
    ∃ Q K0 B0 : k[X],
      algebraMap k[X] (RatFunc k) Q = q ∧
      algebraMap k[X] (RatFunc k) K0 = K ∧
      algebraMap k[X] (RatFunc k) B0 = B := by
  obtain ⟨Q, hQ⟩ :=
    ratFunc_isPolynomial_of_alignedBoundaryQuartic46 q P E theta hquartic
  obtain ⟨K0, hK0⟩ :=
    ratFunc_K_isPolynomial_of_alignedBoundaryE46 q K P E Q hQ hE
  obtain ⟨B0, hB0⟩ := ratFunc_isPolynomial_of_sq_isPolynomial46 B K0 (by
    rw [hB, hK0])
  exact ⟨Q, K0, B0, hQ, hK0, hB0⟩

/-- Once `r` is polynomial on the aligned `A=0` line, the two original
boundary equations exhibit `B²` as a polynomial. -/
theorem ratFunc_Bsq_isPolynomial_of_alignedLineBoundaries46
    [CharZero k]
    (r B : RatFunc k) (P E R : k[X])
    (hR : algebraMap k[X] (RatFunc k) R = r)
    (hP : algebraMap k[X] (RatFunc k) P = r * B + r ^ 4)
    (hE : algebraMap k[X] (RatFunc k) E =
      r ^ 6 + (3 / 2 : RatFunc k) * r ^ 3 * B +
        (3 / 8 : RatFunc k) * B ^ 2) :
    ∃ K0 : k[X], algebraMap k[X] (RatFunc k) K0 = B ^ 2 := by
  refine ⟨C (8 / 3 : k) * E - C (8 / 3 : k) * R ^ 6 -
    C (4 : k) * R ^ 2 * (P - R ^ 4), ?_⟩
  simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C, hR]
  have h83 : RatFunc.C (8 / 3 : k) = (8 / 3 : RatFunc k) := by
    calc
      RatFunc.C (8 / 3 : k) = algebraMap k (RatFunc k) (8 / 3 : k) := by
        rw [RatFunc.algebraMap_eq_C]
      _ = algebraMap k (RatFunc k) (8 : k) /
          algebraMap k (RatFunc k) (3 : k) := by rw [map_div₀]
      _ = (8 / 3 : RatFunc k) := by rw [map_ofNat, map_ofNat]
  have h4 : RatFunc.C (4 : k) = (4 : RatFunc k) := by
    calc
      RatFunc.C (4 : k) = algebraMap k (RatFunc k) (4 : k) := by
        rw [RatFunc.algebraMap_eq_C]
      _ = (4 : RatFunc k) := by rw [map_ofNat]
  rw [h83, h4, hE, hP]
  ring

/-- The complete aligned `A=0` boundary handoff: the octic makes `r`
polynomial, and then the two boundary equations make `B²`, hence `B`,
polynomial. -/
theorem alignedBoundaryLine_forces_polynomial46
    [CharZero k]
    (r B : RatFunc k) (P E : k[X])
    (hoctic : r ^ 8 - 6 * algebraMap k[X] (RatFunc k) P * r ^ 4 +
        8 * algebraMap k[X] (RatFunc k) E * r ^ 2 -
        3 * (algebraMap k[X] (RatFunc k) P) ^ 2 = 0)
    (hP : algebraMap k[X] (RatFunc k) P = r * B + r ^ 4)
    (hE : algebraMap k[X] (RatFunc k) E =
      r ^ 6 + (3 / 2 : RatFunc k) * r ^ 3 * B +
        (3 / 8 : RatFunc k) * B ^ 2) :
    ∃ R B0 : k[X], algebraMap k[X] (RatFunc k) R = r ∧
      algebraMap k[X] (RatFunc k) B0 = B := by
  obtain ⟨R, hR⟩ :=
    ratFunc_isPolynomial_of_alignedBoundaryOctic46 r P E hoctic
  obtain ⟨K0, hK0⟩ :=
    ratFunc_Bsq_isPolynomial_of_alignedLineBoundaries46 r B P E R hR hP hE
  obtain ⟨B0, hB0⟩ := ratFunc_isPolynomial_of_sq_isPolynomial46 B K0 hK0.symm
  exact ⟨R, B0, hR, hB0⟩

/-- Direct nonlinear-component handoff from the three exact eliminated
boundary identities, without asking a client to restate the quartic. -/
theorem alignedBoundaryNonlinear_from_exactBoundaries_forces_polynomial46
    [CharZero k]
    (q B K w : RatFunc k) (P E : k[X]) (theta : k)
    (hw : w = algebraMap k[X] (RatFunc k) P - q ^ 2)
    (hE : algebraMap k[X] (RatFunc k) E =
      (-1 / 2 : RatFunc k) * q ^ 3 +
        (3 / 2 : RatFunc k) * algebraMap k[X] (RatFunc k) P * q +
        (3 / 8 : RatFunc k) * K)
    (hw2 : w ^ 2 = q * K -
      (1 / 2 : RatFunc k) * algebraMap k (RatFunc k) theta)
    (hB : B ^ 2 = K) :
    ∃ Q K0 B0 : k[X],
      algebraMap k[X] (RatFunc k) Q = q ∧
      algebraMap k[X] (RatFunc k) K0 = K ∧
      algebraMap k[X] (RatFunc k) B0 = B := by
  have hquartic := aligned_boundary_monicQuartic q K w
    (algebraMap k (RatFunc k) theta)
    (algebraMap k[X] (RatFunc k) P)
    (algebraMap k[X] (RatFunc k) E) hw hE hw2
  exact alignedBoundaryNonlinear_forces_polynomial46
    q B K P E theta hquartic hE hB

/-- Direct line-component handoff from its two exact boundary identities,
without asking a client to restate the octic. -/
theorem alignedBoundaryLine_from_exactBoundaries_forces_polynomial46
    [CharZero k]
    (r B : RatFunc k) (P E : k[X])
    (hP : algebraMap k[X] (RatFunc k) P = r * B + r ^ 4)
    (hE : algebraMap k[X] (RatFunc k) E =
      r ^ 6 + (3 / 2 : RatFunc k) * r ^ 3 * B +
        (3 / 8 : RatFunc k) * B ^ 2) :
    ∃ R B0 : k[X], algebraMap k[X] (RatFunc k) R = r ∧
      algebraMap k[X] (RatFunc k) B0 = B := by
  have hoctic := aligned_boundary_A_zero_monicOctic r B
    (algebraMap k[X] (RatFunc k) P)
    (algebraMap k[X] (RatFunc k) E) hP hE
  exact alignedBoundaryLine_forces_polynomial46 r B P E hoctic hP hE

end BoundaryIntegrality

section UnitProducts

variable {k : Type*} [Field k]

/-- On the square aligned branch, the restricted last row cannot be a
nonzero constant once its coefficients are polynomials. -/
theorem square_aligned_unitProduct_impossible46
    (h B : k[X]) (j : k) (hj : j ≠ 0)
    (hlast : C (-3 / 4 : k) * h * B ^ 2 * derivative B = C j) : False := by
  have hjUnit : IsUnit (C j : k[X]) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hj)
  have hprod : IsUnit (C (-3 / 4 : k) * h * B ^ 2 * derivative B) := by
    rw [hlast]
    exact hjUnit
  have hBUnit : IsUnit B := by
    have hparts := (IsUnit.mul_iff.mp hprod).1
    have hparts' := (IsUnit.mul_iff.mp hparts).2
    rw [pow_two] at hparts'
    exact (IsUnit.mul_iff.mp hparts').1
  obtain ⟨c, -, hBc⟩ := Polynomial.isUnit_iff.mp hBUnit
  rw [← hBc] at hlast
  simp at hlast
  have : C j = C (0 : k) := by simpa using hlast.symm
  exact hj (Polynomial.C_injective this)

/-- The nonsquare descent uses `M²=HK`: if the last-row product `M K'` is a
nonzero constant, then `M` is a unit, hence `HK` and then `K` are units, so
`K'=0`, a contradiction.  This includes the otherwise delicate linear-`K`
case. -/
theorem nonsquare_aligned_unitProduct_impossible46
    (H K M : k[X]) (j c : k) (hj : j ≠ 0)
    (hMK : M ^ 2 = H * K)
    (hlast : C c * M * derivative K = C j) : False := by
  have hjUnit : IsUnit (C j : k[X]) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hj)
  have hprod : IsUnit (C c * M * derivative K) := by
    rw [hlast]
    exact hjUnit
  have hMUnit : IsUnit M := by
    exact (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hprod).1).2
  have hHKUnit : IsUnit (H * K) := by
    rw [← hMK]
    exact hMUnit.pow 2
  have hKUnit : IsUnit K := (IsUnit.mul_iff.mp hHKUnit).2
  obtain ⟨a, -, hKa⟩ := Polynomial.isUnit_iff.mp hKUnit
  rw [← hKa] at hlast
  simp at hlast
  have : C j = C (0 : k) := by simpa using hlast.symm
  exact hj (Polynomial.C_injective this)

end UnitProducts

end Max11DegreeRoutes
