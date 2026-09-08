import LowScale46AlignedZeroFinitePoles
import GCD369DivisibleSourceExclusion

/-! # Component closure in the last aligned `(4,6)` stratum

This module joins the exact `k₂ = 0` component split to the monic boundary
eliminants and the polynomial unit-product contradiction.  The square working
field is written as `k(x)`.  Its derivation is kept abstract, with the single
source-honest compatibility condition that it restricts to ordinary
polynomial differentiation on `k[x]`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section DerivativeTransport

variable {k : Type*} [Field k] [CharZero k]

/-- Once `h` and `B` have polynomial representatives, the restricted aligned
last row over `k(x)` is exactly the already-closed polynomial unit product. -/
theorem square_aligned_ratFunc_lastRow_impossible46
    (d : RatFunc k → RatFunc k)
    (hd : ∀ P : k[X],
      d (algebraMap k[X] (RatFunc k) P) =
        algebraMap k[X] (RatFunc k) P.derivative)
    (h0 B0 : k[X]) (B : RatFunc k) (j : k) (hj : j ≠ 0)
    (hB : algebraMap k[X] (RatFunc k) B0 = B)
    (hlast : algebraMap k[X] (RatFunc k) h0 *
        ((-3 / 4 : RatFunc k) * B ^ 2 * d B) = RatFunc.C j) : False := by
  have hdB : d B = algebraMap k[X] (RatFunc k) B0.derivative := by
    rw [← hB]
    exact hd B0
  have hC34 : RatFunc.C (-3 / 4 : k) = (-3 / 4 : RatFunc k) := by
    calc
      RatFunc.C (-3 / 4 : k) =
          algebraMap k (RatFunc k) (-3 / 4 : k) := by
            rw [RatFunc.algebraMap_eq_C]
      _ = _ := by rw [map_div₀, map_neg, map_ofNat, map_ofNat]
  have hpoly : algebraMap k[X] (RatFunc k)
      (C (-3 / 4 : k) * h0 * B0 ^ 2 * B0.derivative) =
      algebraMap k[X] (RatFunc k) (C j) := by
    have hlast' := hlast
    rw [← hB, hd B0] at hlast'
    simp only [map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hC34]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hlast'
  have hpoly' : C (-3 / 4 : k) * h0 * B0 ^ 2 * B0.derivative = C j := by
    exact (FaithfulSMul.algebraMap_injective k[X] (RatFunc k)) hpoly
  exact square_aligned_unitProduct_impossible46 h0 B0 j hj hpoly'

end DerivativeTransport

section SquareComponent

variable {k : Type*} [Field k] [CharZero k]

/-- Full closure of the square-working-field part of the final aligned
component.  The hypotheses are the literal two coefficient-curve rows, the
two polynomial boundary rows, and the nonzero constant last row. -/
theorem alignedZeroSquareComponent_impossible46
    (d : RatFunc k → RatFunc k)
    (hd : ∀ P : k[X],
      d (algebraMap k[X] (RatFunc k) P) =
        algebraMap k[X] (RatFunc k) P.derivative)
    (h0 D0 E0 : k[X]) (r A B U : RatFunc k)
    (gamma k1 j : k) (hj : j ≠ 0)
    (hcurve2 : coefficientCurveTwo46 0 A B U 0
        (algebraMap k (RatFunc k) gamma) 0 = 0)
    (hcurve1 : coefficientCurveOne46 0 A B U 0
        (algebraMap k (RatFunc k) gamma) 0 =
          algebraMap k (RatFunc k) k1)
    (hD : boundaryD46 r (translatedQ46 r A) B U =
      algebraMap k[X] (RatFunc k) D0)
    (hE : boundaryE46 0 r (translatedQ46 r A) B U 0
        (algebraMap k (RatFunc k) gamma) 0 =
      algebraMap k[X] (RatFunc k) E0)
    (hlast : algebraMap k[X] (RatFunc k) h0 *
        eta46 0 A B U 0 (algebraMap k (RatFunc k) gamma) 0
          (d A) (d B) (d U) = RatFunc.C j) : False := by
  let g : RatFunc k := algebraMap k (RatFunc k) gamma
  let q : RatFunc k := translatedQ46 r A
  let V : RatFunc k := alignedShiftV46 U g
  let P0 : k[X] := D0 + C ((2 / 3 : k) * gamma)
  have h23 : algebraMap k (RatFunc k) (2 / 3 : k) =
      (2 / 3 : RatFunc k) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h43 : algebraMap k (RatFunc k) (-4 / 3 : k) =
      (-4 / 3 : RatFunc k) := by
    rw [map_div₀, map_neg, map_ofNat, map_ofNat]
  have hC23 : RatFunc.C (2 / 3 : k) = (2 / 3 : RatFunc k) := by
    rw [← RatFunc.algebraMap_eq_C, h23]
  have hBV : B * V = 0 := by
    have hiff := (aligned_curveTwo_iff A B U g 0).mp hcurve2
    norm_num [V] at hiff ⊢
    exact hiff
  rcases mul_eq_zero.mp hBV with hBzero | hV
  · subst B
    have heta : eta46 0 A 0 U 0 g 0 (d A) (d 0) (d U) = 0 := by
      simp [eta46, etaA46, etaB46, etaU46]
    rw [heta, mul_zero] at hlast
    have hCeq : RatFunc.C j = RatFunc.C 0 := by simpa using hlast.symm
    exact hj (RatFunc.C_injective hCeq)
  · have heta : eta46 0 A B U 0 g 0 (d A) (d B) (d U) =
        (-3 / 4 : RatFunc k) * B ^ 2 * d B :=
      eta46_alignedShiftV_zero A B U g (d A) (d B) (d U) hV
    have hlast' : algebraMap k[X] (RatFunc k) h0 *
        ((-3 / 4 : RatFunc k) * B ^ 2 * d B) = RatFunc.C j := by
      change algebraMap k[X] (RatFunc k) h0 *
        eta46 0 A B U 0 g 0 (d A) (d B) (d U) = RatFunc.C j at hlast
      rw [heta] at hlast
      exact hlast
    have hcurve1' := (aligned_curveOne_iff A B U g
      (algebraMap k (RatFunc k) k1)).mp hcurve1
    have htheta : A * B ^ 2 = algebraMap k (RatFunc k)
        ((-4 / 3 : k) * (k1 + (2 / 3 : k) * gamma ^ 2)) := by
      change alignedShiftV46 U g = 0 at hV
      rw [hV] at hcurve1'
      have hraw : A * B ^ 2 = (-4 / 3 : RatFunc k) *
          (algebraMap k (RatFunc k) k1 + (2 / 3 : RatFunc k) * g ^ 2) := by
        linear_combination (-1 / 8 : RatFunc k) * hcurve1'
      rw [map_mul, map_add, map_mul, map_pow, h43, h23]
      exact hraw
    let theta : k := (-4 / 3 : k) * (k1 + (2 / 3 : k) * gamma ^ 2)
    by_cases htheta0 : theta = 0
    · have hAB : A * B ^ 2 = 0 := by simpa only [theta, htheta0, map_zero] using htheta
      rcases mul_eq_zero.mp hAB with hAzero | hBsqzero
      · subst A
        have hq : q = r ^ 2 := by simp [q, translatedQ46]
        have hPmap : algebraMap k[X] (RatFunc k) P0 =
            alignedBoundaryP46 (algebraMap k[X] (RatFunc k) D0) g := by
          simp only [P0, alignedBoundaryP46, map_add, map_mul,
            RatFunc.algebraMap_C, g, hC23, RatFunc.algebraMap_eq_C]
        have hw := aligned_boundary_w_eq r q B U g
          (algebraMap k[X] (RatFunc k) D0) hV (by simpa only [q] using hD)
        have hE' := aligned_boundary_E_eq r q B U g
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0) hV
          (by simpa only [q] using hD) (by simpa only [q] using hE)
        have hPline : algebraMap k[X] (RatFunc k) P0 = r * B + r ^ 4 := by
          calc
            algebraMap k[X] (RatFunc k) P0 =
                alignedBoundaryP46 (algebraMap k[X] (RatFunc k) D0) g := hPmap
            _ = r * B + q ^ 2 := by linear_combination -hw
            _ = r * B + r ^ 4 := by rw [hq]; ring
        have hEline : algebraMap k[X] (RatFunc k) E0 =
            r ^ 6 + (3 / 2 : RatFunc k) * r ^ 3 * B +
              (3 / 8 : RatFunc k) * B ^ 2 := by
          rw [hq, ← hPmap, hPline] at hE'
          linear_combination hE'
        obtain ⟨R0, B0, _hR0, hB0⟩ :=
          alignedBoundaryLine_from_exactBoundaries_forces_polynomial46
            r B P0 E0 hPline hEline
        exact square_aligned_ratFunc_lastRow_impossible46
          d hd h0 B0 B j hj hB0 hlast'
      · have hBzero : B = 0 := by
          by_contra hBne
          exact (pow_ne_zero 2 hBne) hBsqzero
        rw [hBzero] at hlast'
        have hCeq : RatFunc.C j = RatFunc.C 0 := by simpa using hlast'.symm
        exact hj (RatFunc.C_injective hCeq)
    · have hPmap : algebraMap k[X] (RatFunc k) P0 =
          alignedBoundaryP46 (algebraMap k[X] (RatFunc k) D0) g := by
        simp only [P0, alignedBoundaryP46, map_add, map_mul,
          RatFunc.algebraMap_C, g, hC23, RatFunc.algebraMap_eq_C]
      have hw0 := aligned_boundary_w_eq r q B U g
        (algebraMap k[X] (RatFunc k) D0) hV (by simpa only [q] using hD)
      have hE0' := aligned_boundary_E_eq r q B U g
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0) hV
        (by simpa only [q] using hD) (by simpa only [q] using hE)
      let K : RatFunc k := B ^ 2
      let w : RatFunc k := r * B
      have hw : w = algebraMap k[X] (RatFunc k) P0 - q ^ 2 := by
        rw [hPmap]
        simpa only [w] using hw0
      have hEexact : algebraMap k[X] (RatFunc k) E0 =
          (-1 / 2 : RatFunc k) * q ^ 3 +
            (3 / 2 : RatFunc k) * algebraMap k[X] (RatFunc k) P0 * q +
            (3 / 8 : RatFunc k) * K := by
        rw [hPmap]
        simpa only [K] using hE0'
      have hw2 : w ^ 2 = q * K -
          (1 / 2 : RatFunc k) * algebraMap k (RatFunc k) theta := by
        have hqdef : q = r ^ 2 + (1 / 2 : RatFunc k) * A := by
          rfl
        have := aligned_boundary_w_sq r q A B hqdef
        rw [show A * B ^ 2 = algebraMap k (RatFunc k) theta by
          simpa only [theta] using htheta] at this
        simpa only [w, K] using this
      obtain ⟨Q0, K0, B0, _hQ0, _hK0, hB0⟩ :=
        alignedBoundaryNonlinear_from_exactBoundaries_forces_polynomial46
          q B K w P0 E0 theta hw hEexact hw2 rfl
      exact square_aligned_ratFunc_lastRow_impossible46
        d hd h0 B0 B j hj hB0 hlast'

/-- Source-ready specialization to the standard quotient-rule differential
already constructed on `k(x)`. -/
theorem alignedZeroSquareComponent_standardDifferential_impossible46
    (h0 D0 E0 : k[X]) (r A B U : RatFunc k)
    (gamma k1 j : k) (hj : j ≠ 0)
    (hcurve2 : coefficientCurveTwo46 0 A B U 0
        (algebraMap k (RatFunc k) gamma) 0 = 0)
    (hcurve1 : coefficientCurveOne46 0 A B U 0
        (algebraMap k (RatFunc k) gamma) 0 =
          algebraMap k (RatFunc k) k1)
    (hD : boundaryD46 r (translatedQ46 r A) B U =
      algebraMap k[X] (RatFunc k) D0)
    (hE : boundaryE46 0 r (translatedQ46 r A) B U 0
        (algebraMap k (RatFunc k) gamma) 0 =
      algebraMap k[X] (RatFunc k) E0)
    (hlast : algebraMap k[X] (RatFunc k) h0 *
        eta46 0 A B U 0 (algebraMap k (RatFunc k) gamma) 0
          (Differential.deriv A) (Differential.deriv B)
          (Differential.deriv U) = RatFunc.C j) : False := by
  exact alignedZeroSquareComponent_impossible46
    (fun z : RatFunc k => Differential.deriv z)
    GCD369RatFuncDerivative h0 D0 E0 r A B U gamma k1 j hj
    hcurve2 hcurve1 hD hE hlast

end SquareComponent

section NonsquareDescent

variable {k F : Type*} [Field k] [Field F] [CharZero k] [CharZero F]
  [Algebra k F] [Algebra k[X] F] [IsScalarTower k k[X] F]

/-- The final nonsquare descent calculation.  If `K=B²` and `M=hB` have
the prescribed polynomial representatives, differentiating `K=B²` turns
the restricted last row into `(-3/8) M K'`; the polynomial relation
`M²=HK` then gives the nonsquare unit-product contradiction. -/
theorem nonsquare_aligned_descent_lastRow_impossible46
    (d : Derivation k F F)
    (hd : ∀ P : k[X],
      d (algebraMap k[X] F P) = algebraMap k[X] F P.derivative)
    (hι : Function.Injective (algebraMap k[X] F))
    (H0 K0 M0 : k[X]) (h B : F) (j : k) (hj : j ≠ 0)
    (hK : algebraMap k[X] F K0 = B ^ 2)
    (hM : algebraMap k[X] F M0 = h * B)
    (hMK : M0 ^ 2 = H0 * K0)
    (hlast : h * ((-3 / 4 : F) * B ^ 2 * d B) =
      algebraMap k F j) : False := by
  have h38 : algebraMap k F (-3 / 8 : k) = (-3 / 8 : F) := by
    rw [map_div₀, map_neg, map_ofNat, map_ofNat]
  have hC38 : algebraMap k[X] F (C (-3 / 8 : k)) = (-3 / 8 : F) := by
    calc
      algebraMap k[X] F (C (-3 / 8 : k)) =
          algebraMap k F (-3 / 8 : k) := by
            simpa using (IsScalarTower.algebraMap_apply k k[X] F
              (-3 / 8 : k)).symm
      _ = _ := h38
  have hCj : algebraMap k[X] F (C j) = algebraMap k F j := by
    simpa using (IsScalarTower.algebraMap_apply k k[X] F j).symm
  have hrestrict : algebraMap k[X] F (C (-3 / 8 : k) * M0 * K0.derivative) =
      h * ((-3 / 4 : F) * B ^ 2 * d B) := by
    simp only [map_mul, hC38, hM]
    rw [← hd K0, hK]
    simp only [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
    field_simp
    ring
  have hpolyMap : algebraMap k[X] F (C (-3 / 8 : k) * M0 * K0.derivative) =
      algebraMap k[X] F (C j) := by
    exact hrestrict.trans (hlast.trans hCj.symm)
  have hpoly : C (-3 / 8 : k) * M0 * K0.derivative = C j := by
    exact hι hpolyMap
  exact nonsquare_aligned_unitProduct_impossible46
    H0 K0 M0 j (-3 / 8 : k) hj hMK hpoly

end NonsquareDescent

end Max11DegreeRoutes
