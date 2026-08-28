import LowScale46QuadraticSourceBridge
import LowScale46AlignedComponentEndgame

/-! # Closure of the nonsquare aligned `(4,6)` source branch

The quadratic deck involution makes `q = r² + A/2`, `K = B²`, `w = rB`,
and `M = √H B` descend to `k(x)`.  The exact boundary equations make `q`
and `K` polynomial; normality then makes `M` polynomial.  The relation
`M² = HK` feeds the existing nonsquare final-row contradiction.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section QuadraticEndgame

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F46" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticEndgameCharZero46 : CharZero F46 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F46).injective

/-- No nonsquare aligned source package can have a nonzero Jacobian
constant. -/
theorem NonsquareAlignedSourceCurveData46.impossible
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData46 H p q j) (hj : j ≠ 0) : False := by
  let h : F46 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let U : F46 := S.A ^ 2 - 4 * S.C0
  let g : F46 := algebraMap k F46 S.gamma
  let qF : F46 := translatedQ46 S.r S.A
  let KF : F46 := S.B ^ 2
  let wF : F46 := S.r * S.B
  let MF : F46 := h * S.B
  have hroot : h ^ 2 = quadraticCoefficientMap46 H H := by
    exact alignedQuadraticRoot_sq46 H
  have hBne : S.B ≠ 0 := by
    intro hBzero
    have hlast0 := S.lastRow
    rw [hBzero] at hlast0
    simp [eta46, etaA46, etaB46, etaU46] at hlast0
    exact hj ((algebraMap k F46).injective (by simpa using hlast0.symm))
  have hBV : S.B * alignedShiftV46 U g = 0 := by
    have hcurve := (aligned_curveTwo_iff S.A S.B U g 0).mp (by
      simpa only [U, g] using S.curveTwo)
    simpa using hcurve
  have hV : alignedShiftV46 U g = 0 :=
    (mul_eq_zero.mp hBV).resolve_left hBne
  have hqFix : alignedQuadraticDeck46 H qF = qF := by
    simp only [qF, translatedQ46, map_add, map_pow, map_mul, map_div₀,
      map_ofNat, map_one, S.r_odd, S.A_even]
    ring
  have hKFix : alignedQuadraticDeck46 H KF = KF := by
    simp only [KF, map_pow, S.B_odd]
    ring
  have hwFix : alignedQuadraticDeck46 H wF = wF := by
    simp only [wF, map_mul, S.r_odd, S.B_odd]
    ring
  have hMFix : alignedQuadraticDeck46 H MF = MF := by
    simp only [MF, h, map_mul, alignedQuadraticDeck46_root, S.B_odd]
    ring
  obtain ⟨qR, hqDesc⟩ :=
    alignedQuadraticFixedElementDescends46 H qF hqFix
  obtain ⟨KR, hKDesc⟩ :=
    alignedQuadraticFixedElementDescends46 H KF hKFix
  obtain ⟨wR, hwDesc⟩ :=
    alignedQuadraticFixedElementDescends46 H wF hwFix
  obtain ⟨mR, hmDesc⟩ :=
    alignedQuadraticFixedElementDescends46 H MF hMFix
  have hcurve1' := (aligned_curveOne_iff S.A S.B U g
    (algebraMap k F46 S.k1)).mp (by
      simpa only [U, g] using S.curveOne)
  rw [hV] at hcurve1'
  let theta : k := (-4 / 3 : k) *
    (S.k1 + (2 / 3 : k) * S.gamma ^ 2)
  have h43 : algebraMap k F46 (-4 / 3 : k) = (-4 / 3 : F46) := by
    rw [map_div₀, map_neg, map_ofNat, map_ofNat]
  have h23 : algebraMap k F46 (2 / 3 : k) = (2 / 3 : F46) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have htheta : S.A * S.B ^ 2 = algebraMap k F46 theta := by
    have hraw : S.A * S.B ^ 2 = (-4 / 3 : F46) *
        (algebraMap k F46 S.k1 + (2 / 3 : F46) * g ^ 2) := by
      linear_combination (-1 / 8 : F46) * hcurve1'
    simp only [theta, map_mul, map_add, map_pow]
    rw [h43, h23]
    exact hraw
  let D0 : k[X] := p.coeff 0
  let E0 : k[X] := q.coeff 0 - C S.alpha * p.coeff 0 - C S.epsilon
  let P0 : k[X] := D0 + C ((2 / 3 : k) * S.gamma)
  have hcoeffC (c : k) : quadraticCoefficientMap46 H (C c) =
      algebraMap k F46 c := by
    rw [quadraticCoefficientMap46_eq_algebraMap]
    simpa using (IsScalarTower.algebraMap_apply k k[X] F46 c).symm
  have hPmap : quadraticCoefficientMap46 H P0 =
      alignedBoundaryP46 (quadraticCoefficientMap46 H D0) g := by
    simp only [P0, map_add, hcoeffC, alignedBoundaryP46, g, map_mul, h23]
  have hwField := aligned_boundary_w_eq S.r qF S.B U g
    (quadraticCoefficientMap46 H D0) hV (by
      simpa only [qF, U, D0] using S.boundaryD)
  have hEField := aligned_boundary_E_eq S.r qF S.B U g
    (quadraticCoefficientMap46 H D0)
    (quadraticCoefficientMap46 H E0) hV
    (by simpa only [qF, U, D0] using S.boundaryD)
    (by simpa only [qF, U, E0] using S.boundaryE)
  have hwRat : wR = algebraMap k[X] (RatFunc k) P0 - qR ^ 2 := by
    apply (algebraMap (RatFunc k) F46).injective
    simp only [map_sub, map_pow]
    rw [← hwDesc, ← hqDesc]
    change wF = quadraticCoefficientMap46 H P0 - qF ^ 2
    rw [hPmap]
    exact hwField
  have hERat : algebraMap k[X] (RatFunc k) E0 =
      (-1 / 2 : RatFunc k) * qR ^ 3 +
        (3 / 2 : RatFunc k) * algebraMap k[X] (RatFunc k) P0 * qR +
        (3 / 8 : RatFunc k) * KR := by
    apply (algebraMap (RatFunc k) F46).injective
    simp only [map_add, map_mul, map_pow, map_neg, map_div₀, map_ofNat]
    rw [← hqDesc, ← hKDesc]
    change quadraticCoefficientMap46 H E0 =
      (-1 / 2 : F46) * qF ^ 3 +
        (3 / 2 : F46) * quadraticCoefficientMap46 H P0 * qF +
        (3 / 8 : F46) * KF
    rw [hPmap]
    simpa only [KF] using hEField
  have hw2Field : wF ^ 2 = qF * KF -
      (1 / 2 : F46) * algebraMap k F46 theta := by
    have hqDef : qF = S.r ^ 2 + (1 / 2 : F46) * S.A := by
      rfl
    have hsquare := aligned_boundary_w_sq S.r qF S.A S.B hqDef
    rw [htheta] at hsquare
    simpa only [wF, KF] using hsquare
  have hw2Rat : wR ^ 2 = qR * KR -
      (1 / 2 : RatFunc k) * algebraMap k (RatFunc k) theta := by
    apply (algebraMap (RatFunc k) F46).injective
    simp only [map_sub, map_mul, map_pow, map_div₀, map_ofNat]
    rw [← hwDesc, ← hqDesc, ← hKDesc]
    exact hw2Field
  have hquartic := aligned_boundary_monicQuartic qR KR wR
    (algebraMap k (RatFunc k) theta)
    (algebraMap k[X] (RatFunc k) P0)
    (algebraMap k[X] (RatFunc k) E0) hwRat hERat hw2Rat
  obtain ⟨Q0, hQ0⟩ :=
    ratFunc_isPolynomial_of_alignedBoundaryQuartic46
      qR P0 E0 theta hquartic
  obtain ⟨K0, hK0⟩ :=
    ratFunc_K_isPolynomial_of_alignedBoundaryE46
      qR KR P0 E0 Q0 hQ0 hERat
  have hKField : algebraMap k[X] F46 K0 = S.B ^ 2 := by
    change algebraMap (RatFunc k) F46
      (algebraMap k[X] (RatFunc k) K0) = S.B ^ 2
    rw [hK0, ← hKDesc]
  have hmSq : mR ^ 2 =
      algebraMap k[X] (RatFunc k) (H * K0) := by
    apply (algebraMap (RatFunc k) F46).injective
    simp only [map_pow, map_mul]
    rw [← hmDesc]
    change MF ^ 2 = quadraticCoefficientMap46 H H *
      algebraMap k[X] F46 K0
    rw [← hroot, hKField]
    simp only [MF]
    ring
  obtain ⟨M0, hM0⟩ :=
    ratFunc_isPolynomial_of_sq_isPolynomial46 mR (H * K0) hmSq
  have hMField : algebraMap k[X] F46 M0 = h * S.B := by
    change algebraMap (RatFunc k) F46
      (algebraMap k[X] (RatFunc k) M0) = h * S.B
    rw [hM0, ← hmDesc]
  have hMK : M0 ^ 2 = H * K0 := by
    apply alignedQuadraticPolynomialMap_injective46 H
      NonsquarePolynomial46.not_sq
    simp only [map_pow, map_mul]
    rw [hMField, hKField,
      ← quadraticCoefficientMap46_eq_algebraMap H H, ← hroot]
    ring
  have hd : ∀ P : k[X],
      quadraticDerivation46 H (algebraMap k[X] F46 P) =
        algebraMap k[X] F46 P.derivative := by
    intro P
    rw [quadraticDerivation46_apply]
    exact alignedQuadraticDeriv_polynomial46 H
      NonsquarePolynomial46.not_sq P
  have hlast := S.lastRow
  change h * eta46 0 S.A S.B U 0 g 0
      (quadraticDerivation46 H S.A) (quadraticDerivation46 H S.B)
      (quadraticDerivation46 H U) = algebraMap k F46 j at hlast
  rw [eta46_alignedShiftV_zero S.A S.B U g
    (quadraticDerivation46 H S.A) (quadraticDerivation46 H S.B)
    (quadraticDerivation46 H U) hV] at hlast
  exact nonsquare_aligned_descent_lastRow_impossible46
    (quadraticDerivation46 H) hd
    (alignedQuadraticPolynomialMap_injective46 H
      NonsquarePolynomial46.not_sq)
    H K0 M0 h S.B j hj hKField hMField hMK hlast

end QuadraticEndgame

end Max11DegreeRoutes
