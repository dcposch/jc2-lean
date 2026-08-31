import FiniteCommonSource

/-! # Excluding an exact moving-cubic square

The transverse construction has one degenerate fallback: all three exact
normal coordinates can vanish, so the normalized sextic is literally a
cubic square.  This file rules that fallback out directly from the nonzero
constant Jacobian of the polynomial source.
-/

noncomputable section
open Polynomial

/-- A depressed sextic on the exact common-cubic locus is literally the
square of the corresponding monic cubic. -/
theorem GCD369CubeDepressedSextic_eq_cubic_sq
    {R : Type*} [CommRing R] (u v : R) :
  GCD369CubeDepressedSextic (v ^ 2) (2 * u * v) (u ^ 2) (2 * v) (2 * u) =
      (X ^ 3 + C u * X + C v) ^ 2 := by
  simp only [GCD369CubeDepressedSextic, ← C_mul_X_pow_eq_monomial,
    map_mul, map_pow, map_ofNat, C_1, one_mul]
  ring

/-- The rational-function Jacobian of a square has its square root as a
factor. -/
theorem GCD369CubeRatFuncJacobian_sq
    {k : Type*} [Field k]
    (r q : (RatFunc k)[X]) :
    GCD369CubeRatFuncJacobian (r ^ 2) q =
      2 * r * GCD369CubeRatFuncJacobian r q := by
  simp only [GCD369CubeRatFuncJacobian,
    GCD369CubeRatFuncCoefficientDerivative_pow, derivative_pow]
  rw [C_eq_natCast]
  ring

namespace GCD369CubePolynomialSource

/-- A normalized sextic with nonzero constant Jacobian cannot be the square
of a cubic. -/
theorem normalizedP_not_square_of_cubic
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k)
    (r : (RatFunc k)[X]) (hr : r.natDegree = 3)
    (hsquare : S.normalizedP = r ^ 2) : False := by
  have hJ := S.normalized_jacobian
  rw [hsquare, GCD369CubeRatFuncJacobian_sq] at hJ
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  have hjRat : algebraMap k (RatFunc k) S.j ≠ 0 :=
    by
      simpa only [map_zero] using
        (FaithfulSMul.algebraMap_injective k (RatFunc k)).ne S.hj
  have hc : algebraMap k (RatFunc k) S.j / S.sRat ≠ 0 :=
    div_ne_zero hjRat hsRat
  have hC : C (algebraMap k (RatFunc k) S.j / S.sRat) ≠
      (0 : (RatFunc k)[X]) := C_ne_zero.mpr hc
  have hdvd : r ∣ C (algebraMap k (RatFunc k) S.j / S.sRat) := by
    refine ⟨2 * GCD369CubeRatFuncJacobian r S.normalizedQ, ?_⟩
    rw [← hJ]
    ring
  have hdegree := natDegree_le_of_dvd hdvd hC
  rw [hr, natDegree_C] at hdegree
  omega

/-- If every exact transverse normal vanishes at a finite coefficient pole,
the normalized sextic is a forbidden global cubic square. -/
theorem finite_exactNormals_zero_inconsistent
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (h2 : (S.finiteCommonValueData a hpole).normal2 = 0)
    (h1 : (S.finiteCommonValueData a hpole).normal1 = 0)
    (h0 : (S.finiteCommonValueData a hpole).normal0 = 0) : False := by
  let Cc := S.finiteCommonValueData a hpole
  let Sc := Cc.normal.sextic.scale
  have hr2 : Sc.regular2 = Cc.cubicU ^ 2 := by
    apply sub_eq_zero.mp
    simpa only [Cc, Sc, GCD369CubeHahnCommonValueData.normal2] using h2
  have hr1 : Sc.regular1 = 2 * Cc.cubicU * Cc.cubicV := by
    apply sub_eq_zero.mp
    simpa only [Cc, Sc, GCD369CubeHahnCommonValueData.normal1] using h1
  have hr0 : Sc.regular0 = Cc.cubicV ^ 2 := by
    apply sub_eq_zero.mp
    simpa only [Cc, Sc, GCD369CubeHahnCommonValueData.normal0] using h0
  have hreg2 : 4 * Sc.regular2 = Sc.regular4 ^ 2 := by
    rw [hr2, Cc.regular4_eq_two_cubicU]
    ring
  have hreg1 : 2 * Sc.regular1 = Sc.regular4 * Sc.regular3 := by
    rw [hr1, Cc.regular4_eq_two_cubicU, Cc.regular3_eq_two_cubicV]
    ring
  have hreg0 : 4 * Sc.regular0 = Sc.regular3 ^ 2 := by
    rw [hr0, Cc.regular3_eq_two_cubicV]
    ring
  have hscaled2 : 4 * Sc.scaled2 = Sc.scaled4 ^ 2 :=
    congrArg Subtype.val hreg2
  have hscaled1 : 2 * Sc.scaled1 = Sc.scaled4 * Sc.scaled3 :=
    congrArg Subtype.val hreg1
  have hscaled0 : 4 * Sc.scaled0 = Sc.scaled3 ^ 2 :=
    congrArg Subtype.val hreg0
  let H := GCD369CubeRatFuncHahnAt a
  rcases S.finiteSexticValueData_source_fields a hpole with
    ⟨ha0H, ha1H, ha2H, ha3H, ha4H, _⟩
  change Sc.a0 = H (S.normalizedP.coeff 0) at ha0H
  change Sc.a1 = H (S.normalizedP.coeff 1) at ha1H
  change Sc.a2 = H (S.normalizedP.coeff 2) at ha2H
  change Sc.a3 = H (S.normalizedP.coeff 3) at ha3H
  change Sc.a4 = H (S.normalizedP.coeff 4) at ha4H
  have ht : Sc.t ≠ 0 := by
    exact HahnSeries.single_ne_zero one_ne_zero
  have hmap2 : 4 * H (S.normalizedP.coeff 2) =
      H (S.normalizedP.coeff 4) ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 4 ht)
    calc
      Sc.t ^ 4 * (4 * H (S.normalizedP.coeff 2)) =
          4 * (Sc.t ^ 4 * H (S.normalizedP.coeff 2)) := by ring
      _ = 4 * Sc.scaled2 := by
        rw [GCD369CubeHahnPoleScale.scaled2, ha2H]
      _ = Sc.scaled4 ^ 2 := hscaled2
      _ = (Sc.t ^ 2 * H (S.normalizedP.coeff 4)) ^ 2 := by
        rw [GCD369CubeHahnPoleScale.scaled4, ha4H]
      _ = Sc.t ^ 4 * H (S.normalizedP.coeff 4) ^ 2 := by ring
  have hmap1 : 2 * H (S.normalizedP.coeff 1) =
      H (S.normalizedP.coeff 4) * H (S.normalizedP.coeff 3) := by
    apply mul_left_cancel₀ (pow_ne_zero 5 ht)
    calc
      Sc.t ^ 5 * (2 * H (S.normalizedP.coeff 1)) =
          2 * (Sc.t ^ 5 * H (S.normalizedP.coeff 1)) := by ring
      _ = 2 * Sc.scaled1 := by
        rw [GCD369CubeHahnPoleScale.scaled1, ha1H]
      _ = Sc.scaled4 * Sc.scaled3 := hscaled1
      _ = (Sc.t ^ 2 * H (S.normalizedP.coeff 4)) *
          (Sc.t ^ 3 * H (S.normalizedP.coeff 3)) := by
        rw [GCD369CubeHahnPoleScale.scaled4,
          GCD369CubeHahnPoleScale.scaled3, ha4H, ha3H]
      _ = Sc.t ^ 5 *
          (H (S.normalizedP.coeff 4) * H (S.normalizedP.coeff 3)) := by ring
  have hmap0 : 4 * H (S.normalizedP.coeff 0) =
      H (S.normalizedP.coeff 3) ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 ht)
    calc
      Sc.t ^ 6 * (4 * H (S.normalizedP.coeff 0)) =
          4 * (Sc.t ^ 6 * H (S.normalizedP.coeff 0)) := by ring
      _ = 4 * Sc.scaled0 := by
        rw [GCD369CubeHahnPoleScale.scaled0, ha0H]
      _ = Sc.scaled3 ^ 2 := hscaled0
      _ = (Sc.t ^ 3 * H (S.normalizedP.coeff 3)) ^ 2 := by
        rw [GCD369CubeHahnPoleScale.scaled3, ha3H]
      _ = Sc.t ^ 6 * H (S.normalizedP.coeff 3) ^ 2 := by ring
  have hcoeff2 : 4 * S.normalizedP.coeff 2 =
      S.normalizedP.coeff 4 ^ 2 := by
    apply GCD369CubeRatFuncHahnAt_injective a
    simpa only [map_mul, map_pow, map_ofNat] using hmap2
  have hcoeff1 : 2 * S.normalizedP.coeff 1 =
      S.normalizedP.coeff 4 * S.normalizedP.coeff 3 := by
    apply GCD369CubeRatFuncHahnAt_injective a
    simpa only [map_mul, map_ofNat] using hmap1
  have hcoeff0 : 4 * S.normalizedP.coeff 0 =
      S.normalizedP.coeff 3 ^ 2 := by
    apply GCD369CubeRatFuncHahnAt_injective a
    simpa only [map_mul, map_pow, map_ofNat] using hmap0
  let u : RatFunc k := S.normalizedP.coeff 4 / 2
  let v : RatFunc k := S.normalizedP.coeff 3 / 2
  have ha4 : S.normalizedP.coeff 4 = 2 * u := by
    dsimp only [u]
    field_simp
  have ha3 : S.normalizedP.coeff 3 = 2 * v := by
    dsimp only [v]
    field_simp
  have ha2 : S.normalizedP.coeff 2 = u ^ 2 := by
    dsimp only [u]
    field_simp
    calc
      S.normalizedP.coeff 2 * 2 ^ 2 =
          4 * S.normalizedP.coeff 2 := by ring
      _ = S.normalizedP.coeff 4 ^ 2 := hcoeff2
  have ha1 : S.normalizedP.coeff 1 = 2 * u * v := by
    dsimp only [u, v]
    field_simp
    simpa [mul_comm] using hcoeff1
  have ha0 : S.normalizedP.coeff 0 = v ^ 2 := by
    dsimp only [v]
    field_simp
    calc
      S.normalizedP.coeff 0 * 2 ^ 2 =
          4 * S.normalizedP.coeff 0 := by ring
      _ = S.normalizedP.coeff 3 ^ 2 := hcoeff0
  let r : (RatFunc k)[X] := X ^ 3 + C u * X + C v
  have hrle : r.natDegree ≤ 3 := by
    dsimp only [r]
    rw [show C u * X = monomial 1 u by
      simpa using (C_mul_X_pow_eq_monomial (a := u) (n := 1))]
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    have hn1 : 1 ≠ n := by omega
    have hn0 : n ≠ 0 := by omega
    simp [coeff_add, coeff_monomial, coeff_X_pow, coeff_C,
      ne_of_gt hn, hn1, hn0]
  have hrge : 3 ≤ r.natDegree := by
    apply le_natDegree_of_ne_zero
    simp [r]
  have hr : r.natDegree = 3 := le_antisymm hrle hrge
  have hsquare : S.normalizedP = r ^ 2 := by
    rw [S.normalizedP_eq_depressed, ha0, ha1, ha2, ha3, ha4,
      GCD369CubeDepressedSextic_eq_cubic_sq]
  exact S.normalizedP_not_square_of_cubic r hr hsquare

end GCD369CubePolynomialSource

#print axioms GCD369CubeRatFuncJacobian_sq
#print axioms GCD369CubeDepressedSextic_eq_cubic_sq
#print axioms GCD369CubePolynomialSource.normalizedP_not_square_of_cubic
#print axioms GCD369CubePolynomialSource.finite_exactNormals_zero_inconsistent
