import InfinityFirstLoad
import FiniteExactSquareExclusion

noncomputable section
open Polynomial

/-! # Excluding the exact common-cubic square at infinity -/

namespace GCD369CubePolynomialSource

/-- If every exact transverse normal at the constant-core infinity pole
vanishes, polynomial injectivity at infinity makes the normalized sextic a
global cubic square, contradicting its nonzero constant Jacobian. -/
theorem infinity_exactNormals_zero_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (h2 : (S.infinityCommonCoefficientData hsdegree).normal2 = 0)
    (h1 : (S.infinityCommonCoefficientData hsdegree).normal1 = 0)
    (h0 : (S.infinityCommonCoefficientData hsdegree).normal0 = 0) : False := by
  let D := S.infinityCommonCoefficientData hsdegree
  let Sc := D.faber.scale
  have hr2 : Sc.regular2 = D.cubicU ^ 2 := by
    apply sub_eq_zero.mp
    simpa only [D, Sc, GCD369CubeHahnCommonCoefficientData.normal2] using h2
  have hr1 : Sc.regular1 = 2 * D.cubicU * D.cubicV := by
    apply sub_eq_zero.mp
    simpa only [D, Sc, GCD369CubeHahnCommonCoefficientData.normal1] using h1
  have hr0 : Sc.regular0 = D.cubicV ^ 2 := by
    apply sub_eq_zero.mp
    simpa only [D, Sc, GCD369CubeHahnCommonCoefficientData.normal0] using h0
  have hreg2 : 4 * Sc.regular2 = Sc.regular4 ^ 2 := by
    rw [hr2, D.regular4_eq_two_cubicU]
    ring
  have hreg1 : 2 * Sc.regular1 = Sc.regular4 * Sc.regular3 := by
    rw [hr1, D.regular4_eq_two_cubicU, D.regular3_eq_two_cubicV]
    ring
  have hreg0 : 4 * Sc.regular0 = Sc.regular3 ^ 2 := by
    rw [hr0, D.regular3_eq_two_cubicV]
    ring
  have hscaled2 : 4 * Sc.scaled2 = Sc.scaled4 ^ 2 :=
    congrArg Subtype.val hreg2
  have hscaled1 : 2 * Sc.scaled1 = Sc.scaled4 * Sc.scaled3 :=
    congrArg Subtype.val hreg1
  have hscaled0 : 4 * Sc.scaled0 = Sc.scaled3 ^ 2 :=
    congrArg Subtype.val hreg0
  let H := GCD369CubeRatFuncHahnAtInfinity (k := k)
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  have ha0H : Sc.a0 = H (S.normalizedP.coeff 0) := by
    dsimp only [Sc, D]
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    rfl
  have ha1H : Sc.a1 = H (S.normalizedP.coeff 1) := by
    dsimp only [Sc, D]
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    rfl
  have ha2H : Sc.a2 = H (S.normalizedP.coeff 2) := by
    dsimp only [Sc, D]
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    rfl
  have ha3H : Sc.a3 = H (S.normalizedP.coeff 3) := by
    dsimp only [Sc, D]
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    rfl
  have ha4H : Sc.a4 = H (S.normalizedP.coeff 4) := by
    dsimp only [Sc, D]
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    rfl
  have ht : Sc.t ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
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
  let P := S.constantCoreNormalizedPPolynomial
  have hpoly2 : 4 * P.coeff 2 = P.coeff 4 ^ 2 := by
    apply GCD369CubeRatFuncHahnAtInfinity_polynomial_injective
    simp only [map_mul, map_ofNat, map_pow]
    rw [← S.constantCoreNormalizedP_coeff hsdegree 2,
      ← S.constantCoreNormalizedP_coeff hsdegree 4]
    simpa only [H] using hmap2
  have hpoly1 : 2 * P.coeff 1 = P.coeff 4 * P.coeff 3 := by
    apply GCD369CubeRatFuncHahnAtInfinity_polynomial_injective
    simp only [map_mul, map_ofNat]
    rw [← S.constantCoreNormalizedP_coeff hsdegree 1,
      ← S.constantCoreNormalizedP_coeff hsdegree 4,
      ← S.constantCoreNormalizedP_coeff hsdegree 3]
    simpa only [H] using hmap1
  have hpoly0 : 4 * P.coeff 0 = P.coeff 3 ^ 2 := by
    apply GCD369CubeRatFuncHahnAtInfinity_polynomial_injective
    simp only [map_mul, map_ofNat, map_pow]
    rw [← S.constantCoreNormalizedP_coeff hsdegree 0,
      ← S.constantCoreNormalizedP_coeff hsdegree 3]
    simpa only [H] using hmap0
  have hcoeff2 : 4 * S.normalizedP.coeff 2 =
      S.normalizedP.coeff 4 ^ 2 := by
    rw [S.constantCoreNormalizedP_coeff hsdegree 2,
      S.constantCoreNormalizedP_coeff hsdegree 4]
    simpa only [map_mul, map_ofNat, map_pow] using
      congrArg (algebraMap k[X] (RatFunc k)) hpoly2
  have hcoeff1 : 2 * S.normalizedP.coeff 1 =
      S.normalizedP.coeff 4 * S.normalizedP.coeff 3 := by
    rw [S.constantCoreNormalizedP_coeff hsdegree 1,
      S.constantCoreNormalizedP_coeff hsdegree 4,
      S.constantCoreNormalizedP_coeff hsdegree 3]
    simpa only [map_mul, map_ofNat] using
      congrArg (algebraMap k[X] (RatFunc k)) hpoly1
  have hcoeff0 : 4 * S.normalizedP.coeff 0 =
      S.normalizedP.coeff 3 ^ 2 := by
    rw [S.constantCoreNormalizedP_coeff hsdegree 0,
      S.constantCoreNormalizedP_coeff hsdegree 3]
    simpa only [map_mul, map_ofNat, map_pow] using
      congrArg (algebraMap k[X] (RatFunc k)) hpoly0
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
