import Mathlib.FieldTheory.Laurent
import Mathlib.RingTheory.LaurentSeries
import FaberLaterSource

noncomputable section
open Polynomial
open scoped LaurentSeries RatFunc

/-! # Exact finite-place expansion of rational trajectories

The local pole producer uses the Taylor automorphism of `k(x)` at a finite
point and the canonical embedding of rational functions into Laurent series.
Embedding integer exponents into rational exponents places the result in the
same Hahn-series field used by the boundary certificates.
-/

/-- The order-preserving additive embedding of integer Laurent exponents
into the rational Puiseux exponent group. -/
def GCD369CubeIntToRat : ℤ →+ ℚ := Int.castAddHom ℚ

/-- Laurent series with integer exponents embed multiplicatively into Hahn
series with rational exponents. -/
def GCD369CubeLaurentToHahn
    {k : Type*} [Field k] : LaurentSeries k →+* HahnSeries ℚ k :=
  HahnSeries.embDomainRingHom GCD369CubeIntToRat
    Int.cast_injective (fun _ _ => Int.cast_le)

/-- Exact Hahn expansion of a rational function at the finite place `x=a`.
The Taylor automorphism first replaces `x` by `x+a`, so the local parameter
is `x-a`; the canonical Laurent embedding and exponent extension follow. -/
def GCD369CubeRatFuncHahnAt
    {k : Type*} [Field k] (a : k) : RatFunc k →+* HahnSeries ℚ k :=
  GCD369CubeLaurentToHahn.comp
    ((algebraMap (RatFunc k) (LaurentSeries k)).comp
      (RatFunc.laurent a).toRingHom)

/-- Finite-place Hahn expansion loses no rational-function information. -/
theorem GCD369CubeRatFuncHahnAt_injective
    {k : Type*} [Field k] (a : k) :
    Function.Injective (GCD369CubeRatFuncHahnAt a) := by
  intro x y hxy
  apply RatFunc.laurent_injective a
  apply (algebraMap (RatFunc k) (LaurentSeries k)).injective
  exact GCD369CubeLaurentToHahn.injective hxy

@[simp] theorem GCD369CubeRatFuncHahnAt_C
    {k : Type*} [Field k] (a c : k) :
    GCD369CubeRatFuncHahnAt a (RatFunc.C c) = HahnSeries.C c := by
  simp only [GCD369CubeRatFuncHahnAt, RingHom.comp_apply]
  change GCD369CubeLaurentToHahn
      (algebraMap (RatFunc k) (LaurentSeries k)
        (RatFunc.laurent a (RatFunc.C c))) = HahnSeries.C c
  rw [RatFunc.laurent_C]
  rw [← RatFunc.algebraMap_C,
    ← IsScalarTower.algebraMap_apply k[X] (RatFunc k) (LaurentSeries k)]
  simp [GCD369CubeLaurentToHahn, GCD369CubeIntToRat]

/-- The finite local parameter has exactly one simple Hahn zero. -/
@[simp] theorem GCD369CubeRatFuncHahnAt_X_sub_C
    {k : Type*} [Field k] (a : k) :
    GCD369CubeRatFuncHahnAt a (RatFunc.X - RatFunc.C a) =
      HahnSeries.single 1 1 := by
  simp [GCD369CubeRatFuncHahnAt, GCD369CubeLaurentToHahn,
    GCD369CubeIntToRat, RatFunc.coe_X]

/-- On embedded polynomials, the local expansion is exactly their Taylor
polynomial, now viewed as a rational-exponent Hahn series. -/
theorem GCD369CubeRatFuncHahnAt_algebraMap
    {k : Type*} [Field k] (a : k) (p : k[X]) :
    GCD369CubeRatFuncHahnAt a (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (HahnSeries ℚ k) (taylor a p) := by
  change GCD369CubeLaurentToHahn
      (algebraMap (RatFunc k) (LaurentSeries k)
        (RatFunc.laurent a (algebraMap k[X] (RatFunc k) p))) = _
  rw [RatFunc.laurent_algebraMap,
    ← IsScalarTower.algebraMap_apply k[X] (RatFunc k) (LaurentSeries k)]
  have hhom :
      GCD369CubeLaurentToHahn.comp
          (algebraMap k[X] (LaurentSeries k)) =
        algebraMap k[X] (HahnSeries ℚ k) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [GCD369CubeLaurentToHahn, GCD369CubeIntToRat]
    · simp [GCD369CubeLaurentToHahn, GCD369CubeIntToRat]
  exact RingHom.congr_fun hhom (taylor a p)

/-- Embedded polynomials have no negative local exponents. -/
theorem GCD369CubeHahn_algebraMap_orderTop_nonneg
    {k : Type*} [Field k] (p : k[X]) :
    (↑(0 : ℚ) : WithTop ℚ) ≤
      (algebraMap k[X] (HahnSeries ℚ k) p).orderTop := by
  rw [Polynomial.algebraMap_hahnSeries_apply,
    HahnSeries.ofPowerSeries_apply, HahnSeries.orderTop_embDomain]
  cases horder : (HahnSeries.toPowerSeries.symm (p : PowerSeries k)).orderTop with
  | top => simp
  | coe n => simp

/-- Hence every original coefficient polynomial is regular in the exact
finite-place expansion. -/
theorem GCD369CubeRatFuncHahnAt_algebraMap_orderTop_nonneg
    {k : Type*} [Field k] (a : k) (p : k[X]) :
    (↑(0 : ℚ) : WithTop ℚ) ≤
      (GCD369CubeRatFuncHahnAt a
        (algebraMap k[X] (RatFunc k) p)).orderTop := by
  rw [GCD369CubeRatFuncHahnAt_algebraMap]
  exact GCD369CubeHahn_algebraMap_orderTop_nonneg (taylor a p)

/-- Consequently every scalar monomial at `a` has its literal local Hahn
monomial expansion. -/
theorem GCD369CubeRatFuncHahnAt_monomial
    {k : Type*} [Field k] (a c : k) (m : ℕ) :
    GCD369CubeRatFuncHahnAt a
        (RatFunc.C c * (RatFunc.X - RatFunc.C a) ^ m) =
      HahnSeries.single (m : ℚ) c := by
  rw [map_mul, map_pow, GCD369CubeRatFuncHahnAt_C,
    GCD369CubeRatFuncHahnAt_X_sub_C, HahnSeries.single_pow,
    HahnSeries.C_apply, HahnSeries.single_mul_single]
  simp

/-- Polynomial monomials use the same exact local expansion after the
canonical embedding `k[x] → k(x)`. -/
theorem GCD369CubeRatFuncHahnAt_polynomial_monomial
    {k : Type*} [Field k] (a c : k) (m : ℕ) :
    GCD369CubeRatFuncHahnAt a
        (algebraMap k[X] (RatFunc k) (C c * (X - C a) ^ m)) =
      HahnSeries.single (m : ℚ) c := by
  simpa only [map_mul, map_pow, map_sub, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X] using GCD369CubeRatFuncHahnAt_monomial a c m

namespace GCD369CubePolynomialSource

/-- Reversing the normalized source change recovers the embedded original
sextic exactly. -/
theorem reconstruct_pRat
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) :
    GCD369CubeSourceTransform S.normalizedP S.sRat S.translation = S.pRat := by
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  have h := GCD369CubeSourceTransformInverse S.pRat S.sRat⁻¹
    (-(S.sRat⁻¹ * S.translation)) (inv_ne_zero hsRat)
  simpa [normalizedP, inv_inv, hsRat] using h

/-- The same inverse normalization recovers the embedded original nonic. -/
theorem reconstruct_qRat
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) :
    GCD369CubeSourceTransform S.normalizedQ S.sRat S.translation = S.qRat := by
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  have h := GCD369CubeSourceTransformInverse S.qRat S.sRat⁻¹
    (-(S.sRat⁻¹ * S.translation)) (inv_ne_zero hsRat)
  simpa [normalizedQ, inv_inv, hsRat] using h

/-- The normalized sextic value at the recovered translation is literally
the original constant source row. -/
theorem normalizedP_eval_translation
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) :
    S.normalizedP.eval S.translation =
      algebraMap k[X] (RatFunc k) (S.p.coeff 0) := by
  have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) S.reconstruct_pRat
  rw [GCD369CubeSourceTransformValue, S.pRat_coeff] at h
  exact h

/-- The normalized nonic value at the same translation is the original
constant source row as well. -/
theorem normalizedQ_eval_translation
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) :
    S.normalizedQ.eval S.translation =
      algebraMap k[X] (RatFunc k) (S.q.coeff 0) := by
  have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) S.reconstruct_qRat
  rw [GCD369CubeSourceTransformValue, S.qRat_coeff] at h
  exact h

/-- At every finite place, original polynomiality makes the reconstructed
sextic value row regular. -/
theorem hahnAt_normalizedP_eval_translation_orderTop_nonneg
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (a : k) :
    (↑(0 : ℚ) : WithTop ℚ) ≤
      (GCD369CubeRatFuncHahnAt a
        (S.normalizedP.eval S.translation)).orderTop := by
  rw [S.normalizedP_eval_translation]
  exact GCD369CubeRatFuncHahnAt_algebraMap_orderTop_nonneg a (S.p.coeff 0)

/-- The reconstructed nonic value row is regular at the same finite place. -/
theorem hahnAt_normalizedQ_eval_translation_orderTop_nonneg
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (a : k) :
    (↑(0 : ℚ) : WithTop ℚ) ≤
      (GCD369CubeRatFuncHahnAt a
        (S.normalizedQ.eval S.translation)).orderTop := by
  rw [S.normalizedQ_eval_translation]
  exact GCD369CubeRatFuncHahnAt_algebraMap_orderTop_nonneg a (S.q.coeff 0)

/-- On the nonconstant primitive branch, the classified cube-root polynomial
has its exact one-place Hahn expansion. -/
theorem hahnAt_sRat_of_monomial
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (a : k) (m : ℕ)
    (hsform : S.s = C S.s.leadingCoeff * (X - C a) ^ m) :
    GCD369CubeRatFuncHahnAt a S.sRat =
      HahnSeries.single (m : ℚ) S.s.leadingCoeff := by
  calc
    GCD369CubeRatFuncHahnAt a S.sRat =
        GCD369CubeRatFuncHahnAt a
          (algebraMap k[X] (RatFunc k)
            (C S.s.leadingCoeff * (X - C a) ^ m)) := by
      change GCD369CubeRatFuncHahnAt a
          (algebraMap k[X] (RatFunc k) S.s) = _
      exact congrArg (GCD369CubeRatFuncHahnAt a)
        (congrArg (algebraMap k[X] (RatFunc k)) hsform)
    _ = HahnSeries.single (m : ℚ) S.s.leadingCoeff :=
      GCD369CubeRatFuncHahnAt_polynomial_monomial a S.s.leadingCoeff m

/-- The inverse source scale therefore has the corresponding unique pole
and reciprocal leading coefficient. -/
theorem hahnAt_sRat_inv_of_monomial
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (a : k) (m : ℕ)
    (hsform : S.s = C S.s.leadingCoeff * (X - C a) ^ m) :
    GCD369CubeRatFuncHahnAt a S.sRat⁻¹ =
      HahnSeries.single (-(m : ℚ)) S.s.leadingCoeff⁻¹ := by
  rw [map_inv₀, S.hahnAt_sRat_of_monomial a m hsform,
    HahnSeries.inv_single]

end GCD369CubePolynomialSource

#print axioms GCD369CubeRatFuncHahnAt_injective
#print axioms GCD369CubeRatFuncHahnAt_X_sub_C
#print axioms GCD369CubeRatFuncHahnAt_algebraMap
#print axioms GCD369CubeRatFuncHahnAt_algebraMap_orderTop_nonneg
#print axioms GCD369CubeRatFuncHahnAt_monomial
#print axioms GCD369CubeRatFuncHahnAt_polynomial_monomial
#print axioms GCD369CubePolynomialSource.hahnAt_sRat_of_monomial
#print axioms GCD369CubePolynomialSource.hahnAt_sRat_inv_of_monomial
#print axioms GCD369CubePolynomialSource.reconstruct_pRat
#print axioms GCD369CubePolynomialSource.reconstruct_qRat
#print axioms GCD369CubePolynomialSource.normalizedP_eval_translation
#print axioms GCD369CubePolynomialSource.normalizedQ_eval_translation
#print axioms
  GCD369CubePolynomialSource.hahnAt_normalizedP_eval_translation_orderTop_nonneg
#print axioms
  GCD369CubePolynomialSource.hahnAt_normalizedQ_eval_translation_orderTop_nonneg
