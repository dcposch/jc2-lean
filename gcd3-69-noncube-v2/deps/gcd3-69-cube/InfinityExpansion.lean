import LocalExpansion
import FinitePoleSource
import Mathlib.FieldTheory.RatFunc.Valuation

noncomputable section

open Polynomial

/-! # Exact expansion at the rational-function place at infinity

The finite-pole source proof expands a rational function after translating a
finite place to zero.  For the constant-core branch the relevant place is
infinity.  We realize it without a second Laurent-series implementation:
first apply the rational-function involution `x ↦ x⁻¹`, then use the existing
exact expansion at zero.
-/

/-- The affine source transform commutes with coefficient homomorphisms. -/
theorem GCD369CubeSourceTransform_map
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R[X]) (s r : R) (F : R →+* S) :
    (GCD369CubeSourceTransform f s r).map F =
      GCD369CubeSourceTransform (f.map F) (F s) (F r) := by
  simp [GCD369CubeSourceTransform, Polynomial.map_comp]

/-- Polynomial evaluation at the inverse rational-function coordinate. -/
def GCD369CubePolynomialAtInverse
    {k : Type*} [Field k] : k[X] →+* RatFunc k :=
  Polynomial.eval₂RingHom (algebraMap k (RatFunc k)) (RatFunc.X⁻¹)

/-- The inverse rational-function coordinate is transcendental, so
polynomial evaluation there is injective. -/
theorem GCD369CubePolynomialAtInverse_injective
    {k : Type*} [Field k] :
    Function.Injective (GCD369CubePolynomialAtInverse (k := k)) := by
  have ht : Transcendental k ((RatFunc.X : RatFunc k)⁻¹) := by
    simpa only [Transcendental, IsAlgebraic.inv_iff] using
      (RatFunc.transcendental_X (K := k))
  have hi := (transcendental_iff_injective.mp ht)
  change Function.Injective
    (Polynomial.aeval ((RatFunc.X : RatFunc k)⁻¹) : k[X] → RatFunc k)
  exact hi

/-- The rational-function automorphism on generators given by `x ↦ x⁻¹`.
The involutivity facts needed below are proved generatorwise. -/
def GCD369CubeRatFuncInversion
    {k : Type*} [Field k] : RatFunc k →+* RatFunc k :=
  RatFunc.liftRingHom (GCD369CubePolynomialAtInverse (k := k))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      GCD369CubePolynomialAtInverse_injective)

@[simp] theorem GCD369CubeRatFuncInversion_C
    {k : Type*} [Field k] (c : k) :
    GCD369CubeRatFuncInversion (RatFunc.C c) = RatFunc.C c := by
  rw [GCD369CubeRatFuncInversion, RatFunc.liftRingHom_C]
  simp [GCD369CubePolynomialAtInverse, RatFunc.algebraMap_eq_C]

@[simp] theorem GCD369CubeRatFuncInversion_X
    {k : Type*} [Field k] :
    GCD369CubeRatFuncInversion (RatFunc.X : RatFunc k) = RatFunc.X⁻¹ := by
  rw [GCD369CubeRatFuncInversion, RatFunc.liftRingHom_X]
  simp [GCD369CubePolynomialAtInverse]

/-- Exact rational-exponent Hahn expansion at infinity. -/
def GCD369CubeRatFuncHahnAtInfinity
    {k : Type*} [Field k] : RatFunc k →+* HahnSeries ℚ k :=
  (GCD369CubeRatFuncHahnAt (0 : k)).comp
    (GCD369CubeRatFuncInversion (k := k))

@[simp] theorem GCD369CubeRatFuncHahnAtInfinity_C
    {k : Type*} [Field k] (c : k) :
    GCD369CubeRatFuncHahnAtInfinity (RatFunc.C c) = HahnSeries.C c := by
  simp [GCD369CubeRatFuncHahnAtInfinity]

/-- The original affine coordinate has a simple pole at infinity. -/
@[simp] theorem GCD369CubeRatFuncHahnAtInfinity_X
    {k : Type*} [Field k] :
    GCD369CubeRatFuncHahnAtInfinity (RatFunc.X : RatFunc k) =
      HahnSeries.single (-1) 1 := by
  rw [GCD369CubeRatFuncHahnAtInfinity, RingHom.comp_apply,
    GCD369CubeRatFuncInversion_X, map_inv₀]
  have hX :
      GCD369CubeRatFuncHahnAt (0 : k) (RatFunc.X : RatFunc k) =
        HahnSeries.single 1 1 := by
    simpa using GCD369CubeRatFuncHahnAt_X_sub_C (0 : k)
  rw [hX]
  simp

/-- On embedded polynomials, expansion at infinity is ordinary evaluation
at the Hahn monomial `t⁻¹`. -/
theorem GCD369CubeRatFuncHahnAtInfinity_algebraMap
    {k : Type*} [Field k] (p : k[X]) :
    GCD369CubeRatFuncHahnAtInfinity
      (algebraMap k[X] (RatFunc k) p) =
      Polynomial.eval₂ (HahnSeries.C : k →+* HahnSeries ℚ k)
        (HahnSeries.single (-1) 1) p := by
  have hhom :
      (GCD369CubeRatFuncHahnAtInfinity (k := k)).comp
          (algebraMap k[X] (RatFunc k)) =
        Polynomial.eval₂RingHom (HahnSeries.C : k →+* HahnSeries ℚ k)
          (HahnSeries.single (-1) 1) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      rw [RatFunc.algebraMap_C, GCD369CubeRatFuncHahnAtInfinity_C]
    · simp [RatFunc.algebraMap_X]
  exact RingHom.congr_fun hhom p

/-- A scalar polynomial monomial of degree `m` has the literal infinity
Hahn monomial of exponent `-m`. -/
theorem GCD369CubeRatFuncHahnAtInfinity_polynomial_monomial
    {k : Type*} [Field k] (c : k) (m : ℕ) :
    GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) (C c * X ^ m)) =
      HahnSeries.single (-(m : ℚ)) c := by
  simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    GCD369CubeRatFuncHahnAtInfinity_C,
    GCD369CubeRatFuncHahnAtInfinity_X,
    HahnSeries.single_pow, HahnSeries.C_apply,
    HahnSeries.single_mul_single]
  simp

/-- The infinity expansion of a polynomial is the finite sum of its
coefficient monomials, with polynomial degree `n` placed at Hahn exponent
`-n`. -/
theorem GCD369CubeRatFuncHahnAtInfinity_polynomial_sum
    {k : Type*} [Field k] (p : k[X]) :
    GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) p) =
      p.sum fun n c => HahnSeries.single (-(n : ℚ)) c := by
  rw [GCD369CubeRatFuncHahnAtInfinity_algebraMap,
    Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [HahnSeries.C_apply, HahnSeries.single_pow,
    HahnSeries.single_mul_single]
  simp

/-- The coefficient at the lowest infinity exponent of a nonzero polynomial
is its leading coefficient. -/
theorem GCD369CubeRatFuncHahnAtInfinity_coeff_neg_natDegree
    {k : Type*} [Field k] (p : k[X]) (hp : p ≠ 0) :
    (GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) p)).coeff
          (-(p.natDegree : ℚ)) = p.leadingCoeff := by
  rw [GCD369CubeRatFuncHahnAtInfinity_polynomial_sum,
    Polynomial.sum_def, HahnSeries.coeff_sum]
  rw [Finset.sum_eq_single p.natDegree]
  · simp [Polynomial.coeff_natDegree]
  · intro n hn hne
    simp only [HahnSeries.coeff_single]
    split_ifs with h
    · have : n = p.natDegree := by
        have hcast : (p.natDegree : ℚ) = (n : ℚ) := neg_inj.mp h
        have hnat : p.natDegree = n := by exact_mod_cast hcast
        exact hnat.symm
      exact (hne this).elim
    · rfl
  · intro h
    exact (h (Polynomial.natDegree_mem_support_of_nonzero hp)).elim

/-- No polynomial term occurs strictly below the negative of the polynomial's
degree in the infinity expansion. -/
theorem GCD369CubeRatFuncHahnAtInfinity_coeff_eq_zero_of_lt_neg_natDegree
    {k : Type*} [Field k] (p : k[X]) (g : ℚ)
    (hg : g < -(p.natDegree : ℚ)) :
    (GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) p)).coeff g = 0 := by
  rw [GCD369CubeRatFuncHahnAtInfinity_polynomial_sum,
    Polynomial.sum_def, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro n hn
  simp only [HahnSeries.coeff_single]
  split_ifs with h
  · have hnle : n ≤ p.natDegree :=
      Polynomial.le_natDegree_of_mem_supp n hn
    have hnleQ : (n : ℚ) ≤ (p.natDegree : ℚ) := by exact_mod_cast hnle
    have hge : -(p.natDegree : ℚ) ≤ g := by
      rw [h]
      exact neg_le_neg hnleQ
    exact (not_lt_of_ge hge hg).elim
  · rfl

/-- Exact degree/order dictionary at infinity: a nonzero polynomial of degree
`d` has Hahn order `-d`. -/
theorem GCD369CubeRatFuncHahnAtInfinity_order_polynomial
    {k : Type*} [Field k] (p : k[X]) (hp : p ≠ 0) :
    (GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) p)).order =
      -(p.natDegree : ℚ) := by
  let f := GCD369CubeRatFuncHahnAtInfinity
    (algebraMap k[X] (RatFunc k) p)
  have hcoeff : f.coeff (-(p.natDegree : ℚ)) = p.leadingCoeff := by
    exact GCD369CubeRatFuncHahnAtInfinity_coeff_neg_natDegree p hp
  have hcoeff_ne : f.coeff (-(p.natDegree : ℚ)) ≠ 0 := by
    rw [hcoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hf : f ≠ 0 := by
    intro hf
    rw [hf] at hcoeff_ne
    exact hcoeff_ne rfl
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero hcoeff_ne
  · rw [HahnSeries.le_order_iff_forall hf]
    intro g hg
    exact
      GCD369CubeRatFuncHahnAtInfinity_coeff_eq_zero_of_lt_neg_natDegree p g hg

/-- The exact infinity expansion is nonzero on every nonzero embedded
polynomial. -/
theorem GCD369CubeRatFuncHahnAtInfinity_polynomial_ne_zero
    {k : Type*} [Field k] (p : k[X]) (hp : p ≠ 0) :
    GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) p) ≠ 0 := by
  intro hzero
  have hcoeff :=
    GCD369CubeRatFuncHahnAtInfinity_coeff_neg_natDegree p hp
  rw [hzero] at hcoeff
  have hlead : p.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hp
  exact hlead hcoeff.symm

/-- Expansion at infinity is injective on embedded polynomials. -/
theorem GCD369CubeRatFuncHahnAtInfinity_polynomial_injective
    {k : Type*} [Field k] :
    Function.Injective (fun p : k[X] =>
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) p)) := by
  intro p q hpq
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hexp := GCD369CubeRatFuncHahnAtInfinity_polynomial_ne_zero
    (p - q) hsub
  apply hexp
  simpa only [map_sub, hpq, sub_self]

/-- If a weighted infinity expansion is regular and has nonzero residue,
then its polynomial degree is exactly the weight times the pole scale. -/
theorem GCD369CubeRatFuncHahnAtInfinity_natDegree_eq_weight_mul
    {k : Type*} [Field k] (p : ℚ) (w : ℕ) (f : k[X])
    (hregular : 0 ≤ (w : ℚ) * p +
      (GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) f)).order)
    (hresidue :
      (((HahnSeries.single p 1) ^ w *
        GCD369CubeRatFuncHahnAtInfinity
          (algebraMap k[X] (RatFunc k) f)).coeff 0) ≠ 0) :
    (f.natDegree : ℚ) = (w : ℚ) * p := by
  let Hf := GCD369CubeRatFuncHahnAtInfinity
    (algebraMap k[X] (RatFunc k) f)
  change (((HahnSeries.single p 1) ^ w * Hf).coeff 0) ≠ 0 at hresidue
  have hHf : Hf ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hresidue
    exact hresidue rfl
  have hf : f ≠ 0 := by
    intro hzero
    apply hHf
    simp [Hf, hzero]
  have ht : (HahnSeries.single p (1 : k)) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  have hscaled : (HahnSeries.single p (1 : k)) ^ w * Hf ≠ 0 :=
    mul_ne_zero (pow_ne_zero w ht) hHf
  have hscaledOrderLe :
      ((HahnSeries.single p (1 : k)) ^ w * Hf).order ≤ 0 :=
    HahnSeries.order_le_of_coeff_ne_zero hresidue
  have hscaledOrder :
      ((HahnSeries.single p (1 : k)) ^ w * Hf).order = 0 := by
    apply le_antisymm hscaledOrderLe
    rw [HahnSeries.order_mul (pow_ne_zero w ht) hHf,
      HahnSeries.order_pow, HahnSeries.order_single one_ne_zero]
    simpa [Hf, nsmul_eq_mul] using hregular
  rw [HahnSeries.order_mul (pow_ne_zero w ht) hHf,
    HahnSeries.order_pow, HahnSeries.order_single one_ne_zero] at hscaledOrder
  have horder := GCD369CubeRatFuncHahnAtInfinity_order_polynomial f hf
  change Hf.order = -(f.natDegree : ℚ) at horder
  rw [horder] at hscaledOrder
  simp only [nsmul_eq_mul] at hscaledOrder
  linarith

/-- A ground-field rational-function constant is regular at infinity. -/
noncomputable def GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
    {k : Type*} [Field k] (c : k) : GCD369CubeHahnRegular k := by
  refine ⟨GCD369CubeRatFuncHahnAtInfinity
    (algebraMap k (RatFunc k) c), ?_⟩
  rw [RatFunc.algebraMap_eq_C, GCD369CubeRatFuncHahnAtInfinity_C]
  change (↑(0 : ℚ) : WithTop ℚ) ≤ (HahnSeries.single 0 c).orderTop
  exact HahnSeries.orderTop_single_le

/-- A rational function identified with a ground-field constant is regular
at infinity. -/
noncomputable def GCD369CubeHahnRegular.ofRatFuncEqConstantAtInfinity
    {k : Type*} [Field k] (r : RatFunc k) (c : k)
    (h : r = algebraMap k (RatFunc k) c) : GCD369CubeHahnRegular k := by
  refine ⟨GCD369CubeRatFuncHahnAtInfinity r, ?_⟩
  rw [h]
  exact (GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity c).property

set_option maxRecDepth 10000 in
/-- Constant-coefficient extraction commutes with the denominator-cleared
terminal Faber numerator on the regular Hahn local ring. -/
theorem GCD369CubeHahnRegular.constantCoeff_fullN5
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1 :
      GCD369CubeHahnRegular k) :
    constantCoeff (GCD369CubeFaberFullN5
      a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1) =
      GCD369CubeFaberFullN5
        (constantCoeff a0) (constantCoeff a1) (constantCoeff a2)
        (constantCoeff a3) (constantCoeff a4) (constantCoeff d)
        (constantCoeff c7) (constantCoeff c5) (constantCoeff c4)
        (constantCoeff c3) (constantCoeff c2) (constantCoeff c1) := by
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]

set_option maxRecDepth 10000 in
/-- The residue of the terminal Faber invariant of regular Hahn inputs is
the terminal Faber invariant of their residues. -/
theorem GCD369CubeFaberR5_coeff_zero_of_hahnRegular
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1 :
      GCD369CubeHahnRegular k) :
    (GCD369CubeFaberR5
      (a0 : HahnSeries ℚ k) a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1).coeff 0 =
      GCD369CubeFaberR5
        (GCD369CubeHahnRegular.constantCoeff a0)
        (GCD369CubeHahnRegular.constantCoeff a1)
        (GCD369CubeHahnRegular.constantCoeff a2)
        (GCD369CubeHahnRegular.constantCoeff a3)
        (GCD369CubeHahnRegular.constantCoeff a4)
        (GCD369CubeHahnRegular.constantCoeff d)
        (GCD369CubeHahnRegular.constantCoeff c7)
        (GCD369CubeHahnRegular.constantCoeff c5)
        (GCD369CubeHahnRegular.constantCoeff c4)
        (GCD369CubeHahnRegular.constantCoeff c3)
        (GCD369CubeHahnRegular.constantCoeff c2)
        (GCD369CubeHahnRegular.constantCoeff c1) := by
  let N : GCD369CubeHahnRegular k :=
    GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1
  have hdenreg : (↑(0 : ℚ) : WithTop ℚ) ≤
      ((13436928 : HahnSeries ℚ k)⁻¹).orderTop := by
    change (↑(0 : ℚ) : WithTop ℚ) ≤
      ((HahnSeries.C (13436928 : k))⁻¹).orderTop
    rw [← map_inv₀]
    exact HahnSeries.orderTop_single_le
  rw [GCD369CubeFaberR5_eq_fullN5_div,
    GCD369CubeFaberR5_eq_fullN5_div, div_eq_mul_inv]
  change (N.1 * (13436928 : HahnSeries ℚ k)⁻¹).coeff 0 = _
  rw [GCD369CubeHahn_coeff_zero_mul_of_nonneg N.1
    (13436928 : HahnSeries ℚ k)⁻¹ N.2 hdenreg]
  change GCD369CubeHahnRegular.constantCoeff N *
    ((13436928 : HahnSeries ℚ k)⁻¹).coeff 0 = _
  rw [GCD369CubeHahnRegular.constantCoeff_fullN5]
  change GCD369CubeFaberFullN5
      (GCD369CubeHahnRegular.constantCoeff a0)
      (GCD369CubeHahnRegular.constantCoeff a1)
      (GCD369CubeHahnRegular.constantCoeff a2)
      (GCD369CubeHahnRegular.constantCoeff a3)
      (GCD369CubeHahnRegular.constantCoeff a4)
      (GCD369CubeHahnRegular.constantCoeff d)
      (GCD369CubeHahnRegular.constantCoeff c7)
      (GCD369CubeHahnRegular.constantCoeff c5)
      (GCD369CubeHahnRegular.constantCoeff c4)
      (GCD369CubeHahnRegular.constantCoeff c3)
      (GCD369CubeHahnRegular.constantCoeff c2)
      (GCD369CubeHahnRegular.constantCoeff c1) *
        ((HahnSeries.C (13436928 : k))⁻¹).coeff 0 = _
  simp [HahnSeries.C_apply, div_eq_mul_inv]

/-- The constant half, packaged directly in the regular Hahn local ring.
This keeps the infinity common-coordinate packet independent of the
finite-boundary value machinery. -/
noncomputable def GCD369CubeHahnRegular.half
    {k : Type*} [Field k] : GCD369CubeHahnRegular k :=
  ⟨HahnSeries.C ((2 : k)⁻¹), by
    change (↑(0 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.C ((2 : k)⁻¹)).orderTop
    exact HahnSeries.orderTop_single_le⟩

@[simp] theorem GCD369CubeHahnRegular.constantCoeff_half
    {k : Type*} [Field k] :
    GCD369CubeHahnRegular.constantCoeff
      (GCD369CubeHahnRegular.half (k := k)) = (2 : k)⁻¹ := by
  simp [GCD369CubeHahnRegular.half,
    GCD369CubeHahnRegular.constantCoeff, HahnSeries.C_apply]

/-- The common-cubic coefficient jet at a pole, stripped of the finite-place
boundary values that are irrelevant at infinity. -/
structure GCD369CubeHahnCommonCoefficientData
    (k : Type*) [Field k] [CharZero k] where
  faber : GCD369CubeHahnFaberPoleData k
  u : k
  v : k
  hprojective : u ≠ 0 ∨ v ≠ 0
  ha4 : faber.scale.leading4 = 2 * u
  ha3 : faber.scale.leading3 = 2 * v
  ha2 : faber.scale.leading2 = u ^ 2
  ha1 : faber.scale.leading1 = 2 * u * v
  ha0 : faber.scale.leading0 = v ^ 2

namespace GCD369CubeHahnCommonCoefficientData

/-- Moving common-cubic coordinates read from the top two scaled
coefficients. -/
noncomputable def cubicU
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    GCD369CubeHahnRegular k :=
  GCD369CubeHahnRegular.half * D.faber.scale.regular4

noncomputable def cubicV
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    GCD369CubeHahnRegular k :=
  GCD369CubeHahnRegular.half * D.faber.scale.regular3

@[simp] theorem constantCoeff_cubicU
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    GCD369CubeHahnRegular.constantCoeff D.cubicU = D.u := by
  simp only [cubicU, map_mul,
    GCD369CubeHahnRegular.constantCoeff_half]
  change (2 : k)⁻¹ * D.faber.scale.leading4 = D.u
  rw [D.ha4]
  field_simp

@[simp] theorem constantCoeff_cubicV
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    GCD369CubeHahnRegular.constantCoeff D.cubicV = D.v := by
  simp only [cubicV, map_mul,
    GCD369CubeHahnRegular.constantCoeff_half]
  change (2 : k)⁻¹ * D.faber.scale.leading3 = D.v
  rw [D.ha3]
  field_simp

/-- Exact coordinates transverse to the moving common-cubic square. -/
noncomputable def normal2
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    GCD369CubeHahnRegular k :=
  D.faber.scale.regular2 - D.cubicU ^ 2

noncomputable def normal1
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    GCD369CubeHahnRegular k :=
  D.faber.scale.regular1 - 2 * D.cubicU * D.cubicV

noncomputable def normal0
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    GCD369CubeHahnRegular k :=
  D.faber.scale.regular0 - D.cubicV ^ 2

@[simp] theorem constantCoeff_normal2
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    GCD369CubeHahnRegular.constantCoeff D.normal2 = 0 := by
  simp only [normal2, map_sub, map_pow, constantCoeff_cubicU]
  change D.faber.scale.leading2 - D.u ^ 2 = 0
  rw [D.ha2]
  ring

@[simp] theorem constantCoeff_normal1
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    GCD369CubeHahnRegular.constantCoeff D.normal1 = 0 := by
  simp only [normal1, map_sub, map_mul, map_ofNat,
    constantCoeff_cubicU, constantCoeff_cubicV]
  change D.faber.scale.leading1 - 2 * D.u * D.v = 0
  rw [D.ha1]
  ring

@[simp] theorem constantCoeff_normal0
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    GCD369CubeHahnRegular.constantCoeff D.normal0 = 0 := by
  simp only [normal0, map_sub, map_pow, constantCoeff_cubicV]
  change D.faber.scale.leading0 - D.v ^ 2 = 0
  rw [D.ha0]
  ring

/-- A nonnegative monomial in the regular local ring. -/
def monomial
    {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 ≤ delta) :
    GCD369CubeHahnRegular k :=
  ⟨HahnSeries.single delta 1, by
    change (↑(0 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.single delta (1 : k)).orderTop
    rw [HahnSeries.orderTop_single one_ne_zero]
    exact_mod_cast hdelta⟩

/-- Divide a regular series by a monomial whose exponent does not exceed
its order. -/
def shift
    {k : Type*} [Field k]
    (x : GCD369CubeHahnRegular k) (delta : ℚ)
    (hdelta : (↑delta : WithTop ℚ) ≤ x.1.orderTop) :
    GCD369CubeHahnRegular k :=
  ⟨HahnSeries.single (-delta) 1 * x.1, by
    change (↑(0 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.single (-delta) (1 : k) * x.1).orderTop
    rw [HahnSeries.orderTop_mul,
      HahnSeries.orderTop_single one_ne_zero]
    have h := add_le_add_left hdelta (↑(-delta) : WithTop ℚ)
    simpa [add_comm] using h⟩

theorem monomial_mul_shift
    {k : Type*} [Field k]
    (x : GCD369CubeHahnRegular k) (delta : ℚ) (hdelta0 : 0 ≤ delta)
    (hdelta : (↑delta : WithTop ℚ) ≤ x.1.orderTop) :
    monomial delta hdelta0 * shift x delta hdelta = x := by
  apply Subtype.ext
  change HahnSeries.single delta 1 *
      (HahnSeries.single (-delta) 1 * x.1) = x.1
  rw [← mul_assoc, HahnSeries.single_mul_single]
  simp

theorem constantCoeff_shift
    {k : Type*} [Field k]
    (x : GCD369CubeHahnRegular k) (delta : ℚ)
    (hdelta : (↑delta : WithTop ℚ) ≤ x.1.orderTop) :
    GCD369CubeHahnRegular.constantCoeff (shift x delta hdelta) =
      x.1.coeff delta := by
  change (HahnSeries.single (-delta) 1 * x.1).coeff 0 = x.1.coeff delta
  rw [HahnSeries.coeff_single_mul]
  simp

theorem constantCoeff_shift_ne_zero
    {k : Type*} [Field k]
    (x : GCD369CubeHahnRegular k) (delta : ℚ)
    (horder : x.1.orderTop = (↑delta : WithTop ℚ)) :
    GCD369CubeHahnRegular.constantCoeff
        (shift x delta horder.symm.le) ≠ 0 := by
  rw [constantCoeff_shift]
  exact HahnSeries.coeff_orderTop_ne horder

theorem orderTop_pos_of_constantCoeff_zero
    {k : Type*} [Field k] (x : GCD369CubeHahnRegular k)
    (hx : GCD369CubeHahnRegular.constantCoeff x = 0) :
    (↑(0 : ℚ) : WithTop ℚ) < x.1.orderTop := by
  apply lt_of_le_of_ne x.2
  exact (HahnSeries.orderTop_ne_of_coeff_eq_zero hx).symm

/-- The first nonzero transverse common-cubic jet, normalized at its exact
positive Hahn order. -/
structure TransverseScale
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) where
  delta : ℚ
  hdelta : 0 < delta
  Xn : GCD369CubeHahnRegular k
  Yn : GCD369CubeHahnRegular k
  Zn : GCD369CubeHahnRegular k
  hnormal2 : D.normal2 = monomial delta hdelta.le * Xn
  hnormal1 : D.normal1 = monomial delta hdelta.le * Yn
  hnormal0 : D.normal0 = monomial delta hdelta.le * Zn
  hleading :
    GCD369CubeHahnRegular.constantCoeff Xn ≠ 0 ∨
    GCD369CubeHahnRegular.constantCoeff Yn ≠ 0 ∨
    GCD369CubeHahnRegular.constantCoeff Zn ≠ 0

/-- If the sextic is not already an exact moving cubic square, the three
normal coordinates have a canonical first positive order. -/
noncomputable def transverseScale
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (hnonzero : D.normal2 ≠ 0 ∨ D.normal1 ≠ 0 ∨ D.normal0 ≠ 0) :
    D.TransverseScale := by
  let o2 : WithTop ℚ := D.normal2.1.orderTop
  let o1 : WithTop ℚ := D.normal1.1.orderTop
  let o0 : WithTop ℚ := D.normal0.1.orderTop
  let M : WithTop ℚ := min (min o2 o1) o0
  have hM2 : M ≤ o2 := by
    dsimp only [M]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hM1 : M ≤ o1 := by
    dsimp only [M]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hM0 : M ≤ o0 := by
    dsimp only [M]
    exact min_le_right _ _
  have hMne : M ≠ ⊤ := by
    intro hMtop
    rcases hnonzero with h2 | h1 | h0
    · have h2' : D.normal2.1 ≠ 0 := by
        intro hz
        apply h2
        exact Subtype.ext hz
      have ho2 : o2 = ⊤ := top_unique (hMtop ▸ hM2)
      exact (HahnSeries.orderTop_ne_top.mpr h2') ho2
    · have h1' : D.normal1.1 ≠ 0 := by
        intro hz
        apply h1
        exact Subtype.ext hz
      have ho1 : o1 = ⊤ := top_unique (hMtop ▸ hM1)
      exact (HahnSeries.orderTop_ne_top.mpr h1') ho1
    · have h0' : D.normal0.1 ≠ 0 := by
        intro hz
        apply h0
        exact Subtype.ext hz
      have ho0 : o0 = ⊤ := top_unique (hMtop ▸ hM0)
      exact (HahnSeries.orderTop_ne_top.mpr h0') ho0
  let delta : ℚ := M.untop hMne
  have hdelta_coe : (↑delta : WithTop ℚ) = M :=
    WithTop.coe_untop M hMne
  have hp2 : (↑(0 : ℚ) : WithTop ℚ) < o2 :=
    orderTop_pos_of_constantCoeff_zero D.normal2 D.constantCoeff_normal2
  have hp1 : (↑(0 : ℚ) : WithTop ℚ) < o1 :=
    orderTop_pos_of_constantCoeff_zero D.normal1 D.constantCoeff_normal1
  have hp0 : (↑(0 : ℚ) : WithTop ℚ) < o0 :=
    orderTop_pos_of_constantCoeff_zero D.normal0 D.constantCoeff_normal0
  have hMpos : (↑(0 : ℚ) : WithTop ℚ) < M := by
    dsimp only [M]
    exact lt_min (lt_min hp2 hp1) hp0
  have hdelta_top :
      (↑(0 : ℚ) : WithTop ℚ) < (↑delta : WithTop ℚ) := by
    rw [hdelta_coe]
    exact hMpos
  have hdelta : 0 < delta := WithTop.coe_lt_coe.mp hdelta_top
  have hb2 : (↑delta : WithTop ℚ) ≤ D.normal2.1.orderTop := by
    change (↑delta : WithTop ℚ) ≤ o2
    rw [hdelta_coe]
    exact hM2
  have hb1 : (↑delta : WithTop ℚ) ≤ D.normal1.1.orderTop := by
    change (↑delta : WithTop ℚ) ≤ o1
    rw [hdelta_coe]
    exact hM1
  have hb0 : (↑delta : WithTop ℚ) ≤ D.normal0.1.orderTop := by
    change (↑delta : WithTop ℚ) ≤ o0
    rw [hdelta_coe]
    exact hM0
  let Xn := shift D.normal2 delta hb2
  let Yn := shift D.normal1 delta hb1
  let Zn := shift D.normal0 delta hb0
  refine {
    delta := delta
    hdelta := hdelta
    Xn := Xn
    Yn := Yn
    Zn := Zn
    hnormal2 := (monomial_mul_shift
      D.normal2 delta hdelta.le hb2).symm
    hnormal1 := (monomial_mul_shift
      D.normal1 delta hdelta.le hb1).symm
    hnormal0 := (monomial_mul_shift
      D.normal0 delta hdelta.le hb0).symm
    hleading := ?_
  }
  have hchoice : M = o2 ∨ M = o1 ∨ M = o0 := by
    rcases min_choice (min o2 o1) o0 with hout | hout
    · rcases min_choice o2 o1 with hin | hin
      · exact Or.inl (by simpa only [M] using hout.trans hin)
      · exact Or.inr (Or.inl (by simpa only [M] using hout.trans hin))
    · exact Or.inr (Or.inr (by simpa only [M] using hout))
  rcases hchoice with h2 | h1 | h0
  · left
    have horder : D.normal2.1.orderTop = (↑delta : WithTop ℚ) := by
      change o2 = (↑delta : WithTop ℚ)
      exact (hdelta_coe.trans h2).symm
    simpa only [Xn] using
      (constantCoeff_shift_ne_zero D.normal2 delta horder)
  · right; left
    have horder : D.normal1.1.orderTop = (↑delta : WithTop ℚ) := by
      change o1 = (↑delta : WithTop ℚ)
      exact (hdelta_coe.trans h1).symm
    simpa only [Yn] using
      (constantCoeff_shift_ne_zero D.normal1 delta horder)
  · right; right
    have horder : D.normal0.1.orderTop = (↑delta : WithTop ℚ) := by
      change o0 = (↑delta : WithTop ℚ)
      exact (hdelta_coe.trans h0).symm
    simpa only [Zn] using
      (constantCoeff_shift_ne_zero D.normal0 delta horder)

/-- Exact cubic-square versus first-positive-normal dichotomy. -/
theorem normals_zero_or_transverseScale
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    (D.normal2 = 0 ∧ D.normal1 = 0 ∧ D.normal0 = 0) ∨
      Nonempty D.TransverseScale := by
  by_cases h2 : D.normal2 = 0
  · by_cases h1 : D.normal1 = 0
    · by_cases h0 : D.normal0 = 0
      · exact Or.inl ⟨h2, h1, h0⟩
      · exact Or.inr ⟨D.transverseScale (Or.inr (Or.inr h0))⟩
    · exact Or.inr ⟨D.transverseScale (Or.inr (Or.inl h1))⟩
  · exact Or.inr ⟨D.transverseScale (Or.inl h2)⟩

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

/-- The inverse leading scale, represented inside the polynomial coefficient
ring when the cube root is constant. -/
noncomputable def constantCoreScalePolynomial
    {k : Type*} [Field k] (S : GCD369CubePolynomialSource k) : k[X] :=
  C (S.s.coeff 0)⁻¹

/-- Polynomial representative of the depressed translation parameter
`A / 6` in the constant-core branch. -/
noncomputable def constantCoreTranslationPolynomial
    {k : Type*} [Field k] (S : GCD369CubePolynomialSource k) : k[X] :=
  C ((6 : k)⁻¹) *
    (C ((S.s.coeff 0)⁻¹ ^ 5) * S.p.coeff 5)

/-- The literal normalized sextic, retained over `k[x]` rather than merely
over `k(x)`, in the constant-core branch. -/
noncomputable def constantCoreNormalizedPPolynomial
    {k : Type*} [Field k] (S : GCD369CubePolynomialSource k) : k[X][X] :=
  GCD369CubeSourceTransform S.p S.constantCoreScalePolynomial
    (-(S.constantCoreScalePolynomial *
      S.constantCoreTranslationPolynomial))

set_option maxRecDepth 10000 in
/-- Constant-core normalization introduces no rational denominators in the
source variable: the rational normalized sextic is the coefficient embedding
of an actual bivariate polynomial. -/
theorem constantCoreNormalizedPPolynomial_map
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    S.constantCoreNormalizedPPolynomial.map
        (algebraMap k[X] (RatFunc k)) = S.normalizedP := by
  let c := S.s.coeff 0
  have hsform : S.s = C c :=
    Polynomial.eq_C_of_natDegree_eq_zero hsdegree
  have hc : c ≠ 0 := by
    intro hc
    apply S.hs
    rw [hsform, hc, C_0]
  have hscale :
      algebraMap k[X] (RatFunc k) S.constantCoreScalePolynomial =
        S.sRat⁻¹ := by
    change algebraMap k[X] (RatFunc k) (C c⁻¹) =
      (algebraMap k[X] (RatFunc k) S.s)⁻¹
    rw [hsform, RatFunc.algebraMap_C, RatFunc.algebraMap_C]
    exact map_inv₀ (RatFunc.C : k →+* RatFunc k) c
  have htranslation :
      algebraMap k[X] (RatFunc k) S.constantCoreTranslationPolynomial =
        S.translation := by
    change algebraMap k[X] (RatFunc k)
        (C (6 : k)⁻¹ * (C (c⁻¹ ^ 5) * S.p.coeff 5)) =
      (algebraMap k[X] (RatFunc k) (S.p.coeff 5) /
        (algebraMap k[X] (RatFunc k) S.s) ^ 5) / 6
    rw [hsform]
    simp only [map_mul, RatFunc.algebraMap_C, map_pow, map_inv₀,
      map_ofNat, div_eq_mul_inv]
    ring
  calc
    S.constantCoreNormalizedPPolynomial.map
        (algebraMap k[X] (RatFunc k)) =
      GCD369CubeSourceTransform
        (S.p.map (algebraMap k[X] (RatFunc k)))
        (algebraMap k[X] (RatFunc k) S.constantCoreScalePolynomial)
        (algebraMap k[X] (RatFunc k)
          (-(S.constantCoreScalePolynomial *
            S.constantCoreTranslationPolynomial))) := by
      exact GCD369CubeSourceTransform_map _ _ _ _
    _ = S.normalizedP := by
      simp only [map_neg, map_mul, htranslation]
      rw [hscale]
      rfl

/-- Each low rational normalized coefficient is the embedding of its literal
constant-core polynomial coefficient. -/
theorem constantCoreNormalizedP_coeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (n : ℕ) :
    S.normalizedP.coeff n =
      algebraMap k[X] (RatFunc k)
        (S.constantCoreNormalizedPPolynomial.coeff n) := by
  have h := congrArg (fun f : (RatFunc k)[X] => f.coeff n)
    (S.constantCoreNormalizedPPolynomial_map hsdegree)
  simpa using h.symm

/-- The affine terminal primitive forced by a constant core has exact order
`-1` at infinity. -/
theorem hahnAtInfinity_terminalFaberInvariant_order_eq_neg_one
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    (GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order = -1 := by
  let P := S.faberPrimitiveData
  let H := GCD369CubeRatFuncHahnAtInfinity (k := k)
  obtain ⟨hdenDegree, hnumDegree⟩ := S.faberPrimitive_constantCore hsdegree
  have hnumne :
      H (algebraMap k[X] (RatFunc k) P.numerator) ≠ 0 :=
    GCD369CubeRatFuncHahnAtInfinity_polynomial_ne_zero
      P.numerator P.hnumerator
  have hdenne :
      H (algebraMap k[X] (RatFunc k) P.denominator) ≠ 0 :=
    GCD369CubeRatFuncHahnAtInfinity_polynomial_ne_zero
      P.denominator P.hdenominator
  have hnumorder :
      (H (algebraMap k[X] (RatFunc k) P.numerator)).order = -1 := by
    rw [GCD369CubeRatFuncHahnAtInfinity_order_polynomial
      P.numerator P.hnumerator, hnumDegree]
    norm_num
  have hdenorder :
      (H (algebraMap k[X] (RatFunc k) P.denominator)).order = 0 := by
    rw [GCD369CubeRatFuncHahnAtInfinity_order_polynomial
      P.denominator P.hdenominator, hdenDegree]
    norm_num
  have hinvorder :
      (H (algebraMap k[X] (RatFunc k) P.denominator))⁻¹.order =
        -(H (algebraMap k[X] (RatFunc k) P.denominator)).order := by
    have hmul := HahnSeries.order_mul (inv_ne_zero hdenne) hdenne
    rw [inv_mul_cancel₀ hdenne, HahnSeries.order_one] at hmul
    linarith
  have hvalue := congrArg H P.hvalue
  rw [_root_.map_div₀] at hvalue
  simp only [terminalFaberInvariant]
  rw [hvalue, div_eq_mul_inv,
    HahnSeries.order_mul hnumne (inv_ne_zero hdenne), hinvorder,
    hnumorder, hdenorder]
  norm_num

/-- In particular, the affine terminal primitive is polar at infinity. -/
theorem hahnAtInfinity_terminalFaberInvariant_order_neg
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    (GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order < 0 := by
  rw [S.hahnAtInfinity_terminalFaberInvariant_order_eq_neg_one hsdegree]
  norm_num

/-- A terminal pole at infinity forces at least one low normalized sextic
coefficient to be polar there. -/
theorem infinityNormalizedCoeffPole_of_terminalPole
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hterminal :
      (GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order < 0) :
    (GCD369CubeRatFuncHahnAtInfinity
      (S.normalizedP.coeff 0)).order < 0 ∨
    (GCD369CubeRatFuncHahnAtInfinity
      (S.normalizedP.coeff 1)).order < 0 ∨
    (GCD369CubeRatFuncHahnAtInfinity
      (S.normalizedP.coeff 2)).order < 0 ∨
    (GCD369CubeRatFuncHahnAtInfinity
      (S.normalizedP.coeff 3)).order < 0 ∨
    (GCD369CubeRatFuncHahnAtInfinity
      (S.normalizedP.coeff 4)).order < 0 := by
  by_contra hpole
  simp only [not_or] at hpole
  rcases hpole with ⟨h0, h1, h2, h3, h4⟩
  let H := GCD369CubeRatFuncHahnAtInfinity (k := k)
  let N := S.faberNormalForm
  let P := S.faberConstantParameters
  let a0r : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedP.coeff 0),
      HahnSeries.zero_le_orderTop_iff.mpr (le_of_not_gt h0)⟩
  let a1r : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedP.coeff 1),
      HahnSeries.zero_le_orderTop_iff.mpr (le_of_not_gt h1)⟩
  let a2r : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedP.coeff 2),
      HahnSeries.zero_le_orderTop_iff.mpr (le_of_not_gt h2)⟩
  let a3r : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedP.coeff 3),
      HahnSeries.zero_le_orderTop_iff.mpr (le_of_not_gt h3)⟩
  let a4r : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedP.coeff 4),
      HahnSeries.zero_le_orderTop_iff.mpr (le_of_not_gt h4)⟩
  let dr := GCD369CubeHahnRegular.ofRatFuncEqConstantAtInfinity N.d P.d P.hd
  let c7r :=
    GCD369CubeHahnRegular.ofRatFuncEqConstantAtInfinity N.c7 P.c7 P.hc7
  let c5r :=
    GCD369CubeHahnRegular.ofRatFuncEqConstantAtInfinity N.c5 P.c5 P.hc5
  let c4r :=
    GCD369CubeHahnRegular.ofRatFuncEqConstantAtInfinity N.c4 P.c4 P.hc4
  let c3r :=
    GCD369CubeHahnRegular.ofRatFuncEqConstantAtInfinity N.c3 P.c3 P.hc3
  let c2r :=
    GCD369CubeHahnRegular.ofRatFuncEqConstantAtInfinity N.c2 P.c2 P.hc2
  let c1r :=
    GCD369CubeHahnRegular.ofRatFuncEqConstantAtInfinity N.c1 P.c1 P.hc1
  have hregular := GCD369CubeFaberR5_mem_hahnRegular
    a0r a1r a2r a3r a4r dr c7r c5r c4r c3r c2r c1r
  have hmap := GCD369CubeFaberR5_map H
    (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
    (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
    (S.normalizedP.coeff 4)
    N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1
  have hterminalMap :
      H S.terminalFaberInvariant =
        GCD369CubeFaberR5
          (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
          (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
          (H (S.normalizedP.coeff 4))
          (H N.d) (H N.c7) (H N.c5) (H N.c4)
          (H N.c3) (H N.c2) (H N.c1) := by
    simpa only [terminalFaberInvariant] using hmap
  have hregularTerminal :
      (↑(0 : ℚ) : WithTop ℚ) ≤ (H S.terminalFaberInvariant).orderTop := by
    rw [hterminalMap]
    exact hregular
  exact (not_lt_of_ge
    (HahnSeries.zero_le_orderTop_iff.mp hregularTerminal)) hterminal

/-- Every constant-core source therefore has an active normalized
coefficient at infinity. -/
theorem infinityNormalizedCoeffPole_of_constantCore
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    (GCD369CubeRatFuncHahnAtInfinity
      (S.normalizedP.coeff 0)).order < 0 ∨
    (GCD369CubeRatFuncHahnAtInfinity
      (S.normalizedP.coeff 1)).order < 0 ∨
    (GCD369CubeRatFuncHahnAtInfinity
      (S.normalizedP.coeff 2)).order < 0 ∨
    (GCD369CubeRatFuncHahnAtInfinity
      (S.normalizedP.coeff 3)).order < 0 ∨
    (GCD369CubeRatFuncHahnAtInfinity
      (S.normalizedP.coeff 4)).order < 0 :=
  S.infinityNormalizedCoeffPole_of_terminalPole
    (S.hahnAtInfinity_terminalFaberInvariant_order_neg hsdegree)

/-- The infinity pole of a constant-core source produces the same exact
weighted Faber packet as a finite pole. -/
noncomputable def infinityFaberPoleData
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0) :
    GCD369CubeHahnFaberPoleData k := by
  let H := GCD369CubeRatFuncHahnAtInfinity (k := k)
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  let T := GCD369CubeHahnPoleScale.ofSomePole
    (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
    (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
    (H (S.normalizedP.coeff 4)) hpole
  have hr1src :
      GCD369CubeFaberR1
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        (algebraMap k (RatFunc k) P.d)
        (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1) =
      algebraMap k (RatFunc k) R.rho1 := by
    simpa only [← P.hd, ← P.hc7, ← P.hc5, ← P.hc4, ← P.hc3,
      ← P.hc2, ← P.hc1] using R.hrho1
  have hr2src :
      GCD369CubeFaberR2
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        (algebraMap k (RatFunc k) P.d)
        (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1) =
      algebraMap k (RatFunc k) R.rho2 := by
    simpa only [← P.hd, ← P.hc7, ← P.hc5, ← P.hc4, ← P.hc3,
      ← P.hc2, ← P.hc1] using R.hrho2
  have hr3src :
      GCD369CubeFaberR3
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        (algebraMap k (RatFunc k) P.d)
        (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1) =
      algebraMap k (RatFunc k) R.rho3 := by
    simpa only [← P.hd, ← P.hc7, ← P.hc5, ← P.hc4, ← P.hc3,
      ← P.hc2, ← P.hc1] using R.hrho3
  have hr4src :
      GCD369CubeFaberR4
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        (algebraMap k (RatFunc k) P.d)
        (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1) =
      algebraMap k (RatFunc k) R.rho4 := by
    simpa only [← P.hd, ← P.hc7, ← P.hc5, ← P.hc4, ← P.hc3,
      ← P.hc2, ← P.hc1] using R.hrho4
  refine {
    scale := T
    d := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity P.d
    c7 := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity P.c7
    c5 := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity P.c5
    c4 := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity P.c4
    c3 := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity P.c3
    c2 := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity P.c2
    c1 := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity P.c1
    rho1 := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity R.rho1
    rho2 := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity R.rho2
    rho3 := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity R.rho3
    rho4 := GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity R.rho4
    hr1 := ?_
    hr2 := ?_
    hr3 := ?_
    hr4 := ?_
  }
  · change GCD369CubeFaberR1
      (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
      (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
      (H (S.normalizedP.coeff 4))
      (H (algebraMap k (RatFunc k) P.d))
      (H (algebraMap k (RatFunc k) P.c7))
      (H (algebraMap k (RatFunc k) P.c5))
      (H (algebraMap k (RatFunc k) P.c4))
      (H (algebraMap k (RatFunc k) P.c3))
      (H (algebraMap k (RatFunc k) P.c2))
      (H (algebraMap k (RatFunc k) P.c1)) =
      H (algebraMap k (RatFunc k) R.rho1)
    exact (GCD369CubeFaberR_map H _ _ _ _ _ _ _ _ _ _ _ _).1.symm.trans
      (congrArg H hr1src)
  · change GCD369CubeFaberR2
      (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
      (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
      (H (S.normalizedP.coeff 4))
      (H (algebraMap k (RatFunc k) P.d))
      (H (algebraMap k (RatFunc k) P.c7))
      (H (algebraMap k (RatFunc k) P.c5))
      (H (algebraMap k (RatFunc k) P.c4))
      (H (algebraMap k (RatFunc k) P.c3))
      (H (algebraMap k (RatFunc k) P.c2))
      (H (algebraMap k (RatFunc k) P.c1)) =
      H (algebraMap k (RatFunc k) R.rho2)
    exact (GCD369CubeFaberR_map H _ _ _ _ _ _ _ _ _ _ _ _).2.1.symm.trans
      (congrArg H hr2src)
  · change GCD369CubeFaberR3
      (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
      (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
      (H (S.normalizedP.coeff 4))
      (H (algebraMap k (RatFunc k) P.d))
      (H (algebraMap k (RatFunc k) P.c7))
      (H (algebraMap k (RatFunc k) P.c5))
      (H (algebraMap k (RatFunc k) P.c4))
      (H (algebraMap k (RatFunc k) P.c3))
      (H (algebraMap k (RatFunc k) P.c2))
      (H (algebraMap k (RatFunc k) P.c1)) =
      H (algebraMap k (RatFunc k) R.rho3)
    exact (GCD369CubeFaberR_map H _ _ _ _ _ _ _ _ _ _ _ _).2.2.1.symm.trans
      (congrArg H hr3src)
  · change GCD369CubeFaberR4
      (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
      (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
      (H (S.normalizedP.coeff 4))
      (H (algebraMap k (RatFunc k) P.d))
      (H (algebraMap k (RatFunc k) P.c7))
      (H (algebraMap k (RatFunc k) P.c5))
      (H (algebraMap k (RatFunc k) P.c4))
      (H (algebraMap k (RatFunc k) P.c3))
      (H (algebraMap k (RatFunc k) P.c2))
      (H (algebraMap k (RatFunc k) P.c1)) =
      H (algebraMap k (RatFunc k) R.rho4)
    exact (GCD369CubeFaberR_map H _ _ _ _ _ _ _ _ _ _ _ _).2.2.2.symm.trans
      (congrArg H hr4src)

/-- Weight homogeneity identifies the scaled terminal Faber expression with
`t^14` times the actual terminal invariant at infinity. -/
theorem infinityFaberPoleData_scaled_terminal
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0) :
    let F := S.infinityFaberPoleData hpole
    GCD369CubeFaberR5
      F.scale.scaled0 F.scale.scaled1 F.scale.scaled2
      F.scale.scaled3 F.scale.scaled4
      (F.scale.weightedRegular 1 F.d).1
      (F.scale.weightedRegular 2 F.c7).1
      (F.scale.weightedRegular 4 F.c5).1
      (F.scale.weightedRegular 5 F.c4).1
      (F.scale.weightedRegular 6 F.c3).1
      (F.scale.weightedRegular 7 F.c2).1
      (F.scale.weightedRegular 8 F.c1).1 =
      F.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant := by
  letI : CharZero (HahnSeries ℚ k) :=
    charZero_of_injective_algebraMap (R := k)
      (RingHom.injective (algebraMap k (HahnSeries ℚ k)))
  let H := GCD369CubeRatFuncHahnAtInfinity (k := k)
  let F := S.infinityFaberPoleData hpole
  let N := S.faberNormalForm
  let P := S.faberConstantParameters
  have horig :
      GCD369CubeFaberR5
        F.scale.a0 F.scale.a1 F.scale.a2 F.scale.a3 F.scale.a4
        F.d.1 F.c7.1 F.c5.1 F.c4.1 F.c3.1 F.c2.1 F.c1.1 =
      H S.terminalFaberInvariant := by
    change GCD369CubeFaberR5
      (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
      (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
      (H (S.normalizedP.coeff 4))
      (H (algebraMap k (RatFunc k) P.d))
      (H (algebraMap k (RatFunc k) P.c7))
      (H (algebraMap k (RatFunc k) P.c5))
      (H (algebraMap k (RatFunc k) P.c4))
      (H (algebraMap k (RatFunc k) P.c3))
      (H (algebraMap k (RatFunc k) P.c2))
      (H (algebraMap k (RatFunc k) P.c1)) =
      H S.terminalFaberInvariant
    rw [← P.hd, ← P.hc7, ← P.hc5, ← P.hc4, ← P.hc3,
      ← P.hc2, ← P.hc1]
    symm
    simpa only [terminalFaberInvariant] using
      (GCD369CubeFaberR5_map H
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1)
  calc
    GCD369CubeFaberR5
        F.scale.scaled0 F.scale.scaled1 F.scale.scaled2
        F.scale.scaled3 F.scale.scaled4
        (F.scale.weightedRegular 1 F.d).1
        (F.scale.weightedRegular 2 F.c7).1
        (F.scale.weightedRegular 4 F.c5).1
        (F.scale.weightedRegular 5 F.c4).1
        (F.scale.weightedRegular 6 F.c3).1
        (F.scale.weightedRegular 7 F.c2).1
        (F.scale.weightedRegular 8 F.c1).1 =
      F.scale.t ^ 14 * GCD369CubeFaberR5
        F.scale.a0 F.scale.a1 F.scale.a2 F.scale.a3 F.scale.a4
        F.d.1 F.c7.1 F.c5.1 F.c4.1 F.c3.1 F.c2.1 F.c1.1 := by
      simpa only [GCD369CubeHahnPoleScale.scaled0,
        GCD369CubeHahnPoleScale.scaled1,
        GCD369CubeHahnPoleScale.scaled2,
        GCD369CubeHahnPoleScale.scaled3,
        GCD369CubeHahnPoleScale.scaled4,
        GCD369CubeHahnPoleScale.weightedRegular, pow_one] using
          (GCD369CubeFaberInvariantWeights F.scale.t
            F.scale.a0 F.scale.a1 F.scale.a2 F.scale.a3 F.scale.a4
            F.d.1 F.c7.1 F.c5.1 F.c4.1 F.c3.1 F.c2.1 F.c1.1).2.2.2.2
    _ = F.scale.t ^ 14 * H S.terminalFaberInvariant := by rw [horig]

/-- The scaled terminal expression belongs to the regular Hahn local ring. -/
theorem infinityFaberPoleData_scaled_terminal_regular
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0) :
    let F := S.infinityFaberPoleData hpole
    (↑(0 : ℚ) : WithTop ℚ) ≤
      (F.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).orderTop := by
  dsimp only
  let F := S.infinityFaberPoleData hpole
  change (↑(0 : ℚ) : WithTop ℚ) ≤
    (F.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).orderTop
  rw [← S.infinityFaberPoleData_scaled_terminal hpole]
  exact GCD369CubeFaberR5_mem_hahnRegular
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The residue of the scaled terminal expression is the terminal Faber
value at the leading projective point with all high constants zero. -/
theorem infinityFaberPoleData_scaled_terminal_coeff_zero
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0) :
    let F := S.infinityFaberPoleData hpole
    (F.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).coeff 0 =
      GCD369CubeFaberR5
        F.scale.leading0 F.scale.leading1 F.scale.leading2
        F.scale.leading3 F.scale.leading4 0 0 0 0 0 0 0 := by
  dsimp only
  let F := S.infinityFaberPoleData hpole
  change (F.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).coeff 0 =
    GCD369CubeFaberR5
      F.scale.leading0 F.scale.leading1 F.scale.leading2
      F.scale.leading3 F.scale.leading4 0 0 0 0 0 0 0
  rw [← S.infinityFaberPoleData_scaled_terminal hpole]
  change (GCD369CubeFaberR5
      (F.scale.regular0 : HahnSeries ℚ k)
      (F.scale.regular1 : HahnSeries ℚ k)
      (F.scale.regular2 : HahnSeries ℚ k)
      (F.scale.regular3 : HahnSeries ℚ k)
      (F.scale.regular4 : HahnSeries ℚ k)
      (F.scale.weightedRegular 1 F.d).1
      (F.scale.weightedRegular 2 F.c7).1
      (F.scale.weightedRegular 4 F.c5).1
      (F.scale.weightedRegular 5 F.c4).1
      (F.scale.weightedRegular 6 F.c3).1
      (F.scale.weightedRegular 7 F.c2).1
      (F.scale.weightedRegular 8 F.c1).1).coeff 0 =
    GCD369CubeFaberR5
      F.scale.leading0 F.scale.leading1 F.scale.leading2
      F.scale.leading3 F.scale.leading4 0 0 0 0 0 0 0
  rw [GCD369CubeFaberR5_coeff_zero_of_hahnRegular
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)]
  rw [F.scale.weightedRegular_constantCoeff_zero 1 (by norm_num) F.d,
    F.scale.weightedRegular_constantCoeff_zero 2 (by norm_num) F.c7,
    F.scale.weightedRegular_constantCoeff_zero 4 (by norm_num) F.c5,
    F.scale.weightedRegular_constantCoeff_zero 5 (by norm_num) F.c4,
    F.scale.weightedRegular_constantCoeff_zero 6 (by norm_num) F.c3,
    F.scale.weightedRegular_constantCoeff_zero 7 (by norm_num) F.c2,
    F.scale.weightedRegular_constantCoeff_zero 8 (by norm_num) F.c1]
  rfl

/-- The scaled terminal invariant has its exact order before any landing
case is selected.  This is the order-theoretic form of weight-fourteen
homogeneity together with the affine constant-core primitive. -/
theorem infinityFaberPoleData_scaled_terminal_order
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0) :
    let F := S.infinityFaberPoleData hpole
    (F.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
      14 * F.scale.p - 1 := by
  dsimp only
  let F := S.infinityFaberPoleData hpole
  let T := GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant
  have hTorder : T.order = -1 :=
    S.hahnAtInfinity_terminalFaberInvariant_order_eq_neg_one hsdegree
  have hT : T ≠ 0 := by
    intro hzero
    rw [hzero, HahnSeries.order_zero] at hTorder
    norm_num at hTorder
  have ht : F.scale.t ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  rw [HahnSeries.order_mul (pow_ne_zero 14 ht) hT,
    HahnSeries.order_pow, GCD369CubeHahnPoleScale.t,
    HahnSeries.order_single one_ne_zero, hTorder]
  simp only [nsmul_eq_mul]
  ring

/-- Once a branch identifies the first surviving scaled terminal term as a
weight-`w` term, the common scale equation is `(14-w) * p = 1`. -/
theorem infinity_terminal_scale_eq_of_order_eq_weight
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (w : ℕ)
    (hfirst :
      let F := S.infinityFaberPoleData hpole
      (F.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
        w * F.scale.p) :
    (14 - (w : ℚ)) * (S.infinityFaberPoleData hpole).scale.p = 1 := by
  let F := S.infinityFaberPoleData hpole
  change (F.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
    w * F.scale.p at hfirst
  rw [S.infinityFaberPoleData_scaled_terminal_order hsdegree hpole] at hfirst
  linarith

/-- A nonzero residue of the scaled terminal invariant forces the exact
constant-core scale equation `14 * p = 1`. -/
theorem infinity_terminal_scale_eq_of_coeff_ne
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (hcoeff :
      let F := S.infinityFaberPoleData hpole
      (F.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity
          S.terminalFaberInvariant).coeff 0 ≠ 0) :
    14 * (S.infinityFaberPoleData hpole).scale.p = 1 := by
  let F := S.infinityFaberPoleData hpole
  let T := GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant
  change (F.scale.t ^ 14 * T).coeff 0 ≠ 0 at hcoeff
  have hTorder : T.order = -1 := by
    exact S.hahnAtInfinity_terminalFaberInvariant_order_eq_neg_one hsdegree
  have hT : T ≠ 0 := by
    intro hzero
    rw [hzero, HahnSeries.order_zero] at hTorder
    norm_num at hTorder
  have ht : F.scale.t ≠ 0 := by
    exact HahnSeries.single_ne_zero one_ne_zero
  have hscaled : F.scale.t ^ 14 * T ≠ 0 :=
    mul_ne_zero (pow_ne_zero 14 ht) hT
  have hle : (F.scale.t ^ 14 * T).order ≤ 0 :=
    HahnSeries.order_le_of_coeff_ne_zero hcoeff
  have hge : 0 ≤ (F.scale.t ^ 14 * T).order :=
    HahnSeries.zero_le_orderTop_iff.mp
      (S.infinityFaberPoleData_scaled_terminal_regular hpole)
  have horder : (F.scale.t ^ 14 * T).order = 0 :=
    le_antisymm hle hge
  rw [HahnSeries.order_mul (pow_ne_zero 14 ht) hT,
    HahnSeries.order_pow, GCD369CubeHahnPoleScale.t,
    HahnSeries.order_single one_ne_zero, hTorder] at horder
  simp only [nsmul_eq_mul] at horder
  change 14 * F.scale.p = 1
  norm_num at horder
  linarith

/-- The Davenport--Stothers leading component of a constant-core infinity
pole lands immediately in the impossible `2/14` polynomial-degree row. -/
theorem infinityConstantPoleDegreeLanding_of_davenportStothers
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (lambda : k) (hlambda : lambda ≠ 0)
    (ha4 : (S.infinityFaberPoleData hpole).scale.leading4 = 4 * lambda)
    (ha3 : (S.infinityFaberPoleData hpole).scale.leading3 = 0)
    (ha2 : (S.infinityFaberPoleData hpole).scale.leading2 =
      10 * lambda ^ 2)
    (ha1 : (S.infinityFaberPoleData hpole).scale.leading1 = 0)
    (ha0 : (S.infinityFaberPoleData hpole).scale.leading0 =
      6 * lambda ^ 3) :
    GCD369CubeConstantPoleDegreeLanding := by
  let F := S.infinityFaberPoleData hpole
  have hlead4 : F.scale.leading4 ≠ 0 := by
    rw [ha4]
    exact mul_ne_zero (by norm_num) hlambda
  have hcoeffValue :
      (F.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity
          S.terminalFaberInvariant).coeff 0 =
        (27 / 2) * lambda ^ 7 := by
    rw [S.infinityFaberPoleData_scaled_terminal_coeff_zero hpole,
      ha0, ha1, ha2, ha3, ha4]
    exact (GCD369CubeFaberDSValues lambda).2.2.2.2
  have hcoeff :
      (F.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity
          S.terminalFaberInvariant).coeff 0 ≠ 0 := by
    rw [hcoeffValue]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 7 hlambda)
  have hscale : 14 * F.scale.p = 1 :=
    S.infinity_terminal_scale_eq_of_coeff_ne hsdegree hpole hcoeff
  let n := (S.constantCoreNormalizedPPolynomial.coeff 4).natDegree
  let f := S.constantCoreNormalizedPPolynomial.coeff 4
  have ha4source : F.scale.a4 =
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) f) := by
    change GCD369CubeRatFuncHahnAtInfinity (S.normalizedP.coeff 4) = _
    rw [S.constantCoreNormalizedP_coeff hsdegree 4]
  have hdegree : (n : ℚ) = 2 * F.scale.p := by
    change (f.natDegree : ℚ) = 2 * F.scale.p
    apply GCD369CubeRatFuncHahnAtInfinity_natDegree_eq_weight_mul
      F.scale.p 2 f
    · rw [← ha4source]
      simpa using F.scale.ha4
    · change (F.scale.scaled4.coeff 0) ≠ 0 at hlead4
      simpa [GCD369CubeHahnPoleScale.scaled4,
        GCD369CubeHahnPoleScale.t, ha4source] using hlead4
  exact .dsA4 n (by
    rw [hdegree]
    norm_num
    linarith)

/-- The constant-core source reaches the exact nonzero leading Faber source
at infinity. -/
noncomputable def infinityLeadingFaberSource
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0) :
    GCD369CubeLeadingFaberSource k :=
  (S.infinityFaberPoleData hpole).toLeadingFaberSource

/-- A nonzero weight-two leading coordinate at infinity records the literal
degree of the fourth normalized polynomial coefficient. -/
theorem infinityLeading4_natDegree
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (h4 : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0) :
    ((S.constantCoreNormalizedPPolynomial.coeff 4).natDegree : ℚ) =
      2 * (S.infinityFaberPoleData hpole).scale.p := by
  let F := S.infinityFaberPoleData hpole
  let f := S.constantCoreNormalizedPPolynomial.coeff 4
  have ha4 : F.scale.a4 =
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) f) := by
    change GCD369CubeRatFuncHahnAtInfinity (S.normalizedP.coeff 4) = _
    rw [S.constantCoreNormalizedP_coeff hsdegree 4]
  apply GCD369CubeRatFuncHahnAtInfinity_natDegree_eq_weight_mul
    F.scale.p 2 f
  · rw [← ha4]
    simpa using F.scale.ha4
  · change (F.scale.scaled4.coeff 0) ≠ 0 at h4
    simpa [GCD369CubeHahnPoleScale.scaled4,
      GCD369CubeHahnPoleScale.t, ha4] using h4

/-- A nonzero weight-three leading coordinate at infinity records the literal
degree of the third normalized polynomial coefficient. -/
theorem infinityLeading3_natDegree
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (h3 : (S.infinityFaberPoleData hpole).scale.leading3 ≠ 0) :
    ((S.constantCoreNormalizedPPolynomial.coeff 3).natDegree : ℚ) =
      3 * (S.infinityFaberPoleData hpole).scale.p := by
  let F := S.infinityFaberPoleData hpole
  let f := S.constantCoreNormalizedPPolynomial.coeff 3
  have ha3 : F.scale.a3 =
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) f) := by
    change GCD369CubeRatFuncHahnAtInfinity (S.normalizedP.coeff 3) = _
    rw [S.constantCoreNormalizedP_coeff hsdegree 3]
  apply GCD369CubeRatFuncHahnAtInfinity_natDegree_eq_weight_mul
    F.scale.p 3 f
  · rw [← ha3]
    simpa using F.scale.ha3
  · change (F.scale.scaled3.coeff 0) ≠ 0 at h3
    simpa [GCD369CubeHahnPoleScale.scaled3,
      GCD369CubeHahnPoleScale.t, ha3] using h3

/-- Weight one (`d`) plus its certified nonzero `u`-coordinate reaches the
`2/13` constant-pole degree landing. -/
theorem infinityConstantPoleDegreeLanding_of_d_scale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (hscale : 13 * (S.infinityFaberPoleData hpole).scale.p = 1)
    (h4 : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0) :
    GCD369CubeConstantPoleDegreeLanding := by
  let n := (S.constantCoreNormalizedPPolynomial.coeff 4).natDegree
  have hdegree : (n : ℚ) =
      2 * (S.infinityFaberPoleData hpole).scale.p :=
    S.infinityLeading4_natDegree hsdegree hpole h4
  exact .dA4 n (by rw [hdegree]; norm_num; linarith)

/-- Weight two (`c7`) reaches one of its two common-coordinate degree rows. -/
theorem infinityConstantPoleDegreeLanding_of_c7_scale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (hscale : 12 * (S.infinityFaberPoleData hpole).scale.p = 1)
    (hcoordinate :
      (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 ∨
      (S.infinityFaberPoleData hpole).scale.leading3 ≠ 0) :
    GCD369CubeConstantPoleDegreeLanding := by
  rcases hcoordinate with h4 | h3
  · let n := (S.constantCoreNormalizedPPolynomial.coeff 4).natDegree
    have hdegree : (n : ℚ) =
        2 * (S.infinityFaberPoleData hpole).scale.p :=
      S.infinityLeading4_natDegree hsdegree hpole h4
    exact .c7A4 n (by rw [hdegree]; norm_num; linarith)
  · let n := (S.constantCoreNormalizedPPolynomial.coeff 3).natDegree
    have hdegree : (n : ℚ) =
        3 * (S.infinityFaberPoleData hpole).scale.p :=
      S.infinityLeading3_natDegree hsdegree hpole h3
    exact .c7A3 n (by rw [hdegree]; norm_num; linarith)

/-- Weight four (`c5`) reaches the `2/10` degree row. -/
theorem infinityConstantPoleDegreeLanding_of_c5_scale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (hscale : 10 * (S.infinityFaberPoleData hpole).scale.p = 1)
    (h4 : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0) :
    GCD369CubeConstantPoleDegreeLanding := by
  let n := (S.constantCoreNormalizedPPolynomial.coeff 4).natDegree
  have hdegree : (n : ℚ) =
      2 * (S.infinityFaberPoleData hpole).scale.p :=
    S.infinityLeading4_natDegree hsdegree hpole h4
  exact .c5A4 n (by rw [hdegree]; norm_num; linarith)

/-- Weight five (`c4`) reaches the `3/9` degree row. -/
theorem infinityConstantPoleDegreeLanding_of_c4_scale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (hscale : 9 * (S.infinityFaberPoleData hpole).scale.p = 1)
    (h3 : (S.infinityFaberPoleData hpole).scale.leading3 ≠ 0) :
    GCD369CubeConstantPoleDegreeLanding := by
  let n := (S.constantCoreNormalizedPPolynomial.coeff 3).natDegree
  have hdegree : (n : ℚ) =
      3 * (S.infinityFaberPoleData hpole).scale.p :=
    S.infinityLeading3_natDegree hsdegree hpole h3
  exact .c4A3 n (by rw [hdegree]; norm_num; linarith)

/-- Weight seven (`c2`) reaches the `2/7` degree row. -/
theorem infinityConstantPoleDegreeLanding_of_c2_scale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (hscale : 7 * (S.infinityFaberPoleData hpole).scale.p = 1)
    (h4 : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0) :
    GCD369CubeConstantPoleDegreeLanding := by
  let n := (S.constantCoreNormalizedPPolynomial.coeff 4).natDegree
  have hdegree : (n : ℚ) =
      2 * (S.infinityFaberPoleData hpole).scale.p :=
    S.infinityLeading4_natDegree hsdegree hpole h4
  exact .c2A4 n (by rw [hdegree]; norm_num; linarith)

/-- Weight eight (`c1`) reaches one of its two common-coordinate rows. -/
theorem infinityConstantPoleDegreeLanding_of_c1_scale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (hscale : 6 * (S.infinityFaberPoleData hpole).scale.p = 1)
    (hcoordinate :
      (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 ∨
      (S.infinityFaberPoleData hpole).scale.leading3 ≠ 0) :
    GCD369CubeConstantPoleDegreeLanding := by
  rcases hcoordinate with h4 | h3
  · let n := (S.constantCoreNormalizedPPolynomial.coeff 4).natDegree
    have hdegree : (n : ℚ) =
        2 * (S.infinityFaberPoleData hpole).scale.p :=
      S.infinityLeading4_natDegree hsdegree hpole h4
    exact .c1A4 n (by rw [hdegree]; norm_num; linarith)
  · let n := (S.constantCoreNormalizedPPolynomial.coeff 3).natDegree
    have hdegree : (n : ℚ) =
        3 * (S.infinityFaberPoleData hpole).scale.p :=
      S.infinityLeading3_natDegree hsdegree hpole h3
    exact .c1A3 n (by rw [hdegree]; norm_num; linarith)

/-- Weight ten (`rho1`) reaches the `2/4` degree row. -/
theorem infinityConstantPoleDegreeLanding_of_rho1_scale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0)
    (hscale : 4 * (S.infinityFaberPoleData hpole).scale.p = 1)
    (h4 : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0) :
    GCD369CubeConstantPoleDegreeLanding := by
  let n := (S.constantCoreNormalizedPPolynomial.coeff 4).natDegree
  have hdegree : (n : ℚ) =
      2 * (S.infinityFaberPoleData hpole).scale.p :=
    S.infinityLeading4_natDegree hsdegree hpole h4
  exact .rho1A4 n (by rw [hdegree]; norm_num; linarith)

/-- Constant-core sources reach the common-cubic/DS leading-component split
without any caller-selected landing hypothesis. -/
theorem infinityLeadingComponent_nonempty_of_constantCore
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    Nonempty (GCD369CubeLeadingComponent
      (S.infinityLeadingFaberSource
        (S.infinityNormalizedCoeffPole_of_constantCore hsdegree)).a0
      (S.infinityLeadingFaberSource
        (S.infinityNormalizedCoeffPole_of_constantCore hsdegree)).a1
      (S.infinityLeadingFaberSource
        (S.infinityNormalizedCoeffPole_of_constantCore hsdegree)).a2
      (S.infinityLeadingFaberSource
        (S.infinityNormalizedCoeffPole_of_constantCore hsdegree)).a3
      (S.infinityLeadingFaberSource
        (S.infinityNormalizedCoeffPole_of_constantCore hsdegree)).a4) :=
  ⟨(S.infinityLeadingFaberSource
    (S.infinityNormalizedCoeffPole_of_constantCore hsdegree)).toComponent⟩

/-- The Davenport--Stothers side of the leading-component split is already
excluded by polynomial degree integrality.  Thus every constant-core infinity
pole lies on the common-cubic component. -/
theorem infinityLeadingComponent_common_of_constantCore
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
    let F := S.infinityFaberPoleData hpole
    ∃ u v : k, (u ≠ 0 ∨ v ≠ 0) ∧
      F.scale.leading4 = 2 * u ∧ F.scale.leading3 = 2 * v ∧
      F.scale.leading2 = u ^ 2 ∧ F.scale.leading1 = 2 * u * v ∧
      F.scale.leading0 = v ^ 2 := by
  dsimp only
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let F := S.infinityFaberPoleData hpole
  let L := S.infinityLeadingFaberSource hpole
  have hcomponent := L.toComponent
  cases hcomponent with
  | common u v hprojective ha4 ha3 ha2 ha1 ha0 =>
      exact ⟨u, v, hprojective, ha4, ha3, ha2, ha1, ha0⟩
  | davenportStothers lambda hlambda ha4 ha3 ha2 ha1 ha0 =>
      have hlanding : GCD369CubeConstantPoleDegreeLanding :=
        S.infinityConstantPoleDegreeLanding_of_davenportStothers
          hsdegree hpole lambda hlambda ha4 ha3 ha2 ha1 ha0
      exact False.elim (GCD369CubeConstantPoleDegreeLandingEmpty hlanding)

/-- Every constant-core source canonically produces the lightweight common
coefficient jet used by the infinity first-load analysis. -/
noncomputable def infinityCommonCoefficientData
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    GCD369CubeHahnCommonCoefficientData k := by
  classical
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let F := S.infinityFaberPoleData hpole
  have hcommon :
      ∃ u v : k, (u ≠ 0 ∨ v ≠ 0) ∧
        F.scale.leading4 = 2 * u ∧ F.scale.leading3 = 2 * v ∧
        F.scale.leading2 = u ^ 2 ∧ F.scale.leading1 = 2 * u * v ∧
        F.scale.leading0 = v ^ 2 := by
    simpa only [hpole, F] using
      S.infinityLeadingComponent_common_of_constantCore hsdegree
  let u := Classical.choose hcommon
  let hu := Classical.choose_spec hcommon
  let v := Classical.choose hu
  let hv := Classical.choose_spec hu
  exact {
    faber := F
    u := u
    v := v
    hprojective := hv.1
    ha4 := hv.2.1
    ha3 := hv.2.2.1
    ha2 := hv.2.2.2.1
    ha1 := hv.2.2.2.2.1
    ha0 := hv.2.2.2.2.2
  }

@[simp] theorem infinityCommonCoefficientData_faber
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    (S.infinityCommonCoefficientData hsdegree).faber =
      S.infinityFaberPoleData
        (S.infinityNormalizedCoeffPole_of_constantCore hsdegree) := by
  rfl

/-- On the common-cubic component, at least one of `2 * p` and `3 * p` is
the literal natural degree of a normalized polynomial coefficient. -/
theorem infinityLeadingCommon_degree_dichotomy
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
    let F := S.infinityFaberPoleData hpole
    (∃ n : ℕ, (n : ℚ) = 2 * F.scale.p) ∨
      ∃ n : ℕ, (n : ℚ) = 3 * F.scale.p := by
  dsimp only
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let F := S.infinityFaberPoleData hpole
  obtain ⟨u, v, hprojective, ha4, ha3, _ha2, _ha1, _ha0⟩ :=
    S.infinityLeadingComponent_common_of_constantCore hsdegree
  rcases hprojective with hu | hv
  · left
    refine ⟨(S.constantCoreNormalizedPPolynomial.coeff 4).natDegree, ?_⟩
    exact S.infinityLeading4_natDegree hsdegree hpole (by
      rw [ha4]
      exact mul_ne_zero (by norm_num) hu)
  · right
    refine ⟨(S.constantCoreNormalizedPPolynomial.coeff 3).natDegree, ?_⟩
    exact S.infinityLeading3_natDegree hsdegree hpole (by
      rw [ha3]
      exact mul_ne_zero (by norm_num) hv)

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialAtInverse_injective
#print axioms GCD369CubeRatFuncHahnAtInfinity_X
#print axioms GCD369CubeRatFuncHahnAtInfinity_order_polynomial
#print axioms
  GCD369CubePolynomialSource.infinityNormalizedCoeffPole_of_constantCore
#print axioms GCD369CubePolynomialSource.infinityFaberPoleData
#print axioms
  GCD369CubePolynomialSource.infinityLeadingComponent_nonempty_of_constantCore
#print axioms
  GCD369CubePolynomialSource.infinityLeadingComponent_common_of_constantCore
