import LowScale46ScaleZero
import Mathlib.RingTheory.LaurentSeries

/-! # Finite-place series bridge for the `(4,6)` source

The local Newton exclusions are stated for rational-exponent Hahn series.
This module starts the global bridge by translating a selected finite point
to the origin, embedding `k(x)` injectively in Laurent series, and then
embedding integer exponents in rational exponents.  Polynomial loads become
series of nonnegative order.
-/

noncomputable section

open Polynomial
open scoped LaurentSeries

namespace Max11DegreeRoutes

section PoleEmbedding

variable {k : Type*} [Field k]

/-- Translation by a finite point on coefficient polynomials. -/
def polynomialTranslate46 (a : k) : k[X] →+* k[X] :=
  Polynomial.compRingHom (X + C a)

/-- Polynomial translation is injective, with inverse translation by `-a`. -/
theorem polynomialTranslate46_injective (a : k) :
    Function.Injective (polynomialTranslate46 a) := by
  intro p q h
  have h2 := congrArg (fun r : k[X] => r.comp (X - C a)) h
  simpa only [polynomialTranslate46, Polynomial.coe_compRingHom_apply,
    Polynomial.comp_assoc, add_comp, sub_comp, X_comp, C_comp,
    sub_add_cancel, comp_X] using h2

/-- Translate at `a` and embed the resulting polynomial in `k((X))`. -/
def polynomialAtLaurent46 (a : k) : k[X] →+* LaurentSeries k :=
  (algebraMap k[X] (LaurentSeries k)).comp (polynomialTranslate46 a)

theorem polynomialAtLaurent46_injective (a : k) :
    Function.Injective (polynomialAtLaurent46 a) :=
  (FaithfulSMul.algebraMap_injective k[X] (LaurentSeries k)).comp
    (polynomialTranslate46_injective a)

/-- Nonzero polynomials stay nonzero after translated Laurent expansion. -/
theorem polynomialAtLaurent46_mem_nonZeroDivisors (a : k) :
    nonZeroDivisors (k[X]) ≤
      Submonoid.comap (polynomialAtLaurent46 a)
        (nonZeroDivisors (LaurentSeries k)) := by
  intro p hp
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    (by simpa using
      (polynomialAtLaurent46_injective a).ne (nonZeroDivisors.ne_zero hp))

/-- The injective translated Laurent expansion of the rational function
field at the finite point `a`. -/
def ratFuncAtLaurent46 (a : k) : RatFunc k →+* LaurentSeries k :=
  RatFunc.liftRingHom (polynomialAtLaurent46 a)
    (polynomialAtLaurent46_mem_nonZeroDivisors a)

theorem ratFuncAtLaurent46_injective (a : k) :
    Function.Injective (ratFuncAtLaurent46 a) :=
  RatFunc.liftRingHom_injective _ (polynomialAtLaurent46_injective a)

/-- The integer-to-rational exponent map is injective. -/
theorem intCastAddHom46_injective :
    Function.Injective (Int.castAddHom ℚ) := by
  exact Int.cast_injective

/-- The integer-to-rational exponent map reflects order. -/
theorem intCastAddHom46_le (m n : ℤ) :
    (Int.castAddHom ℚ) m ≤ (Int.castAddHom ℚ) n ↔ m ≤ n :=
  Int.cast_le

/-- Embed integer Laurent exponents in rational Hahn exponents. -/
def laurentToRationalHahn46 : LaurentSeries k →+* HahnSeries ℚ k :=
  HahnSeries.embDomainRingHom (Int.castAddHom ℚ)
    intCastAddHom46_injective intCastAddHom46_le

theorem laurentToRationalHahn46_injective :
    Function.Injective (laurentToRationalHahn46 (k := k)) :=
  HahnSeries.embDomain_injective

/-- The finite-place embedding used to instantiate the local chart. -/
def ratFuncAtHahn46 (a : k) : RatFunc k →+* HahnSeries ℚ k :=
  (laurentToRationalHahn46 (k := k)).comp (ratFuncAtLaurent46 a)

theorem ratFuncAtHahn46_injective (a : k) :
    Function.Injective (ratFuncAtHahn46 a) :=
  laurentToRationalHahn46_injective.comp (ratFuncAtLaurent46_injective a)

/-- Extending Laurent exponents commutes with the natural embedding of
coefficient polynomials. -/
theorem laurentToRationalHahn46_algebraMap_polynomial (p : k[X]) :
    laurentToRationalHahn46
        (algebraMap k[X] (LaurentSeries k) p) =
      algebraMap k[X] (HahnSeries ℚ k) p := by
  have hhom :
      (laurentToRationalHahn46 (k := k)).comp
          (algebraMap k[X] (LaurentSeries k)) =
        algebraMap k[X] (HahnSeries ℚ k) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, Polynomial.algebraMap_hahnSeries_apply]
      rw [show (HahnSeries.ofPowerSeries ℤ k)
          (↑(C c) : PowerSeries k) = HahnSeries.C c by simp]
      rw [show (HahnSeries.ofPowerSeries ℚ k)
          (↑(C c) : PowerSeries k) = HahnSeries.C c by simp]
      exact HahnSeries.embDomainRingHom_C
    · simp only [RingHom.comp_apply, Polynomial.algebraMap_hahnSeries_apply]
      rw [show (HahnSeries.ofPowerSeries ℤ k)
          (↑(X : k[X]) : PowerSeries k) =
            HahnSeries.single (1 : ℤ) 1 by simp]
      rw [show (HahnSeries.ofPowerSeries ℚ k)
          (↑(X : k[X]) : PowerSeries k) =
            HahnSeries.single (1 : ℚ) 1 by simp]
      exact HahnSeries.embDomain_single
  exact DFunLike.congr_fun hhom p

/-- The finite-place embedding sends ground-field constants to Hahn
constants. -/
@[simp]
theorem ratFuncAtHahn46_C (a c : k) :
    ratFuncAtHahn46 a (RatFunc.C c) = HahnSeries.C c := by
  simp only [ratFuncAtHahn46, RingHom.comp_apply, ratFuncAtLaurent46,
    RatFunc.liftRingHom_C, polynomialAtLaurent46, RingHom.comp_apply,
    polynomialTranslate46, Polynomial.coe_compRingHom_apply, C_comp,
    map_C]
  rw [laurentToRationalHahn46_algebraMap_polynomial]
  simp

/-- Exact action on an embedded coefficient polynomial. -/
theorem ratFuncAtHahn46_algebraMap (a : k) (p : k[X]) :
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (HahnSeries ℚ k) (p.comp (X + C a)) := by
  simp only [ratFuncAtHahn46, RingHom.comp_apply, ratFuncAtLaurent46,
    RatFunc.liftRingHom_algebraMap, polynomialAtLaurent46,
    RingHom.comp_apply, polynomialTranslate46,
    Polynomial.coe_compRingHom_apply]
  exact laurentToRationalHahn46_algebraMap_polynomial _

/-- Every polynomial load has nonnegative order at every finite place. -/
theorem polynomialHahn46_orderTop_nonneg (p : k[X]) :
    (0 : WithTop ℚ) ≤
      (algebraMap k[X] (HahnSeries ℚ k) p).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro j hj
  rw [Polynomial.algebraMap_hahnSeries_apply,
    HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  intro h
  obtain ⟨n, hn⟩ := h
  simp only [Nat.castOrderEmbedding_apply] at hn
  subst j
  have hnot : ¬ (((n : ℚ) : WithTop ℚ) < 0) := by simp
  apply hnot
  simpa using hj

/-- In particular, an original coefficient polynomial remains regular after
translation and finite-place embedding. -/
theorem ratFuncAtHahn46_polynomial_orderTop_nonneg (a : k) (p : k[X]) :
    (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) p)).orderTop := by
  rw [ratFuncAtHahn46_algebraMap]
  exact polynomialHahn46_orderTop_nonneg _

section OrderNormalization

/-- Divide every rational Hahn exponent by a selected positive order. -/
def rationalExponentNormalize46 (rho : ℚ) : ℚ →+ ℚ where
  toFun q := q / rho
  map_zero' := by simp
  map_add' x y := by ring

theorem rationalExponentNormalize46_injective {rho : ℚ} (hrho : rho ≠ 0) :
    Function.Injective (rationalExponentNormalize46 rho) := by
  intro x y h
  dsimp only [rationalExponentNormalize46] at h
  exact (div_left_inj' hrho).mp h

theorem rationalExponentNormalize46_le {rho : ℚ} (hrho : 0 < rho)
    (x y : ℚ) :
    rationalExponentNormalize46 rho x ≤ rationalExponentNormalize46 rho y ↔
      x ≤ y := by
  simp only [rationalExponentNormalize46]
  exact div_le_div_iff_of_pos_right hrho

/-- The induced injective reindexing of rational-exponent Hahn series. -/
def normalizeHahnOrder46 (rho : ℚ) (hrho : 0 < rho) :
    HahnSeries ℚ k →+* HahnSeries ℚ k :=
  HahnSeries.embDomainRingHom (rationalExponentNormalize46 rho)
    (rationalExponentNormalize46_injective hrho.ne')
    (rationalExponentNormalize46_le hrho)

theorem normalizeHahnOrder46_injective (rho : ℚ) (hrho : 0 < rho) :
    Function.Injective (normalizeHahnOrder46 (k := k) rho hrho) :=
  HahnSeries.embDomain_injective

@[simp]
theorem normalizeHahnOrder46_C (rho : ℚ) (hrho : 0 < rho) (c : k) :
    normalizeHahnOrder46 rho hrho (HahnSeries.C c) = HahnSeries.C c :=
  HahnSeries.embDomainRingHom_C

/-- Order is divided by `rho`, including the zero series via `WithTop.map`. -/
theorem normalizeHahnOrder46_orderTop (rho : ℚ) (hrho : 0 < rho)
    (x : HahnSeries ℚ k) :
    (normalizeHahnOrder46 rho hrho x).orderTop =
      WithTop.map (rationalExponentNormalize46 rho) x.orderTop := by
  exact HahnSeries.orderTop_embDomain

/-- A series of positive finite order `rho` becomes an order-one series. -/
theorem normalizeHahnOrder46_orderTop_eq_one
    (rho : ℚ) (hrho : 0 < rho) (x : HahnSeries ℚ k)
    (hx : x.orderTop = (↑rho : WithTop ℚ)) :
    (normalizeHahnOrder46 rho hrho x).orderTop =
      (↑(1 : ℚ) : WithTop ℚ) := by
  rw [normalizeHahnOrder46_orderTop, hx, WithTop.map_coe]
  rw [WithTop.coe_eq_coe]
  change rho / rho = 1
  exact div_self hrho.ne'

/-- Nonnegative order remains nonnegative under positive normalization. -/
theorem normalizeHahnOrder46_orderTop_nonneg
    (rho : ℚ) (hrho : 0 < rho) (x : HahnSeries ℚ k)
    (hx : (0 : WithTop ℚ) ≤ x.orderTop) :
    (0 : WithTop ℚ) ≤ (normalizeHahnOrder46 rho hrho x).orderTop := by
  rw [normalizeHahnOrder46_orderTop]
  by_cases htop : x.orderTop = ⊤
  · rw [htop, WithTop.map_top]
    exact le_top
  · rw [← WithTop.coe_untop x.orderTop htop, WithTop.map_coe]
    change ((↑(0 : ℚ) : WithTop ℚ) ≤
      ↑(rationalExponentNormalize46 rho (x.orderTop.untop htop)))
    rw [WithTop.coe_le_coe]
    change (0 : ℚ) ≤ x.orderTop.untop htop / rho
    have hq0 : (0 : ℚ) ≤ x.orderTop.untop htop := by
      rw [← WithTop.coe_untop x.orderTop htop] at hx
      exact WithTop.coe_le_coe.mp hx
    exact div_nonneg hq0 hrho.le

end OrderNormalization

end PoleEmbedding

end Max11DegreeRoutes
