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

/-- The constant coefficient of a translated polynomial expansion is its
value at the selected finite place. -/
theorem ratFuncAtHahn46_algebraMap_coeff_zero (a : k) (p : k[X]) :
    (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) p)).coeff 0 =
      p.eval a := by
  rw [ratFuncAtHahn46_algebraMap]
  rw [Polynomial.algebraMap_hahnSeries_apply]
  change (HahnSeries.ofPowerSeries ℚ k
      (↑(p.comp (X + C a)) : PowerSeries k)).coeff
        (↑(0 : ℕ) : ℚ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff, Polynomial.coeff_coe]
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  simp

/-- A polynomial nonvanishing at the selected point expands with order
exactly zero. -/
theorem ratFuncAtHahn46_polynomial_orderTop_eq_zero_of_eval_ne
    (a : k) (p : k[X]) (hp : p.eval a ≠ 0) :
    (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) p)).orderTop = 0 := by
  apply le_antisymm
  · apply HahnSeries.orderTop_le_of_coeff_ne_zero
    rw [ratFuncAtHahn46_algebraMap_coeff_zero]
    exact hp
  · exact ratFuncAtHahn46_polynomial_orderTop_nonneg a p

/-- A nonzero polynomial vanishing at the selected point expands with
strictly positive order. -/
theorem ratFuncAtHahn46_polynomial_orderTop_pos_of_eval_eq_zero
    (a : k) (p : k[X]) (hp0 : p.eval a = 0) (hp : p ≠ 0) :
    (0 : WithTop ℚ) <
      (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) p)).orderTop := by
  let P : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) p)
  have hPne : P ≠ 0 := by
    simpa only [map_zero] using
      (ratFuncAtHahn46_injective a).ne (RatFunc.algebraMap_ne_zero hp)
  have hP0 : P.coeff 0 = 0 := by
    dsimp only [P]
    rw [ratFuncAtHahn46_algebraMap_coeff_zero, hp0]
  have hnonneg : (0 : WithTop ℚ) ≤ P.orderTop :=
    ratFuncAtHahn46_polynomial_orderTop_nonneg a p
  apply lt_of_le_of_ne hnonneg
  intro hEq
  have hlead := HahnSeries.coeff_orderTop_ne hEq.symm
  exact hlead hP0

/-- Nonnegative order is preserved by addition. -/
theorem hahnOrderTop_add_nonneg46 (x y : HahnSeries ℚ k)
    (hx : (0 : WithTop ℚ) ≤ x.orderTop)
    (hy : (0 : WithTop ℚ) ≤ y.orderTop) :
    (0 : WithTop ℚ) ≤ (x + y).orderTop := by
  exact (le_min hx hy).trans HahnSeries.min_orderTop_le_orderTop_add

/-- Nonnegative order is preserved by multiplication. -/
theorem hahnOrderTop_mul_nonneg46 (x y : HahnSeries ℚ k)
    (hx : (0 : WithTop ℚ) ≤ x.orderTop)
    (hy : (0 : WithTop ℚ) ≤ y.orderTop) :
    (0 : WithTop ℚ) ≤ (x * y).orderTop := by
  rw [HahnSeries.orderTop_mul]
  exact add_nonneg hx hy

/-- Ground-field constants are regular. -/
theorem hahnOrderTop_C_nonneg46 (c : k) :
    (0 : WithTop ℚ) ≤ (HahnSeries.C c : HahnSeries ℚ k).orderTop := by
  rw [HahnSeries.C_apply]
  by_cases hc : c = 0 <;> simp [hc, HahnSeries.orderTop_single]

/-- Rational scalar coefficients are regular in characteristic zero. -/
theorem hahnOrderTop_ratCast_nonneg46 [CharZero k] (c : ℚ) :
    (0 : WithTop ℚ) ≤ (c : HahnSeries ℚ k).orderTop := by
  rw [← map_ratCast (HahnSeries.C : k →+* HahnSeries ℚ k) c]
  exact hahnOrderTop_C_nonneg46 _

/-- Quotients of natural scalar numerals are regular. -/
theorem hahnOrderTop_natDiv_nonneg46 [CharZero k] (m n : ℕ) :
    (0 : WithTop ℚ) ≤
      ((m : HahnSeries ℚ k) / (n : HahnSeries ℚ k)).orderTop := by
  rw [← map_natCast (HahnSeries.C : k →+* HahnSeries ℚ k) m,
    ← map_natCast (HahnSeries.C : k →+* HahnSeries ℚ k) n,
    ← map_div₀]
  exact hahnOrderTop_C_nonneg46 _

/-- Nonnegative order is preserved by subtraction. -/
theorem hahnOrderTop_sub_nonneg46 (x y : HahnSeries ℚ k)
    (hx : (0 : WithTop ℚ) ≤ x.orderTop)
    (hy : (0 : WithTop ℚ) ≤ y.orderTop) :
    (0 : WithTop ℚ) ≤ (x - y).orderTop := by
  rw [sub_eq_add_neg]
  exact hahnOrderTop_add_nonneg46 x (-y) hx (by simpa using hy)

/-- Nonnegative order is preserved by negation. -/
theorem hahnOrderTop_neg_nonneg46 (x : HahnSeries ℚ k)
    (hx : (0 : WithTop ℚ) ≤ x.orderTop) :
    (0 : WithTop ℚ) ≤ (-x).orderTop := by
  simpa using hx

/-- Nonnegative order is preserved by natural powers. -/
theorem hahnOrderTop_pow_nonneg46 (x : HahnSeries ℚ k) (n : ℕ)
    (hx : (0 : WithTop ℚ) ≤ x.orderTop) :
    (0 : WithTop ℚ) ≤ (x ^ n).orderTop := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact hahnOrderTop_mul_nonneg46 _ _ ih hx

/-- The reviewed final-row one-form is regular whenever its coordinates and
their derivatives are regular. -/
theorem hahnEta46_orderTop_nonneg
    [CharZero k] (l beta gamma delta : k)
    (A B U dA dB dU : HahnSeries ℚ k)
    (hA : (0 : WithTop ℚ) ≤ A.orderTop)
    (hB : (0 : WithTop ℚ) ≤ B.orderTop)
    (hU : (0 : WithTop ℚ) ≤ U.orderTop)
    (hdA : (0 : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdU : (0 : WithTop ℚ) ≤ dU.orderTop) :
    (0 : WithTop ℚ) ≤
      (eta46 (HahnSeries.C l) A B U (HahnSeries.C beta)
        (HahnSeries.C gamma) (HahnSeries.C delta) dA dB dU).orderTop := by
  have hc (c : k) := hahnOrderTop_C_nonneg46 (k := k) c
  have hfrac (m n : ℕ) := hahnOrderTop_natDiv_nonneg46 (k := k) m n
  have hA2 := hahnOrderTop_pow_nonneg46 A 2 hA
  have hA3 := hahnOrderTop_pow_nonneg46 A 3 hA
  have hB2 := hahnOrderTop_pow_nonneg46 B 2 hB
  have hLA3 := hahnOrderTop_mul_nonneg46
    ((15 / 64 : HahnSeries ℚ k) * HahnSeries.C l) (A ^ 3)
      (hahnOrderTop_mul_nonneg46 _ _ (hfrac 15 64) (hc l)) hA3
  have hLB2 := hahnOrderTop_mul_nonneg46
    ((5 / 16 : HahnSeries ℚ k) * HahnSeries.C l) (B ^ 2)
      (hahnOrderTop_mul_nonneg46 _ _ (hfrac 5 16) (hc l)) hB2
  have hLAU := hahnOrderTop_mul_nonneg46
    ((5 / 32 : HahnSeries ℚ k) * HahnSeries.C l * A) U
      (hahnOrderTop_mul_nonneg46 _ _
        (hahnOrderTop_mul_nonneg46 _ _ (hfrac 5 32) (hc l)) hA) hU
  have hbetaA2 := hahnOrderTop_mul_nonneg46
    ((3 / 8 : HahnSeries ℚ k) * HahnSeries.C beta) (A ^ 2)
      (hahnOrderTop_mul_nonneg46 _ _ (hfrac 3 8) (hc beta)) hA2
  have hBU := hahnOrderTop_mul_nonneg46
    ((3 / 16 : HahnSeries ℚ k) * B) U
      (hahnOrderTop_mul_nonneg46 _ _ (hfrac 3 16) hB) hU
  have hgammaB := hahnOrderTop_mul_nonneg46
    ((1 / 2 : HahnSeries ℚ k) * HahnSeries.C gamma) B
      (hahnOrderTop_mul_nonneg46 _ _ (by simpa using hfrac 1 2) (hc gamma)) hB
  have hdeltaA := hahnOrderTop_mul_nonneg46
    ((1 / 2 : HahnSeries ℚ k) * HahnSeries.C delta) A
      (hahnOrderTop_mul_nonneg46 _ _ (by simpa using hfrac 1 2) (hc delta)) hA
  have hetaA : (0 : WithTop ℚ) ≤
      (etaA46 (HahnSeries.C l) A B U (HahnSeries.C beta)
        (HahnSeries.C gamma) (HahnSeries.C delta)).orderTop := by
    simp only [etaA46]
    exact hahnOrderTop_add_nonneg46 _ _
      (hahnOrderTop_sub_nonneg46 _ _
        (hahnOrderTop_add_nonneg46 _ _
          (hahnOrderTop_add_nonneg46 _ _
            (hahnOrderTop_sub_nonneg46 _ _
              (hahnOrderTop_sub_nonneg46 _ _ hLA3 hLB2) hLAU)
        hbetaA2) hBU) hgammaB) hdeltaA
  have hneg516 : (0 : WithTop ℚ) ≤
      (-5 / 16 : HahnSeries ℚ k).orderTop := by
    rw [show (-5 / 16 : HahnSeries ℚ k) =
      -((5 : HahnSeries ℚ k) / 16) by ring, HahnSeries.orderTop_neg]
    exact hfrac 5 16
  have hLAB := hahnOrderTop_mul_nonneg46
    ((-5 / 16 : HahnSeries ℚ k) * HahnSeries.C l * A) B
      (hahnOrderTop_mul_nonneg46 _ _
        (hahnOrderTop_mul_nonneg46 _ _ hneg516 (hc l)) hA) hB
  have hB2term := hahnOrderTop_mul_nonneg46
    (3 / 4 : HahnSeries ℚ k) (B ^ 2) (hfrac 3 4) hB2
  have hbetaB := hahnOrderTop_mul_nonneg46
    ((3 / 4 : HahnSeries ℚ k) * HahnSeries.C beta) B
      (hahnOrderTop_mul_nonneg46 _ _ (hfrac 3 4) (hc beta)) hB
  have hetaB : (0 : WithTop ℚ) ≤
      (etaB46 (HahnSeries.C l) A B (HahnSeries.C beta)).orderTop := by
    simp only [etaB46]
    exact hahnOrderTop_sub_nonneg46 _ _
      (hahnOrderTop_sub_nonneg46 _ _
        hLAB hB2term) hbetaB
  have hneg15128 : (0 : WithTop ℚ) ≤
      (-15 / 128 : HahnSeries ℚ k).orderTop := by
    rw [show (-15 / 128 : HahnSeries ℚ k) =
      -((15 : HahnSeries ℚ k) / 128) by ring, HahnSeries.orderTop_neg]
    exact hfrac 15 128
  have hLA2 := hahnOrderTop_mul_nonneg46
    ((-15 / 128 : HahnSeries ℚ k) * HahnSeries.C l) (A ^ 2)
      (hahnOrderTop_mul_nonneg46 _ _ hneg15128 (hc l)) hA2
  have hLU := hahnOrderTop_mul_nonneg46
    ((5 / 64 : HahnSeries ℚ k) * HahnSeries.C l) U
      (hahnOrderTop_mul_nonneg46 _ _ (hfrac 5 64) (hc l)) hU
  have hbetaA := hahnOrderTop_mul_nonneg46
    ((3 / 16 : HahnSeries ℚ k) * HahnSeries.C beta) A
      (hahnOrderTop_mul_nonneg46 _ _ (hfrac 3 16) (hc beta)) hA
  have hdeltaterm := hahnOrderTop_mul_nonneg46
    (1 / 4 : HahnSeries ℚ k) (HahnSeries.C delta)
      (by simpa using hfrac 1 4) (hc delta)
  have hetaU : (0 : WithTop ℚ) ≤
      (etaU46 (HahnSeries.C l) A U (HahnSeries.C beta)
        (HahnSeries.C delta)).orderTop := by
    simp only [etaU46]
    exact hahnOrderTop_sub_nonneg46 _ _
      (hahnOrderTop_sub_nonneg46 _ _
        (hahnOrderTop_add_nonneg46 _ _ hLA2 hLU)
        hbetaA) hdeltaterm
  simp only [eta46]
  exact hahnOrderTop_add_nonneg46 _ _
    (hahnOrderTop_add_nonneg46 _ _
      (hahnOrderTop_mul_nonneg46 _ _ hetaA hdA)
      (hahnOrderTop_mul_nonneg46 _ _ hetaB hdB))
    (hahnOrderTop_mul_nonneg46 _ _ hetaU hdU)

/-- A unit of order zero has inverse of order zero. -/
theorem hahnOrderTop_inv_eq_zero46 (x : HahnSeries ℚ k)
    (hx : x ≠ 0) (horder : x.orderTop = 0) :
    x⁻¹.orderTop = 0 := by
  have h := HahnSeries.orderTop_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, HahnSeries.orderTop_one, horder] at h
  simpa using h.symm

/-- If a rational function is regular at a finite place, then its reduced
denominator does not vanish there. -/
theorem ratFunc_denom_eval_ne_zero_of_orderTop_nonneg
    (a : k) (f : RatFunc k)
    (hf : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 a f).orderTop) :
    f.denom.eval a ≠ 0 := by
  intro hden0
  have hcoprime := aeval_ne_zero_of_isCoprime f.isCoprime_num_denom a
  have hnum : f.num.eval a ≠ 0 := by
    rcases hcoprime with hnum | hden
    · simpa [aeval_def, Polynomial.eval₂_at_apply] using hnum
    · exact (hden (by
        simpa [aeval_def, Polynomial.eval₂_at_apply] using hden0)).elim
  let F : HahnSeries ℚ k := ratFuncAtHahn46 a f
  let N : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) f.num)
  let D : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) f.denom)
  have hN : N.orderTop = 0 := by
    dsimp only [N]
    exact ratFuncAtHahn46_polynomial_orderTop_eq_zero_of_eval_ne a f.num hnum
  have hD : (0 : WithTop ℚ) < D.orderTop := by
    dsimp only [D]
    exact ratFuncAtHahn46_polynomial_orderTop_pos_of_eval_eq_zero
      a f.denom hden0 f.denom_ne_zero
  have hrat : f * algebraMap k[X] (RatFunc k) f.denom =
      algebraMap k[X] (RatFunc k) f.num := by
    calc
      f * algebraMap k[X] (RatFunc k) f.denom =
          (algebraMap k[X] (RatFunc k) f.num /
              algebraMap k[X] (RatFunc k) f.denom) *
            algebraMap k[X] (RatFunc k) f.denom := by
              rw [f.num_div_denom]
      _ = algebraMap k[X] (RatFunc k) f.num :=
        div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
  have hmapped := congrArg (ratFuncAtHahn46 a) hrat
  have hFD : F * D = N := by
    simpa only [F, N, D, map_mul] using hmapped
  have hprod : (0 : WithTop ℚ) < (F * D).orderTop := by
    rw [HahnSeries.orderTop_mul]
    exact hD.trans_le (by simpa [add_comm] using add_le_add_right hf D.orderTop)
  rw [hFD, hN] at hprod
  exact (lt_irrefl 0 hprod).elim

/-- The standard rational derivative of a function regular at a finite
place is regular there as well. -/
theorem ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg
    [CharZero k] (a : k) (f : RatFunc k)
    (hf : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 a f).orderTop) :
    (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (Differential.deriv f)).orderTop := by
  letI : Algebra ℤ (RatFunc k) := Ring.toIntAlgebra (RatFunc k)
  let N : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) f.num)
  let D : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) f.denom)
  let N' : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) f.num.derivative)
  let D' : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) f.denom.derivative)
  have hden := ratFunc_denom_eval_ne_zero_of_orderTop_nonneg a f hf
  have hD0 : D.orderTop = 0 := by
    dsimp only [D]
    exact ratFuncAtHahn46_polynomial_orderTop_eq_zero_of_eval_ne
      a f.denom hden
  have hDne : D ≠ 0 := by
    dsimp only [D]
    simpa only [map_zero] using (ratFuncAtHahn46_injective a).ne
      (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
  have hDinv : D⁻¹.orderTop = 0 :=
    hahnOrderTop_inv_eq_zero46 D hDne hD0
  have hN : (0 : WithTop ℚ) ≤ N.orderTop := by
    dsimp only [N]
    exact ratFuncAtHahn46_polynomial_orderTop_nonneg a f.num
  have hD : (0 : WithTop ℚ) ≤ D.orderTop := hD0.ge
  have hN' : (0 : WithTop ℚ) ≤ N'.orderTop := by
    dsimp only [N']
    exact ratFuncAtHahn46_polynomial_orderTop_nonneg a f.num.derivative
  have hD' : (0 : WithTop ℚ) ≤ D'.orderTop := by
    dsimp only [D']
    exact ratFuncAtHahn46_polynomial_orderTop_nonneg a f.denom.derivative
  have hinside : (0 : WithTop ℚ) ≤ (D * N' - N * D').orderTop := by
    rw [sub_eq_add_neg]
    apply hahnOrderTop_add_nonneg46
    · exact hahnOrderTop_mul_nonneg46 D N' hD hN'
    · simpa using hahnOrderTop_mul_nonneg46 N D' hN hD'
  have hderiv : Differential.deriv f =
      (algebraMap k[X] (RatFunc k) f.denom)⁻¹ ^ 2 *
        (algebraMap k[X] (RatFunc k) f.denom *
            algebraMap k[X] (RatFunc k) f.num.derivative -
            algebraMap k[X] (RatFunc k) f.num *
            algebraMap k[X] (RatFunc k) f.denom.derivative) := by
    calc
      Differential.deriv f = Differential.deriv
          (algebraMap k[X] (RatFunc k) f.num /
            algebraMap k[X] (RatFunc k) f.denom) :=
        congrArg Differential.deriv f.num_div_denom.symm
      _ = _ := by
        rw [Derivation.leibniz_div, GCD369RatFuncDerivative,
          GCD369RatFuncDerivative]
        simp only [smul_eq_mul]
  rw [hderiv]
  simp only [map_mul, map_sub, map_pow, map_inv₀]
  change (0 : WithTop ℚ) ≤ (D⁻¹ ^ 2 * (D * N' - N * D')).orderTop
  apply hahnOrderTop_mul_nonneg46
  · rw [pow_two, HahnSeries.orderTop_mul, hDinv]
    simp
  · exact hinside

/-- At a zero of the nonzero common core, the nonzero last Jacobian row
forces at least one of the three coefficient-curve coordinates to have a
pole. -/
theorem sourceLastRow_forces_coordinate_pole46
    [CharZero k] (a : k) (h0 : k[X]) (j l beta gamma delta : k)
    (A B U : RatFunc k) (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0)
    (hj : j ≠ 0)
    (hlast : algebraMap k[X] (RatFunc k) h0 *
      eta46 (algebraMap k (RatFunc k) l) A B U
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta)
        (Differential.deriv A) (Differential.deriv B)
        (Differential.deriv U) = RatFunc.C j) :
    ¬ ((0 : WithTop ℚ) ≤ (ratFuncAtHahn46 a A).orderTop ∧
      (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 a B).orderTop ∧
      (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 a U).orderTop) := by
  rintro ⟨hA, hB, hU⟩
  let H : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 a A
  let BH : HahnSeries ℚ k := ratFuncAtHahn46 a B
  let UH : HahnSeries ℚ k := ratFuncAtHahn46 a U
  let dAH : HahnSeries ℚ k := ratFuncAtHahn46 a (Differential.deriv A)
  let dBH : HahnSeries ℚ k := ratFuncAtHahn46 a (Differential.deriv B)
  let dUH : HahnSeries ℚ k := ratFuncAtHahn46 a (Differential.deriv U)
  have hHpos : (0 : WithTop ℚ) < H.orderTop := by
    dsimp only [H]
    exact ratFuncAtHahn46_polynomial_orderTop_pos_of_eval_eq_zero
      a h0 hroot hh0
  have hdA : (0 : WithTop ℚ) ≤ dAH.orderTop := by
    dsimp only [dAH]
    exact ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg a A hA
  have hdB : (0 : WithTop ℚ) ≤ dBH.orderTop := by
    dsimp only [dBH]
    exact ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg a B hB
  have hdU : (0 : WithTop ℚ) ≤ dUH.orderTop := by
    dsimp only [dUH]
    exact ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg a U hU
  have hetaMap : ratFuncAtHahn46 a
        (eta46 (algebraMap k (RatFunc k) l) A B U
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) delta)
          (Differential.deriv A) (Differential.deriv B)
          (Differential.deriv U)) =
      eta46 (HahnSeries.C l) AH BH UH (HahnSeries.C beta)
        (HahnSeries.C gamma) (HahnSeries.C delta) dAH dBH dUH := by
    simp only [eta46, etaA46, etaB46, etaU46, AH, BH, UH, dAH, dBH,
      dUH, map_add, map_sub, map_mul, map_pow, map_neg, map_div₀,
      map_ofNat, map_one, RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C]
  have heta : (0 : WithTop ℚ) ≤
      (eta46 (HahnSeries.C l) AH BH UH (HahnSeries.C beta)
        (HahnSeries.C gamma) (HahnSeries.C delta) dAH dBH dUH).orderTop :=
    hahnEta46_orderTop_nonneg l beta gamma delta AH BH UH dAH dBH dUH
      hA hB hU hdA hdB hdU
  have hmapped := congrArg (ratFuncAtHahn46 a) hlast
  have hproduct : H *
      eta46 (HahnSeries.C l) AH BH UH (HahnSeries.C beta)
        (HahnSeries.C gamma) (HahnSeries.C delta) dAH dBH dUH =
      HahnSeries.C j := by
    simpa only [H, map_mul, hetaMap, ratFuncAtHahn46_C] using hmapped
  have hprodpos : (0 : WithTop ℚ) <
      (H * eta46 (HahnSeries.C l) AH BH UH (HahnSeries.C beta)
        (HahnSeries.C gamma) (HahnSeries.C delta) dAH dBH dUH).orderTop := by
    rw [HahnSeries.orderTop_mul]
    exact hHpos.trans_le (by
      simpa [add_comm] using add_le_add_left heta H.orderTop)
  rw [hproduct, HahnSeries.C_apply, HahnSeries.orderTop_single hj] at hprodpos
  exact (lt_irrefl 0 (by simpa using hprodpos)).elim

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
