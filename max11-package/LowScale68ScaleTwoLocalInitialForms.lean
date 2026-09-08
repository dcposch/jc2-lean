import LowScale68ScaleTwoNonalignedInfinity
import LowScale68Infinity

/-! # First local initial forms for the nonaligned `(6,8)` source

For the degree-one local scale `h`, the sextic depression center has
denominator `h⁵`.  Consequently the five depressed sextic coordinates have
denominators `h¹⁰,h¹⁵,h²⁰,h²⁵,h³⁰`.  This module gives their
exact polynomial numerators and transports those identities to the finite-
place Hahn embedding.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ClearedCoordinates68

variable {k : Type*} [Field k] [CharZero k]

local instance localInitialHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Numerator of the depressed quartic coefficient `A`. -/
def localClearedA68 (h a5 a4 : k[X]) : k[X] :=
  a4 * h ^ 6 - C (5 / 12 : k) * a5 ^ 2

/-- Numerator of the depressed cubic coefficient `B`. -/
def localClearedB68 (h a5 a4 a3 : k[X]) : k[X] :=
  a3 * h ^ 12 - C (2 / 3 : k) * a4 * a5 * h ^ 6 +
    C (5 / 27 : k) * a5 ^ 3

/-- Numerator of the depressed quadratic coefficient `C0`. -/
def localClearedC68 (h a5 a4 a3 a2 : k[X]) : k[X] :=
  a2 * h ^ 18 - C (1 / 2 : k) * a3 * a5 * h ^ 12 +
    C (1 / 6 : k) * a4 * a5 ^ 2 * h ^ 6 -
    C (5 / 144 : k) * a5 ^ 4

/-- Numerator of the depressed linear coefficient `D`. -/
def localClearedD68 (h a5 a4 a3 a2 a1 : k[X]) : k[X] :=
  a1 * h ^ 24 - C (1 / 3 : k) * a2 * a5 * h ^ 18 +
    C (1 / 12 : k) * a3 * a5 ^ 2 * h ^ 12 -
    C (1 / 54 : k) * a4 * a5 ^ 3 * h ^ 6 +
    C (1 / 324 : k) * a5 ^ 5

/-- Numerator of the depressed constant coefficient `E`. -/
def localClearedE68 (h a5 a4 a3 a2 a1 a0 : k[X]) : k[X] :=
  a0 * h ^ 30 - C (1 / 6 : k) * a1 * a5 * h ^ 24 +
    C (1 / 36 : k) * a2 * a5 ^ 2 * h ^ 18 -
    C (1 / 216 : k) * a3 * a5 ^ 3 * h ^ 12 +
    C (1 / 1296 : k) * a4 * a5 ^ 4 * h ^ 6 -
    C (5 / 46656 : k) * a5 ^ 6

/-- Exact denominator clearing for `A`. -/
theorem algebraMap_localClearedA68
    (h a5 a4 : k[X]) (hh : h ≠ 0) :
    algebraMap k[X] (RatFunc k) (localClearedA68 h a5 a4) =
      (algebraMap k[X] (RatFunc k) h) ^ 10 *
        depressedA68 (algebraMap k[X] (RatFunc k) h)
          (sexticDepressionR68 (algebraMap k[X] (RatFunc k) h)
            (algebraMap k[X] (RatFunc k) a5))
          (algebraMap k[X] (RatFunc k) a5)
          (algebraMap k[X] (RatFunc k) a4) := by
  simp only [localClearedA68, depressedA68, sexticDepressionR68,
    map_sub, map_mul, map_pow, map_div₀, map_ofNat, RatFunc.algebraMap_C]
  have hh' : algebraMap k[X] (RatFunc k) h ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh
  field_simp [hh']
  ring

/-- Exact denominator clearing for `B`. -/
theorem algebraMap_localClearedB68
    (h a5 a4 a3 : k[X]) (hh : h ≠ 0) :
    algebraMap k[X] (RatFunc k) (localClearedB68 h a5 a4 a3) =
      (algebraMap k[X] (RatFunc k) h) ^ 15 *
        depressedB68 (algebraMap k[X] (RatFunc k) h)
          (sexticDepressionR68 (algebraMap k[X] (RatFunc k) h)
            (algebraMap k[X] (RatFunc k) a5))
          (algebraMap k[X] (RatFunc k) a5)
          (algebraMap k[X] (RatFunc k) a4)
          (algebraMap k[X] (RatFunc k) a3) := by
  simp only [localClearedB68, depressedB68, sexticDepressionR68,
    map_add, map_sub, map_mul, map_pow, map_div₀, map_ofNat,
    RatFunc.algebraMap_C]
  have hh' : algebraMap k[X] (RatFunc k) h ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh
  field_simp [hh']
  ring

/-- Exact denominator clearing for `C0`. -/
theorem algebraMap_localClearedC68
    (h a5 a4 a3 a2 : k[X]) (hh : h ≠ 0) :
    algebraMap k[X] (RatFunc k) (localClearedC68 h a5 a4 a3 a2) =
      (algebraMap k[X] (RatFunc k) h) ^ 20 *
        depressedC68 (algebraMap k[X] (RatFunc k) h)
          (sexticDepressionR68 (algebraMap k[X] (RatFunc k) h)
            (algebraMap k[X] (RatFunc k) a5))
          (algebraMap k[X] (RatFunc k) a5)
          (algebraMap k[X] (RatFunc k) a4)
          (algebraMap k[X] (RatFunc k) a3)
          (algebraMap k[X] (RatFunc k) a2) := by
  simp only [localClearedC68, depressedC68, sexticDepressionR68,
    map_add, map_sub, map_mul, map_pow, map_div₀, map_ofNat,
    RatFunc.algebraMap_C]
  have hh' : algebraMap k[X] (RatFunc k) h ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh
  field_simp [hh']
  simp only [map_one]
  ring

/-- Exact denominator clearing for `D`. -/
theorem algebraMap_localClearedD68
    (h a5 a4 a3 a2 a1 : k[X]) (hh : h ≠ 0) :
    algebraMap k[X] (RatFunc k) (localClearedD68 h a5 a4 a3 a2 a1) =
      (algebraMap k[X] (RatFunc k) h) ^ 25 *
        depressedD68 (algebraMap k[X] (RatFunc k) h)
          (sexticDepressionR68 (algebraMap k[X] (RatFunc k) h)
            (algebraMap k[X] (RatFunc k) a5))
          (algebraMap k[X] (RatFunc k) a5)
          (algebraMap k[X] (RatFunc k) a4)
          (algebraMap k[X] (RatFunc k) a3)
          (algebraMap k[X] (RatFunc k) a2)
          (algebraMap k[X] (RatFunc k) a1) := by
  simp only [localClearedD68, depressedD68, sexticDepressionR68,
    map_add, map_sub, map_neg, map_mul, map_pow, map_div₀, map_ofNat,
    RatFunc.algebraMap_C]
  have hh' : algebraMap k[X] (RatFunc k) h ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh
  field_simp [hh']
  simp only [map_one]
  ring

/-- Exact denominator clearing for `E`. -/
theorem algebraMap_localClearedE68
    (h a5 a4 a3 a2 a1 a0 : k[X]) (hh : h ≠ 0) :
    algebraMap k[X] (RatFunc k) (localClearedE68 h a5 a4 a3 a2 a1 a0) =
      (algebraMap k[X] (RatFunc k) h) ^ 30 *
        depressedE68 (algebraMap k[X] (RatFunc k) h)
          (sexticDepressionR68 (algebraMap k[X] (RatFunc k) h)
            (algebraMap k[X] (RatFunc k) a5))
          (algebraMap k[X] (RatFunc k) a5)
          (algebraMap k[X] (RatFunc k) a4)
          (algebraMap k[X] (RatFunc k) a3)
          (algebraMap k[X] (RatFunc k) a2)
          (algebraMap k[X] (RatFunc k) a1)
          (algebraMap k[X] (RatFunc k) a0) := by
  simp only [localClearedE68, depressedE68, sexticDepressionR68,
    map_add, map_sub, map_neg, map_mul, map_pow, map_div₀, map_ofNat,
    RatFunc.algebraMap_C]
  have hh' : algebraMap k[X] (RatFunc k) h ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh
  field_simp [hh']
  simp only [map_one]
  ring

/-- The five explicit numerators above are the actual coordinates of every
integrated source package coming from a normalized square-core sextic. -/
theorem SquareConstantLIntegratedSourceData68.clearedCoordinates
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (S : SquareConstantLIntegratedSourceData68 p q j h0 l)
    (hp : p.natDegree = 6) (hh0 : h0 ≠ 0)
    (hH : H = h0 ^ 2) (hp6 : p.coeff 6 = H ^ 3) :
    let h := algebraMap k[X] (RatFunc k) h0
    algebraMap k[X] (RatFunc k)
        (localClearedA68 h0 (p.coeff 5) (p.coeff 4)) = h ^ 10 * S.A ∧
    algebraMap k[X] (RatFunc k)
        (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)) =
      h ^ 15 * S.B ∧
    algebraMap k[X] (RatFunc k)
        (localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2)) = h ^ 20 * S.C0 ∧
    algebraMap k[X] (RatFunc k)
        (localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1)) = h ^ 25 * S.D ∧
    algebraMap k[X] (RatFunc k)
        (localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0)) = h ^ 30 * S.E := by
  dsimp only
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let A' := depressedA68 h S.r a5 a4
  let B' := depressedB68 h S.r a5 a4 a3
  let C' := depressedC68 h S.r a5 a4 a3 a2
  let D' := depressedD68 h S.r a5 a4 a3 a2 a1
  let E' := depressedE68 h S.r a5 a4 a3 a2 a1 a0
  have hh : h ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = h ^ 6 := by
    simp only [hp6, hH, h, map_pow]
    ring
  have hpDep : affineDepress68 h S.r (sourceToRatFunc68 p) =
      depressedSextic68 A' B' C' D' E' := by
    exact affineDepress_sourceSextic68 p h S.r hp hh hpTop S.center_eq
  have hforms : depressedSextic68 A' B' C' D' E' =
      depressedSextic68 S.A S.B S.C0 S.D S.E := hpDep.symm.trans S.sextic_eq
  have hA : A' = S.A := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 4) hforms
    simpa [depressedSextic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using hc
  have hB : B' = S.B := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 3) hforms
    simpa [depressedSextic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using hc
  have hC : C' = S.C0 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 2) hforms
    simpa [depressedSextic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using hc
  have hD : D' = S.D := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 1) hforms
    simpa [depressedSextic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using hc
  have hE : E' = S.E := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) hforms
    simpa [depressedSextic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using hc
  dsimp only [A', B', C', D', E'] at hA hB hC hD hE
  rw [S.center_eq] at hA hB hC hD hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [h, a5, a4, hA] using
      algebraMap_localClearedA68 h0 (p.coeff 5) (p.coeff 4) hh0
  · simpa only [h, a5, a4, a3, hB] using
      algebraMap_localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3) hh0
  · simpa only [h, a5, a4, a3, a2, hC] using
      algebraMap_localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) hh0
  · simpa only [h, a5, a4, a3, a2, a1, hD] using
      algebraMap_localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) hh0
  · simpa only [h, a5, a4, a3, a2, a1, a0, hE] using
      algebraMap_localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0) hh0

/-- A polynomial numerator regular at a finite place gives the expected
lower bound after division by a power of a simple local scale. -/
theorem localHahn_orderTop_ge_of_cleared
    (a : k) (h0 A0 : k[X]) (A : RatFunc k) (n : ℕ)
    (hscale :
      (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(1 : ℚ) : WithTop ℚ))
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * A) :
    (↑(-(n : ℚ)) : WithTop ℚ) ≤
      (ratFuncAtHahn46 a A).orderTop := by
  let hH : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 a A
  let A0H : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) A0)
  have hpow : (hH ^ n).orderTop =
      (↑(n : ℚ) : WithTop ℚ) := by
    dsimp only [hH]
    simpa using hahnOrderTop_pow_eq46
      (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)) 1 n hscale
  have hmapped : A0H = hH ^ n * AH := by
    dsimp only [A0H, hH, AH]
    simpa only [map_mul, map_pow] using congrArg (ratFuncAtHahn46 a) hclear
  have hregular : (0 : WithTop ℚ) ≤ A0H.orderTop := by
    dsimp only [A0H]
    exact ratFuncAtHahn46_polynomial_orderTop_nonneg a A0
  have hsum : (0 : WithTop ℚ) ≤
      (↑(n : ℚ) : WithTop ℚ) + AH.orderTop := by
    calc
      (0 : WithTop ℚ) ≤ A0H.orderTop := hregular
      _ = (hH ^ n * AH).orderTop := congrArg HahnSeries.orderTop hmapped
      _ = (↑(n : ℚ) : WithTop ℚ) + AH.orderTop := by
        rw [HahnSeries.orderTop_mul, hpow]
  have hadd := add_le_add_left hsum
    (↑(-(n : ℚ)) : WithTop ℚ)
  have hcancel :
      (↑(n : ℚ) : WithTop ℚ) + AH.orderTop +
          (↑(-(n : ℚ)) : WithTop ℚ) = AH.orderTop := by
    calc
      (↑(n : ℚ) : WithTop ℚ) + AH.orderTop +
          (↑(-(n : ℚ)) : WithTop ℚ) =
          ((↑(n : ℚ) : WithTop ℚ) +
            (↑(-(n : ℚ)) : WithTop ℚ)) + AH.orderTop := by ac_rfl
      _ = (0 : WithTop ℚ) + AH.orderTop := by
        rw [← WithTop.coe_add]
        norm_num
      _ = AH.orderTop := zero_add _
  rw [zero_add, hcancel] at hadd
  exact hadd

/-- A degree-one local scale is literally a single Hahn monomial at its
root. -/
theorem ratFuncAtHahn68_linearRoot_eq_single
    (h0 : k[X]) (a : k) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) :
    ∃ c : k, c ≠ 0 ∧
      ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0) =
        HahnSeries.single (1 : ℚ) c := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by
    simpa [← hlinear] using hroot
  have hcomp : h0.comp (X + C a) = C c * X := by
    apply Polynomial.funext
    intro x
    rw [← hlinear]
    simp only [Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination hca
  refine ⟨c, hc, ?_⟩
  rw [ratFuncAtHahn46_algebraMap, hcomp, map_mul]
  simp [Polynomial.algebraMap_hahnSeries_apply, HahnSeries.C_apply,
    HahnSeries.single_mul_single]

/-- Exact coefficient at the worst possible pole of a coordinate with a
polynomial numerator. -/
theorem localHahn_coeff_neg_of_cleared
    (a c : k) (h0 A0 : k[X]) (A : RatFunc k) (n : ℕ) (hc : c ≠ 0)
    (hsingle :
      ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0) =
        HahnSeries.single (1 : ℚ) c)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * A) :
    (ratFuncAtHahn46 a A).coeff (-(n : ℚ)) =
      (c ^ n)⁻¹ * A0.eval a := by
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 a A
  have hmapped := congrArg (ratFuncAtHahn46 a) hclear
  simp only [map_mul, map_pow, hsingle] at hmapped
  have hcoeff := congrArg (fun x : HahnSeries ℚ k => x.coeff 0) hmapped
  rw [ratFuncAtHahn46_algebraMap_coeff_zero] at hcoeff
  simp only [HahnSeries.single_pow, HahnSeries.coeff_single_mul,
    nsmul_eq_mul, mul_one, zero_sub] at hcoeff
  change A0.eval a = c ^ n * AH.coeff (-(n : ℚ)) at hcoeff
  change AH.coeff (-(n : ℚ)) = (c ^ n)⁻¹ * A0.eval a
  rw [hcoeff]
  field_simp [pow_ne_zero n hc]

/-- The exact first local Newton box for the five depressed sextic
coordinates. -/
theorem SquareConstantLIntegratedLocalRootData68.coordinateOrderBounds
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    let a := T.root
    (↑(-10 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a T.source.A).orderTop ∧
    (↑(-15 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a T.source.B).orderTop ∧
    (↑(-20 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a T.source.C0).orderTop ∧
    (↑(-25 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a T.source.D).orderTop ∧
    (↑(-30 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 a T.source.E).orderTop := by
  dsimp only
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinates hp T.scale_ne_zero hH hp6
  exact ⟨
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedA68 h0 (p.coeff 5) (p.coeff 4)) T.source.A 10
      T.scale_order hA,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3))
      T.source.B 15 T.scale_order hB,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2)) T.source.C0 20 T.scale_order hC,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) T.source.D 25 T.scale_order hD,
    localHahn_orderTop_ge_of_cleared T.root h0
      (localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) T.source.E 30
      T.scale_order hE
  ⟩

/-- Exact worst-pole coefficients of all five depressed sextic coordinates.
These coefficients may vanish; vanishing is exactly the signal that the
corresponding coordinate lies strictly inside the first Newton box. -/
theorem SquareConstantLIntegratedLocalRootData68.coordinateInitialCoeffs
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    ∃ c : k, c ≠ 0 ∧
      (ratFuncAtHahn46 T.root T.source.A).coeff (-10 : ℚ) =
        (c ^ 10)⁻¹ *
          (localClearedA68 h0 (p.coeff 5) (p.coeff 4)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.B).coeff (-15 : ℚ) =
        (c ^ 15)⁻¹ *
          (localClearedB68 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.C0).coeff (-20 : ℚ) =
        (c ^ 20)⁻¹ *
          (localClearedC68 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.D).coeff (-25 : ℚ) =
        (c ^ 25)⁻¹ *
          (localClearedD68 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1)).eval T.root ∧
      (ratFuncAtHahn46 T.root T.source.E).coeff (-30 : ℚ) =
        (c ^ 30)⁻¹ *
          (localClearedE68 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1)
            (p.coeff 0)).eval T.root := by
  obtain ⟨c, hc, hsingle⟩ :=
    ratFuncAtHahn68_linearRoot_eq_single
      h0 T.root T.scale_degree T.root_eq
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.source.clearedCoordinates hp T.scale_ne_zero hH hp6
  refine ⟨c, hc, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedA68 h0 (p.coeff 5) (p.coeff 4)) T.source.A 10 hc
      hsingle hA
  · simpa using localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedB68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3))
      T.source.B 15 hc hsingle hB
  · simpa using localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedC68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2)) T.source.C0 20 hc hsingle hC
  · simpa using localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedD68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1)) T.source.D 25 hc hsingle hD
  · simpa using localHahn_coeff_neg_of_cleared T.root c h0
      (localClearedE68 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0)) T.source.E 30 hc hsingle hE

/-! ## The first lower-row face

The weights of `A,B,C0,D,E` are `2,3,4,5,6`; the local scale has order
one and all five denominator exponents are five times these weights.  The
fourth first integral has top weight nine. -/

/-- A standardized monomial in the five depressed sextic coordinates. -/
def weightedMonomial68 (c : k) (A B C0 D E : HahnSeries ℚ k)
    (aA aB aC aD aE : ℕ) : HahnSeries ℚ k :=
  HahnSeries.C c * A ^ aA * B ^ aB * C0 ^ aC * D ^ aD * E ^ aE

/-- The coefficient at the lower boundary of a five-coordinate weighted
monomial is the corresponding monomial in the five boundary coefficients. -/
theorem weightedMonomial68_coeff_at_weight
    (c : k) (A B C0 D E : HahnSeries ℚ k)
    (aA aB aC aD aE : ℕ) (rho : ℚ)
    (hA : (↑(-2 * rho) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 * rho) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-5 * rho) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 * rho) : WithTop ℚ) ≤ E.orderTop) :
    (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
        (-((2 : ℚ) * aA + 3 * aB + 4 * aC + 5 * aD + 6 * aE) * rho) =
      c * (A.coeff (-2 * rho)) ^ aA * (B.coeff (-3 * rho)) ^ aB *
        (C0.coeff (-4 * rho)) ^ aC * (D.coeff (-5 * rho)) ^ aD *
        (E.coeff (-6 * rho)) ^ aE := by
  have hc : (0 : WithTop ℚ) ≤
      (HahnSeries.C c : HahnSeries ℚ k).orderTop :=
    hahnOrderTop_C_nonneg46 c
  have hAp := hahnOrderTop_pow_lower46 A (-2 * rho) aA hA
  have hBp := hahnOrderTop_pow_lower46 B (-3 * rho) aB hB
  have hCp := hahnOrderTop_pow_lower46 C0 (-4 * rho) aC hC
  have hDp := hahnOrderTop_pow_lower46 D (-5 * rho) aD hD
  have hEp := hahnOrderTop_pow_lower46 E (-6 * rho) aE hE
  have hcA := hahnOrderTop_mul_lower46
    (HahnSeries.C c) (A ^ aA) 0 ((aA : ℚ) * (-2 * rho)) hc hAp
  have hcAB := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA) (B ^ aB)
      (0 + (aA : ℚ) * (-2 * rho)) ((aB : ℚ) * (-3 * rho)) hcA hBp
  have hcABC := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB) (C0 ^ aC)
      ((0 + (aA : ℚ) * (-2 * rho)) + (aB : ℚ) * (-3 * rho))
      ((aC : ℚ) * (-4 * rho)) hcAB hCp
  have hcABCD := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB * C0 ^ aC) (D ^ aD)
      (((0 + (aA : ℚ) * (-2 * rho)) + (aB : ℚ) * (-3 * rho)) +
        (aC : ℚ) * (-4 * rho))
      ((aD : ℚ) * (-5 * rho)) hcABC hDp
  rw [weightedMonomial68]
  rw [show -((2 : ℚ) * aA + 3 * aB + 4 * aC + 5 * aD + 6 * aE) * rho =
      ((((0 + (aA : ℚ) * (-2 * rho)) + (aB : ℚ) * (-3 * rho)) +
        (aC : ℚ) * (-4 * rho)) + (aD : ℚ) * (-5 * rho)) +
        (aE : ℚ) * (-6 * rho) by ring]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB * C0 ^ aC * D ^ aD) (E ^ aE)
      ((((0 + (aA : ℚ) * (-2 * rho)) + (aB : ℚ) * (-3 * rho)) +
        (aC : ℚ) * (-4 * rho)) + (aD : ℚ) * (-5 * rho))
      ((aE : ℚ) * (-6 * rho)) hcABCD hEp]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB * C0 ^ aC) (D ^ aD)
      (((0 + (aA : ℚ) * (-2 * rho)) + (aB : ℚ) * (-3 * rho)) +
        (aC : ℚ) * (-4 * rho)) ((aD : ℚ) * (-5 * rho)) hcABC hDp]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB) (C0 ^ aC)
      ((0 + (aA : ℚ) * (-2 * rho)) + (aB : ℚ) * (-3 * rho))
      ((aC : ℚ) * (-4 * rho)) hcAB hCp]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * A ^ aA) (B ^ aB)
      (0 + (aA : ℚ) * (-2 * rho)) ((aB : ℚ) * (-3 * rho)) hcA hBp]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c) (A ^ aA) 0 ((aA : ℚ) * (-2 * rho)) hc hAp]
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same,
    hahnCoeff_pow_at_lower46 A (-2 * rho) aA hA,
    hahnCoeff_pow_at_lower46 B (-3 * rho) aB hB,
    hahnCoeff_pow_at_lower46 C0 (-4 * rho) aC hC,
    hahnCoeff_pow_at_lower46 D (-5 * rho) aD hD,
    hahnCoeff_pow_at_lower46 E (-6 * rho) aE hE]

/-- A monomial of weighted degree below `target` has no coefficient at the
more negative `-target * rho` face. -/
theorem weightedMonomial68_orderTop_gt
    (c : k) (A B C0 D E : HahnSeries ℚ k)
    (aA aB aC aD aE : ℕ) (rho target : ℚ)
    (hrho : 0 < rho)
    (hA : (↑(-2 * rho) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 * rho) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-5 * rho) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 * rho) : WithTop ℚ) ≤ E.orderTop)
    (hweight : (2 : ℚ) * aA + 3 * aB + 4 * aC + 5 * aD + 6 * aE < target) :
    (↑(-target * rho) : WithTop ℚ) <
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).orderTop := by
  have hc : (0 : WithTop ℚ) ≤
      (HahnSeries.C c : HahnSeries ℚ k).orderTop :=
    hahnOrderTop_C_nonneg46 c
  have hAp := hahnOrderTop_pow_lower46 A (-2 * rho) aA hA
  have hBp := hahnOrderTop_pow_lower46 B (-3 * rho) aB hB
  have hCp := hahnOrderTop_pow_lower46 C0 (-4 * rho) aC hC
  have hDp := hahnOrderTop_pow_lower46 D (-5 * rho) aD hD
  have hEp := hahnOrderTop_pow_lower46 E (-6 * rho) aE hE
  have hcA := hahnOrderTop_mul_lower46
    (HahnSeries.C c) (A ^ aA) 0 ((aA : ℚ) * (-2 * rho)) hc hAp
  have hcAB := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA) (B ^ aB)
      (0 + (aA : ℚ) * (-2 * rho)) ((aB : ℚ) * (-3 * rho)) hcA hBp
  have hcABC := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB) (C0 ^ aC)
      ((0 + (aA : ℚ) * (-2 * rho)) + (aB : ℚ) * (-3 * rho))
      ((aC : ℚ) * (-4 * rho)) hcAB hCp
  have hcABCD := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB * C0 ^ aC) (D ^ aD)
      (((0 + (aA : ℚ) * (-2 * rho)) + (aB : ℚ) * (-3 * rho)) +
        (aC : ℚ) * (-4 * rho))
      ((aD : ℚ) * (-5 * rho)) hcABC hDp
  have hfull := hahnOrderTop_mul_lower46
    (HahnSeries.C c * A ^ aA * B ^ aB * C0 ^ aC * D ^ aD) (E ^ aE)
      ((((0 + (aA : ℚ) * (-2 * rho)) + (aB : ℚ) * (-3 * rho)) +
        (aC : ℚ) * (-4 * rho)) + (aD : ℚ) * (-5 * rho))
      ((aE : ℚ) * (-6 * rho)) hcABCD hEp
  have hstrict : -target * rho <
      ((((0 + (aA : ℚ) * (-2 * rho)) + (aB : ℚ) * (-3 * rho)) +
        (aC : ℚ) * (-4 * rho)) + (aD : ℚ) * (-5 * rho)) +
        (aE : ℚ) * (-6 * rho) := by
    nlinarith
  exact (WithTop.coe_lt_coe.mpr hstrict).trans_le (by
    simpa only [weightedMonomial68] using hfull)

/-- Weight-nine part of the fourth first integral. -/
def firstIntegralFourTopFaceHahn68 (A B C0 D E : HahnSeries ℚ k) :
    HahnSeries ℚ k :=
  weightedMonomial68 (-8 / 27 : k) A B C0 D E 0 3 0 0 0 +
  weightedMonomial68 (-8 / 9 : k) A B C0 D E 2 0 0 1 0 +
  weightedMonomial68 (8 / 3 : k) A B C0 D E 0 1 0 0 1 +
  weightedMonomial68 (8 / 3 : k) A B C0 D E 0 0 1 1 0 +
  weightedMonomial68 (40 / 81 : k) A B C0 D E 3 1 0 0 0 +
  weightedMonomial68 (-16 / 9 : k) A B C0 D E 1 1 1 0 0

/-- All terms of the fourth first integral below weight nine. -/
def firstIntegralFourHigherHahn68
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 zeta A B C0 D E 1 0 0 0 0 +
  weightedMonomial68 (2 * epsilon) A B C0 D E 0 1 0 0 0 +
  weightedMonomial68 (3 * delta) A B C0 D E 0 0 1 0 0 +
  weightedMonomial68 (4 * gamma) A B C0 D E 0 0 0 1 0 +
  weightedMonomial68 (5 * beta) A B C0 D E 0 0 0 0 1 +
  weightedMonomial68 (-(5 / 12 : k) * beta) A B C0 D E 0 2 0 0 0 +
  weightedMonomial68 (-(3 / 4 : k) * delta) A B C0 D E 2 0 0 0 0 +
  weightedMonomial68 ((7 / 12 : k) * L) A B C0 D E 0 0 2 0 0 +
  weightedMonomial68 ((35 / 216 : k) * beta) A B C0 D E 3 0 0 0 0 +
  weightedMonomial68 ((385 / 5184 : k) * L) A B C0 D E 4 0 0 0 0 +
  weightedMonomial68 (-(35 / 72 : k) * L) A B C0 D E 1 2 0 0 0 +
  weightedMonomial68 (-(35 / 72 : k) * L) A B C0 D E 2 0 1 0 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) A B C0 D E 1 0 1 0 0 +
  weightedMonomial68 (-(4 / 3 : k) * gamma) A B C0 D E 1 1 0 0 0 +
  weightedMonomial68 ((7 / 6 : k) * L) A B C0 D E 1 0 0 0 1 +
  weightedMonomial68 ((7 / 6 : k) * L) A B C0 D E 0 1 0 1 0

/-- Exact splitting of the fourth first integral into its weight-nine face
and its strictly lighter terms. -/
theorem firstIntegralFour68_eq_localFaces
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k) :
    firstIntegralFour68 (HahnSeries.C L) A B C0 D E
        (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
        (HahnSeries.C epsilon) (HahnSeries.C zeta) =
      firstIntegralFourTopFaceHahn68 A B C0 D E +
        firstIntegralFourHigherHahn68 L beta gamma delta epsilon zeta
          A B C0 D E := by
  simp only [firstIntegralFour68, firstIntegralFourTopFaceHahn68,
    firstIntegralFourHigherHahn68, weightedMonomial68]
  simp only [map_mul, map_div₀, map_neg, map_ofNat, map_one]
  ring

/-- Every term strictly below weight nine has zero coefficient at the
local exponent `-45`. -/
theorem firstIntegralFourHigherHahn68_coeff_neg45
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-10 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-15 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-20 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-25 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-30 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFourHigherHahn68 L beta gamma delta epsilon zeta
      A B C0 D E).coeff (-45 : ℚ) = 0 := by
  have hA5 : (↑(-2 * (5 : ℚ)) : WithTop ℚ) ≤ A.orderTop := by
    norm_num
    exact hA
  have hB5 : (↑(-3 * (5 : ℚ)) : WithTop ℚ) ≤ B.orderTop := by
    norm_num
    exact hB
  have hC5 : (↑(-4 * (5 : ℚ)) : WithTop ℚ) ≤ C0.orderTop := by
    norm_num
    exact hC
  have hD5 : (↑(-5 * (5 : ℚ)) : WithTop ℚ) ≤ D.orderTop := by
    norm_num
    exact hD
  have hE5 : (↑(-6 * (5 : ℚ)) : WithTop ℚ) ≤ E.orderTop := by
    norm_num
    exact hE
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hw : (2 : ℚ) * aA + 3 * aB + 4 * aC + 5 * aD + 6 * aE < 9) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-45 : ℚ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    have h := weightedMonomial68_orderTop_gt c A B C0 D E
      aA aB aC aD aE 5 9 (by norm_num) hA5 hB5 hC5 hD5 hE5 hw
    norm_num at h
    exact h
  have h1 := hzero zeta 1 0 0 0 0 (by norm_num)
  have h2 := hzero (2 * epsilon) 0 1 0 0 0 (by norm_num)
  have h3 := hzero (3 * delta) 0 0 1 0 0 (by norm_num)
  have h4 := hzero (4 * gamma) 0 0 0 1 0 (by norm_num)
  have h5 := hzero (5 * beta) 0 0 0 0 1 (by norm_num)
  have h6 := hzero (-(5 / 12 : k) * beta) 0 2 0 0 0 (by norm_num)
  have h7 := hzero (-(3 / 4 : k) * delta) 2 0 0 0 0 (by norm_num)
  have h8 := hzero ((7 / 12 : k) * L) 0 0 2 0 0 (by norm_num)
  have h9 := hzero ((35 / 216 : k) * beta) 3 0 0 0 0 (by norm_num)
  have h10 := hzero ((385 / 5184 : k) * L) 4 0 0 0 0 (by norm_num)
  have h11 := hzero (-(35 / 72 : k) * L) 1 2 0 0 0 (by norm_num)
  have h12 := hzero (-(35 / 72 : k) * L) 2 0 1 0 0 (by norm_num)
  have h13 := hzero (-(5 / 6 : k) * beta) 1 0 1 0 0 (by norm_num)
  have h14 := hzero (-(4 / 3 : k) * gamma) 1 1 0 0 0 (by norm_num)
  have h15 := hzero ((7 / 6 : k) * L) 1 0 0 0 1 (by norm_num)
  have h16 := hzero ((7 / 6 : k) * L) 0 1 0 1 0 (by norm_num)
  simp only [firstIntegralFourHigherHahn68, HahnSeries.coeff_add,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, add_zero]

/-- The weight-nine face of the fourth first integral is exactly the
first scalar boundary row. -/
theorem firstIntegralFourTopFaceHahn68_coeff_neg45
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-10 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-15 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-20 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-25 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-30 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFourTopFaceHahn68 A B C0 D E).coeff (-45 : ℚ) =
      (8 / 81 : k) * topRowFour68 (A.coeff (-10 : ℚ))
        (B.coeff (-15 : ℚ)) (C0.coeff (-20 : ℚ))
        (D.coeff (-25 : ℚ)) (E.coeff (-30 : ℚ)) := by
  have hA5 : (↑(-2 * (5 : ℚ)) : WithTop ℚ) ≤ A.orderTop := by
    norm_num
    exact hA
  have hB5 : (↑(-3 * (5 : ℚ)) : WithTop ℚ) ≤ B.orderTop := by
    norm_num
    exact hB
  have hC5 : (↑(-4 * (5 : ℚ)) : WithTop ℚ) ≤ C0.orderTop := by
    norm_num
    exact hC
  have hD5 : (↑(-5 * (5 : ℚ)) : WithTop ℚ) ≤ D.orderTop := by
    norm_num
    exact hD
  have hE5 : (↑(-6 * (5 : ℚ)) : WithTop ℚ) ≤ E.orderTop := by
    norm_num
    exact hE
  have h1 := weightedMonomial68_coeff_at_weight
    (-8 / 27 : k) A B C0 D E 0 3 0 0 0 5 hA5 hB5 hC5 hD5 hE5
  have h2 := weightedMonomial68_coeff_at_weight
    (-8 / 9 : k) A B C0 D E 2 0 0 1 0 5 hA5 hB5 hC5 hD5 hE5
  have h3 := weightedMonomial68_coeff_at_weight
    (8 / 3 : k) A B C0 D E 0 1 0 0 1 5 hA5 hB5 hC5 hD5 hE5
  have h4 := weightedMonomial68_coeff_at_weight
    (8 / 3 : k) A B C0 D E 0 0 1 1 0 5 hA5 hB5 hC5 hD5 hE5
  have h5 := weightedMonomial68_coeff_at_weight
    (40 / 81 : k) A B C0 D E 3 1 0 0 0 5 hA5 hB5 hC5 hD5 hE5
  have h6 := weightedMonomial68_coeff_at_weight
    (-16 / 9 : k) A B C0 D E 1 1 1 0 0 5 hA5 hB5 hC5 hD5 hE5
  have h1' :
      (weightedMonomial68 (-8 / 27 : k) A B C0 D E 0 3 0 0 0).coeff
          (-45 : ℚ) = (-8 / 27 : k) * (B.coeff (-15 : ℚ)) ^ 3 := by
    convert h1 using 1 <;> norm_num
  have h2' :
      (weightedMonomial68 (-8 / 9 : k) A B C0 D E 2 0 0 1 0).coeff
          (-45 : ℚ) = (-8 / 9 : k) * (A.coeff (-10 : ℚ)) ^ 2 *
            D.coeff (-25 : ℚ) := by
    convert h2 using 1 <;> norm_num
  have h3' :
      (weightedMonomial68 (8 / 3 : k) A B C0 D E 0 1 0 0 1).coeff
          (-45 : ℚ) = (8 / 3 : k) * B.coeff (-15 : ℚ) *
            E.coeff (-30 : ℚ) := by
    convert h3 using 1 <;> norm_num
  have h4' :
      (weightedMonomial68 (8 / 3 : k) A B C0 D E 0 0 1 1 0).coeff
          (-45 : ℚ) = (8 / 3 : k) * C0.coeff (-20 : ℚ) *
            D.coeff (-25 : ℚ) := by
    convert h4 using 1 <;> norm_num
  have h5' :
      (weightedMonomial68 (40 / 81 : k) A B C0 D E 3 1 0 0 0).coeff
          (-45 : ℚ) = (40 / 81 : k) * (A.coeff (-10 : ℚ)) ^ 3 *
            B.coeff (-15 : ℚ) := by
    convert h5 using 1 <;> norm_num
  have h6' :
      (weightedMonomial68 (-16 / 9 : k) A B C0 D E 1 1 1 0 0).coeff
          (-45 : ℚ) = (-16 / 9 : k) * A.coeff (-10 : ℚ) *
            B.coeff (-15 : ℚ) * C0.coeff (-20 : ℚ) := by
    convert h6 using 1 <;> norm_num
  simp only [firstIntegralFourTopFaceHahn68, HahnSeries.coeff_add]
  rw [h1', h2', h3', h4', h5', h6']
  simp only [topRowFour68]
  ring

/-- Complete first local initial-form extraction: at exponent `-45`, the
fourth invariant sees exactly the first of the five scalar top rows. -/
theorem firstIntegralFour68_coeff_neg45
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-10 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-15 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-20 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-25 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-30 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFour68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-45 : ℚ) =
      (8 / 81 : k) * topRowFour68 (A.coeff (-10 : ℚ))
        (B.coeff (-15 : ℚ)) (C0.coeff (-20 : ℚ))
        (D.coeff (-25 : ℚ)) (E.coeff (-30 : ℚ)) := by
  rw [firstIntegralFour68_eq_localFaces,
    HahnSeries.coeff_add,
    firstIntegralFourTopFaceHahn68_coeff_neg45 A B C0 D E
      hA hB hC hD hE,
    firstIntegralFourHigherHahn68_coeff_neg45
      L beta gamma delta epsilon zeta A B C0 D E hA hB hC hD hE,
    add_zero]

/-- The first genuine local face forced by a square-source integrated
package: its five worst-pole coefficients satisfy `topRowFour68 = 0`. -/
theorem SquareConstantLIntegratedLocalRootData68.topRowFour_zero
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    topRowFour68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-25 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-30 : ℚ)) = 0 := by
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.A
  let BH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.B
  let CH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.C0
  let DH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.D
  let EH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBounds hp hH hp6
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      l T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4H := congrArg (ratFuncAtHahn46 T.root) hi4
  have hi4H' :
      firstIntegralFour68 (HahnSeries.C l) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i4 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi4H
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-45 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-45 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_neg45
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA hB hC hD hE
  rw [hface] at hcoeff
  have hfactor : (8 / 81 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- The next modular Hahn calculation.  It is deliberately exposed as a
proposition, not assumed: proving this weight-ten identity yields the
second top row from the second exact first integral. -/
def FirstIntegralThreeLocalTopFaceRoute68 : Prop :=
  ∀ (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k),
    (↑(-10 : ℚ) : WithTop ℚ) ≤ A.orderTop →
    (↑(-15 : ℚ) : WithTop ℚ) ≤ B.orderTop →
    (↑(-20 : ℚ) : WithTop ℚ) ≤ C0.orderTop →
    (↑(-25 : ℚ) : WithTop ℚ) ≤ D.orderTop →
    (↑(-30 : ℚ) : WithTop ℚ) ≤ E.orderTop →
    (firstIntegralThree68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-50 : ℚ) =
      (-4 / 243 : k) * topRowThree68 (A.coeff (-10 : ℚ))
        (B.coeff (-15 : ℚ)) (C0.coeff (-20 : ℚ))
        (D.coeff (-25 : ℚ)) (E.coeff (-30 : ℚ))

end ClearedCoordinates68

#print axioms algebraMap_localClearedA68
#print axioms algebraMap_localClearedB68
#print axioms algebraMap_localClearedC68
#print axioms algebraMap_localClearedD68
#print axioms algebraMap_localClearedE68
#print axioms SquareConstantLIntegratedSourceData68.clearedCoordinates
#print axioms localHahn_orderTop_ge_of_cleared
#print axioms ratFuncAtHahn68_linearRoot_eq_single
#print axioms localHahn_coeff_neg_of_cleared
#print axioms SquareConstantLIntegratedLocalRootData68.coordinateOrderBounds
#print axioms SquareConstantLIntegratedLocalRootData68.coordinateInitialCoeffs
#print axioms weightedMonomial68_coeff_at_weight
#print axioms weightedMonomial68_orderTop_gt
#print axioms firstIntegralFour68_coeff_neg45
#print axioms SquareConstantLIntegratedLocalRootData68.topRowFour_zero

end Max11DegreeRoutes
