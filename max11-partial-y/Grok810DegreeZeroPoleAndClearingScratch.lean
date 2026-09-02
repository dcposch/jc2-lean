import Grok810DegreeZeroSourceWrapperScratch
import LowScale68ScaleTwoLocalDerivativeRowTwo

/-! # Pole-one obstruction and source-homogeneous clearing of `(8,10)` degree zero

Lanes Z4 and Z5 of the `(8,10)` chamber map, section 4.2.  Lane Z3 has
already identified the ordinary derivative of the grouped primitive, on
a literal `(8,10)` source, as the simple pole `ρ' = C(j)/h₀`.  This file
records the analytic consumers of that simple pole, and the exact
source-homogeneous clearing bound of the Z1 primitive.

**Z4.** At a linear root `a` of `h₀`, a remaining pole-`n` clearing with
`n ≠ 0` forces the exponent-`-n` head to vanish (per-order obstruction).
The computed remaining order matching Z3 is `1`: if `h₀ ρ` is
polynomial, then the numerator vanishes at `a`.  The second interface is
the finite-order ceiling: if that numerator has `natDegree < M` and
`h₀^M` divides it, then `ρ` is the zero polynomial, hence cannot have
derivative `C(j)/h₀` with `j ≠ 0`.  The holomorphic companion is the
same ceiling with `M` equal to the remaining clearing: `h₀` divides the
numerator, so `ρ` itself is a polynomial, and evaluating
`h₀ · ρ' = C(j)` at `a` forces `j = 0`.

These lemmas consume a *remaining* pole-one clearing.  They do not claim
that the raw grouped primitive is pole-one.

**Z5.** The Z1 primitive is homogeneous of weight `17` in the CAS
grading `L:1, A:2, …, G0:8`.  The octic depression centre is
`a₇/(8 h^7)`, and every landed `_eq_cleared` identity divides by
`h^{7d}` at depth `d`.  A weight-`17` polynomial in those coordinates is
therefore a polynomial over `h^{119}`.  The grouped integer scale of the
displayed denominators is `2^{28} = 268435456`.  Neither `119` nor
`268435456` is copied from the `(6,10)` clearing `75` or the Pi tower
`112 = 7 · 16`.  The generic tower ceiling after the order-`1` pole is
`119 - 1 = 118`.

No source numerator is expanded, no jet peel is performed, and no
chamber is closed.  After degree `0` there is no unused Keller row.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Z5. Weight, integer scale, clearing power, and tower ceiling -/

/-- Weighted degree of the grouped `(8,10)` degree-zero primitive. -/
def degreeZeroPrimitiveWeight810 : ℕ := 17

/-- Source `h`-adic step of one depression depth: the octic centre is
`a₇/(8 h^7)`. -/
def degreeZeroCoordinateClearingStep810 : ℕ := 7

/-- Source-homogeneous clearing of a weight-`17` polynomial in
coordinates of denominator `h^{7d}`. -/
def degreeZeroSourceClearingPower810 : ℕ := 119

/-- Remaining pole order matching the Z3 simple pole `ρ' = C(j)/h₀`. -/
def degreeZeroPoleOrder810 : ℕ := 1

/-- Generic remaining `h`-degree after the order-`1` pole:
`119 - 1 = 118`.  This is not an extracted jet vanishing. -/
def degreeZeroTowerCeiling810 : ℕ := 118

/-- Least common multiple of the displayed group denominators
`2^{28}, 2^{20}, 2^{18}, 2^{14}, 2^{13}, 2^{12}, 2^{9}`. -/
def degreeZeroGroupedIntegerScale810 : ℕ := 268435456

theorem degreeZeroPrimitiveWeight810_eq :
    degreeZeroPrimitiveWeight810 = 17 := rfl

theorem degreeZeroCoordinateClearingStep810_eq :
    degreeZeroCoordinateClearingStep810 = 7 := rfl

theorem degreeZeroSourceClearingPower810_eq :
    degreeZeroSourceClearingPower810 = 119 := rfl

theorem degreeZeroPoleOrder810_eq :
    degreeZeroPoleOrder810 = 1 := rfl

theorem degreeZeroTowerCeiling810_eq :
    degreeZeroTowerCeiling810 = 118 := rfl

theorem degreeZeroGroupedIntegerScale810_eq :
    degreeZeroGroupedIntegerScale810 = 268435456 := rfl

theorem degreeZeroSourceClearingPower810_eq_mul :
    degreeZeroSourceClearingPower810 =
      degreeZeroCoordinateClearingStep810 * degreeZeroPrimitiveWeight810 :=
  rfl

theorem degreeZeroTowerCeiling810_eq_sub :
    degreeZeroTowerCeiling810 =
      degreeZeroSourceClearingPower810 - degreeZeroPoleOrder810 :=
  rfl

theorem degreeZeroGroupedIntegerScale810_eq_pow :
    degreeZeroGroupedIntegerScale810 = 2 ^ 28 := rfl

theorem degreeZeroSourceClearingPower810_ne_seventyFive :
    degreeZeroSourceClearingPower810 ≠ 75 := by decide

theorem degreeZeroSourceClearingPower810_ne_oneHundredTwelve :
    degreeZeroSourceClearingPower810 ≠ 112 := by decide

theorem degreeZeroCoordinateClearingPow_depth_two810 :
    degreeZeroCoordinateClearingStep810 * 2 = 14 := rfl

theorem degreeZeroCoordinateClearingPow_depth_three810 :
    degreeZeroCoordinateClearingStep810 * 3 = 21 := rfl

theorem degreeZeroCoordinateClearingPow_depth_four810 :
    degreeZeroCoordinateClearingStep810 * 4 = 28 := rfl

theorem degreeZeroCoordinateClearingPow_depth_eight810 :
    degreeZeroCoordinateClearingStep810 * 8 = 56 := rfl

theorem degreeZeroCoordinateClearingPow_depth_ten810 :
    degreeZeroCoordinateClearingStep810 * 10 = 70 := rfl

section DegreeZeroClearingBookkeeping810

variable {F : Type*} [Field F] [CharZero F]

theorem octicDepressionR810_eq_center_pow
    (h a7 : F) :
    octicDepressionR810 h a7 =
      a7 / (8 * h ^ degreeZeroCoordinateClearingStep810) := rfl

theorem degreeZeroGroupedIntegerScale810_ne_zero :
    (degreeZeroGroupedIntegerScale810 : F) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

/-- Landed depth-`2` octic clearing is `h^{14} = h^{7·2}`. -/
theorem depressedA810_eq_cleared_weight
    (h a7 a6 : F) (hh : h ≠ 0) :
    depressedA810 h (octicDepressionR810 h a7) a7 a6 =
      (16 * a6 * h ^ 8 - 7 * a7 ^ 2) /
        (16 * h ^ (degreeZeroCoordinateClearingStep810 * 2)) := by
  simpa [degreeZeroCoordinateClearingStep810] using
    depressedA810_eq_cleared h a7 a6 hh

/-- Landed depth-`3` octic clearing is `h^{21} = h^{7·3}`. -/
theorem depressedB810_eq_cleared_weight
    (h a7 a6 a5 : F) (hh : h ≠ 0) :
    depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
      (32 * a5 * h ^ 16 - 24 * a6 * a7 * h ^ 8 + 7 * a7 ^ 3) /
        (32 * h ^ (degreeZeroCoordinateClearingStep810 * 3)) := by
  simpa [degreeZeroCoordinateClearingStep810] using
    depressedB810_eq_cleared h a7 a6 a5 hh

/-- Landed depth-`8` octic clearing is `h^{56} = h^{7·8}`. -/
theorem depressedG810_eq_cleared_weight
    (h a7 a6 a5 a4 a3 a2 a1 a0 : F) (hh : h ≠ 0) :
    depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 a0 =
      (16777216 * a0 * h ^ 56 - 2097152 * a1 * a7 * h ^ 48 +
          262144 * a2 * a7 ^ 2 * h ^ 40 - 32768 * a3 * a7 ^ 3 * h ^ 32 +
          4096 * a4 * a7 ^ 4 * h ^ 24 - 512 * a5 * a7 ^ 5 * h ^ 16 +
          64 * a6 * a7 ^ 6 * h ^ 8 - 7 * a7 ^ 8) /
        (16777216 * h ^ (degreeZeroCoordinateClearingStep810 * 8)) := by
  simpa [degreeZeroCoordinateClearingStep810] using
    depressedG810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 a0 hh

/-- Landed depth-`10` decic clearing is `h^{70} = h^{7·10}`. -/
theorem depressedX810_eq_cleared_weight
    (h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    depressedX810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2
        b1 b0 =
      (-9 * a7 ^ 10 + 2 * lambda * a7 ^ 9 * h ^ 7 +
          64 * a7 ^ 8 * b8 * h ^ 6 - 512 * a7 ^ 7 * b7 * h ^ 14 +
          4096 * a7 ^ 6 * b6 * h ^ 22 - 32768 * a7 ^ 5 * b5 * h ^ 30 +
          262144 * a7 ^ 4 * b4 * h ^ 38 - 2097152 * a7 ^ 3 * b3 * h ^ 46 +
          16777216 * a7 ^ 2 * b2 * h ^ 54 - 134217728 * a7 * b1 * h ^ 62 +
          1073741824 * b0 * h ^ 70) /
        (1073741824 * h ^ (degreeZeroCoordinateClearingStep810 * 10)) := by
  simpa [degreeZeroCoordinateClearingStep810] using
    depressedX810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda
      hh hN

/-- Every displayed group denominator divides the grouped integer scale. -/
theorem degreeZeroGroupedIntegerScale810_dvd_group_denominators :
    512 ∣ degreeZeroGroupedIntegerScale810 ∧
      4096 ∣ degreeZeroGroupedIntegerScale810 ∧
      8192 ∣ degreeZeroGroupedIntegerScale810 ∧
      16384 ∣ degreeZeroGroupedIntegerScale810 ∧
      262144 ∣ degreeZeroGroupedIntegerScale810 ∧
      1048576 ∣ degreeZeroGroupedIntegerScale810 ∧
      268435456 ∣ degreeZeroGroupedIntegerScale810 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end DegreeZeroClearingBookkeeping810

#print axioms degreeZeroSourceClearingPower810_eq_mul
#print axioms degreeZeroTowerCeiling810_eq_sub
#print axioms degreeZeroGroupedIntegerScale810_eq_pow
#print axioms octicDepressionR810_eq_center_pow
#print axioms depressedA810_eq_cleared_weight
#print axioms depressedB810_eq_cleared_weight
#print axioms depressedG810_eq_cleared_weight
#print axioms depressedX810_eq_cleared_weight
#print axioms degreeZeroGroupedIntegerScale810_dvd_group_denominators
#print axioms degreeZeroGroupedIntegerScale810_ne_zero

/-! ## Z4. Per-order head obstruction -/

section DegreeZeroLocalPole810

variable {k : Type*} [Field k] [CharZero k]

local instance degreeZeroLocalPoleHahnCharZero810 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Per-order head obstruction.  If `h0^n ρ` is polynomial for `n ≠ 0`
and `ρ'` is the simple pole `C j / h0`, then the exponent-`-n` Hahn
coefficient of `ρ` vanishes, so the numerator evaluates to zero at the
linear root.  The relevant derivative coefficient is at exponent
`-(n+1)`, which is distinct from `-1`. -/
theorem localLinearPole_head_eval_zero_of_deriv_eq_simplePole810
    (n : ℕ) (hn : n ≠ 0) (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 := by
  obtain ⟨c, hc, hsingle, hscaleDeriv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hrhoBoundary := localHahn_coeff_neg_of_cleared a c h0 A0 rho n hc
    hsingle hclear
  have hderivBoundary := localHahn_deriv_coeff_neg_succ_of_cleared
    a c h0 A0 rho n hc hsingle hscaleDeriv hclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hderiv
  have hne : (-(n : ℚ) - 1) ≠ -(1 : ℚ) := by
    intro h
    have : -(n : ℚ) = 0 := by linear_combination h
    exact hn (Nat.cast_eq_zero.mp (neg_eq_zero.mp this))
  have hderivFar :
      (ratFuncAtHahn46 a (Differential.deriv rho)).coeff
        (-(n : ℚ) - 1) = 0 := by
    have hcoeff := congrArg
      (fun z : HahnSeries ℚ k ↦ z.coeff (-(n : ℚ) - 1)) hmapped
    simpa only [div_eq_mul_inv, map_mul, map_inv₀, ratFuncAtHahn46_C,
      hsingle, HahnSeries.inv_single, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne hne,
      smul_zero] using hcoeff
  have hrhoZero : (ratFuncAtHahn46 a rho).coeff (-(n : ℚ)) = 0 := by
    have hnC : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [hderivFar, neg_mul] at hderivBoundary
    have hprod :
        (n : k) * (ratFuncAtHahn46 a rho).coeff (-(n : ℚ)) = 0 :=
      neg_eq_zero.mp hderivBoundary.symm
    exact (mul_eq_zero.mp hprod).resolve_left hnC
  rw [hrhoZero] at hrhoBoundary
  have hcinv : (c ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero n hc)
  exact (mul_eq_zero.mp hrhoBoundary.symm).resolve_left hcinv

/-- Order-one specialization: a rational function cleared by exactly one
power of a linear local parameter cannot have a nonzero exponent-`-1`
head when its derivative is a simple pole. -/
theorem localLinearPoleOne_head_eval_zero_of_deriv_eq_simplePole810
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ degreeZeroPoleOrder810 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 :=
  localLinearPole_head_eval_zero_of_deriv_eq_simplePole810
    degreeZeroPoleOrder810 (by decide) a j h0 A0 rho hdegree hroot
    hclear hderiv

#print axioms localLinearPole_head_eval_zero_of_deriv_eq_simplePole810
#print axioms localLinearPoleOne_head_eval_zero_of_deriv_eq_simplePole810

end DegreeZeroLocalPole810

/-! ## Z4. Finite-order ceiling, two interfaces -/

section PolynomialCeiling810

variable {k : Type*} [Field k]

theorem polynomial_eq_zero_of_natDegree_lt_of_X_sub_C_pow_dvd810
    (p : k[X]) (a : k) (M : ℕ) (hdeg : p.natDegree < M)
    (hdvd : (X - C a) ^ M ∣ p) : p = 0 := by
  have hpow : ((X - C a) ^ M).natDegree = M := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  exact eq_zero_of_dvd_of_natDegree_lt hdvd (hdeg.trans_eq hpow.symm)

theorem polynomial_eq_zero_of_natDegree_lt_of_linear_pow_dvd810
    (p h0 : k[X]) (M : ℕ) (hdegree : h0.natDegree = 1)
    (hdeg : p.natDegree < M) (hdvd : h0 ^ M ∣ p) : p = 0 := by
  have hpow : (h0 ^ M).natDegree = M := by
    rw [natDegree_pow, hdegree, mul_one]
  exact eq_zero_of_dvd_of_natDegree_lt hdvd (hdeg.trans_eq hpow.symm)

variable [CharZero k]

theorem polynomial_eq_zero_of_natDegree_lt_of_iterate_derivative_eval_eq_zero810
    (p : k[X]) (a : k) (M : ℕ) (hdeg : p.natDegree < M)
    (hvanish : ∀ n < M, (derivative^[n] p).eval a = 0) : p = 0 := by
  match M with
  | 0 => cases hdeg
  | M' + 1 =>
    by_cases hp : p = 0
    · exact hp
    · have hroot : ∀ m ≤ M', (derivative^[m] p).IsRoot a := by
        intro m hm
        exact hvanish m (Nat.lt_succ_of_le hm)
      have hle : M' + 1 ≤ p.rootMultiplicity a :=
        Nat.succ_le_of_lt
          (lt_rootMultiplicity_of_isRoot_iterate_derivative hp hroot)
      exact polynomial_eq_zero_of_natDegree_lt_of_X_sub_C_pow_dvd810 p a
        (M' + 1) hdeg ((le_rootMultiplicity_iff hp).mp hle)

end PolynomialCeiling810

section DegreeZeroPoleCeiling810

variable {k : Type*} [Field k] [CharZero k]

theorem ratFunc_eq_zero_of_pow_clearing_numerator_eq_zero810
    (h0 A0 : k[X]) (rho : RatFunc k) (n : ℕ) (hh0 : h0 ≠ 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hA0 : A0 = 0) : rho = 0 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpow : hRF ^ n ≠ 0 := pow_ne_zero n hhRF
  have hzero : hRF ^ n * rho = 0 := by
    rw [← hclear, hA0, map_zero]
  exact (mul_eq_zero.mp hzero).resolve_left hpow

theorem ratFunc_eq_zero_of_poleOne_numerator_degree_lt_linear_order810
    (a : k) (h0 A0 : k[X]) (rho : RatFunc k) (M : ℕ)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ degreeZeroPoleOrder810 * rho)
    (hdeg : A0.natDegree < M) (hdvd : h0 ^ M ∣ A0) : rho = 0 := by
  have hh0 : h0 ≠ 0 := by
    rintro rfl
    simp at hdegree
  exact ratFunc_eq_zero_of_pow_clearing_numerator_eq_zero810 h0 A0 rho
    degreeZeroPoleOrder810 hh0 hclear
    (polynomial_eq_zero_of_natDegree_lt_of_linear_pow_dvd810 A0 h0 M
      hdegree hdeg hdvd)

theorem ratFunc_eq_zero_of_poleOne_numerator_degree_lt_iterate_derivative810
    (a : k) (h0 A0 : k[X]) (rho : RatFunc k) (M : ℕ)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ degreeZeroPoleOrder810 * rho)
    (hdeg : A0.natDegree < M)
    (hvanish : ∀ n < M, (derivative^[n] A0).eval a = 0) : rho = 0 := by
  have hh0 : h0 ≠ 0 := by
    rintro rfl
    simp at hdegree
  exact ratFunc_eq_zero_of_pow_clearing_numerator_eq_zero810 h0 A0 rho
    degreeZeroPoleOrder810 hh0 hclear
    (polynomial_eq_zero_of_natDegree_lt_of_iterate_derivative_eval_eq_zero810
      A0 a M hdeg hvanish)

/-- A zero rational function cannot have the landed simple-pole
derivative `C j / h0` with `j ≠ 0`. -/
theorem localLinearPoleOne_simplePole_contradicts_eq_zero810
    (j : k) (h0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) (hrho : rho = 0) : False := by
  have hh0 : h0 ≠ 0 := by
    rintro rfl
    simp at hdegree
  have hhRF : algebraMap k[X] (RatFunc k) h0 ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh0
  have hpole : RatFunc.C j / algebraMap k[X] (RatFunc k) h0 = 0 := by
    have hz : (0 : RatFunc k) =
        algebraMap k[X] (RatFunc k) (0 : k[X]) :=
      (map_zero (algebraMap k[X] (RatFunc k))).symm
    rw [← hderiv, hrho, hz, GCD369RatFuncDerivative, derivative_zero,
      map_zero]
  have hjC : RatFunc.C j = RatFunc.C 0 := by
    simpa using (div_eq_zero_iff.mp hpole).resolve_right hhRF
  exact hj (RatFunc.C_injective hjC)

/-- Ceiling along a linear scale: if `h0 · ρ` is polynomial of degree
`< M` and `h0^M` divides that numerator, then the simple-pole equation
`ρ' = C j / h0` with `j ≠ 0` is impossible. -/
theorem localLinearPoleOne_ceiling_of_linear_order810
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k) (M : ℕ)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ degreeZeroPoleOrder810 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hdeg : A0.natDegree < M) (hdvd : h0 ^ M ∣ A0) (hj : j ≠ 0) :
    False :=
  localLinearPoleOne_simplePole_contradicts_eq_zero810 j h0 rho hdegree
    hderiv hj
    (ratFunc_eq_zero_of_poleOne_numerator_degree_lt_linear_order810 a
      h0 A0 rho M hdegree hroot hclear hdeg hdvd)

/-- Ceiling with vanishing supplied as iterated derivatives. -/
theorem localLinearPoleOne_ceiling_of_iterate_derivative_eval_eq_zero810
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k) (M : ℕ)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ degreeZeroPoleOrder810 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hdeg : A0.natDegree < M)
    (hvanish : ∀ n < M, (derivative^[n] A0).eval a = 0)
    (hj : j ≠ 0) : False :=
  localLinearPoleOne_simplePole_contradicts_eq_zero810 j h0 rho hdegree
    hderiv hj
    (ratFunc_eq_zero_of_poleOne_numerator_degree_lt_iterate_derivative810
      a h0 A0 rho M hdegree hroot hclear hdeg hvanish)

/-- Cancel the remaining pole-one clearing.  The remaining factor *is*
`ρ`. -/
theorem algebraMap_cancel_one_of_one_clearing810
    (h0 Q1 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hquot :
      algebraMap k[X] (RatFunc k) (h0 ^ degreeZeroPoleOrder810 * Q1) =
        (algebraMap k[X] (RatFunc k) h0) ^ degreeZeroPoleOrder810 *
          rho) :
    algebraMap k[X] (RatFunc k) Q1 = rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero degreeZeroPoleOrder810 hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k)
          (h0 ^ degreeZeroPoleOrder810 * Q1) =
        hRF ^ degreeZeroPoleOrder810 *
          algebraMap k[X] (RatFunc k) Q1 := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ degreeZeroPoleOrder810 * algebraMap k[X] (RatFunc k) Q1 =
        algebraMap k[X] (RatFunc k)
          (h0 ^ degreeZeroPoleOrder810 * Q1) := hmapPow.symm
    _ = hRF ^ degreeZeroPoleOrder810 * rho := hquot

/-- A rational function that is the image of a polynomial cannot have
derivative `C j / h0` with `j ≠ 0`: evaluating `h0 * (remaining)' = C j`
at the simple root forces `j = 0`. -/
theorem localLinearPoleZero_C_eq_zero_of_deriv_eq_simplePole810
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 = rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 := by
  have hhRF : algebraMap k[X] (RatFunc k) h0 ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh0
  have hderivA :
      algebraMap k[X] (RatFunc k) (derivative A0) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hderiv, ← hclear, GCD369RatFuncDerivative]
  have hpoly : h0 * derivative A0 = Polynomial.C j := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    rw [map_mul, hderivA, mul_div_cancel₀ _ hhRF]
    simp only [RatFunc.algebraMap_C]
  have heval := congrArg (fun p : k[X] ↦ p.eval a) hpoly
  have heval' : (0 : k) = j := by
    simpa [hroot, Polynomial.eval_mul, Polynomial.eval_C] using heval
  exact heval'.symm

/-- If `h0` divides the pole-one numerator, the remaining factor is `ρ`
itself, so the simple-pole equation forces `j = 0`. -/
theorem localLinearPoleOne_of_pow_one_dvd_simplePole_eval810
    (a j : k) (h0 A0 Q1 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hroot : h0.eval a = 0)
    (hA : A0 = h0 ^ degreeZeroPoleOrder810 * Q1)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ degreeZeroPoleOrder810 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 :=
  localLinearPoleZero_C_eq_zero_of_deriv_eq_simplePole810 a j h0 Q1 rho
    hh0 hroot
    (algebraMap_cancel_one_of_one_clearing810 h0 Q1 rho hh0
      (by simpa [hA] using hclear))
    hderiv

/-- Same holomorphic remainder, with `j ≠ 0`, is False. -/
theorem localLinearPoleOne_of_pow_one_dvd_simplePole_ne_zero810
    (a j : k) (h0 A0 Q1 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hroot : h0.eval a = 0)
    (hA : A0 = h0 ^ degreeZeroPoleOrder810 * Q1)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ degreeZeroPoleOrder810 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False :=
  hj (localLinearPoleOne_of_pow_one_dvd_simplePole_eval810 a j h0 A0 Q1
    rho hh0 hroot hA hclear hderiv)

/-- Source-facing form of the holomorphic ceiling: `h0` divides the
pole-one numerator, so a simple pole with `j ≠ 0` is impossible. -/
theorem localLinearPoleOne_of_linear_dvd_simplePole_ne_zero810
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hdvd : h0 ^ degreeZeroPoleOrder810 ∣ A0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ degreeZeroPoleOrder810 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  have hh0 : h0 ≠ 0 := by
    rintro rfl
    simp at hdegree
  obtain ⟨Q1, hQ1⟩ := hdvd
  exact localLinearPoleOne_of_pow_one_dvd_simplePole_ne_zero810 a j h0
    A0 Q1 rho hh0 hroot hQ1 hclear hderiv hj

#print axioms polynomial_eq_zero_of_natDegree_lt_of_X_sub_C_pow_dvd810
#print axioms polynomial_eq_zero_of_natDegree_lt_of_linear_pow_dvd810
#print axioms polynomial_eq_zero_of_natDegree_lt_of_iterate_derivative_eval_eq_zero810
#print axioms ratFunc_eq_zero_of_pow_clearing_numerator_eq_zero810
#print axioms ratFunc_eq_zero_of_poleOne_numerator_degree_lt_linear_order810
#print axioms ratFunc_eq_zero_of_poleOne_numerator_degree_lt_iterate_derivative810
#print axioms localLinearPoleOne_simplePole_contradicts_eq_zero810
#print axioms localLinearPoleOne_ceiling_of_linear_order810
#print axioms localLinearPoleOne_ceiling_of_iterate_derivative_eval_eq_zero810
#print axioms algebraMap_cancel_one_of_one_clearing810
#print axioms localLinearPoleZero_C_eq_zero_of_deriv_eq_simplePole810
#print axioms localLinearPoleOne_of_pow_one_dvd_simplePole_eval810
#print axioms localLinearPoleOne_of_pow_one_dvd_simplePole_ne_zero810
#print axioms localLinearPoleOne_of_linear_dvd_simplePole_ne_zero810

end DegreeZeroPoleCeiling810

end Max11DegreeRoutes
