import Sol610ScaleTwoDegreeZeroLocalPoleScratch

/-! # Finite-order ceiling for the `(6,10)` degree-zero simple pole

Section 4.2 of the degree-zero endgame: a rational function whose
cleared numerator vanishes past its own degree at a simple root of the
linear scale is identically zero, so it cannot have derivative `j/h0`
with `j ≠ 0`.

The bound is finite and explicit.  If the numerator has `natDegree < M`
and vanishes to order `M` at `a` — as a power of `X - C a`, as a power
of the linear scale `h0`, or as `M` iterated derivatives — then it is
the zero polynomial.  No infinite-order identity is assumed.  Later
per-arm modules supply a concrete `M` from frozen heads plus Taylor
mixins.

This is not a closure of any live arm.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section PolynomialCeiling610

variable {k : Type*} [Field k]

/-- A polynomial of degree strictly less than `M` that is divisible by
`(X - a)^M` is zero.  The comparison is `natDegree` against the
multiplicity of a linear factor. -/
theorem polynomial_eq_zero_of_natDegree_lt_of_X_sub_C_pow_dvd610
    (p : k[X]) (a : k) (M : ℕ) (hdeg : p.natDegree < M)
    (hdvd : (X - C a) ^ M ∣ p) : p = 0 := by
  have hpow : ((X - C a) ^ M).natDegree = M := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  exact eq_zero_of_dvd_of_natDegree_lt hdvd (hdeg.trans_eq hpow.symm)

/-- A polynomial of degree strictly less than `M` that is divisible by
the `M`-th power of a degree-one polynomial is zero. -/
theorem polynomial_eq_zero_of_natDegree_lt_of_linear_pow_dvd610
    (p h0 : k[X]) (M : ℕ) (hdegree : h0.natDegree = 1)
    (hdeg : p.natDegree < M) (hdvd : h0 ^ M ∣ p) : p = 0 := by
  have hpow : (h0 ^ M).natDegree = M := by
    rw [natDegree_pow, hdegree, mul_one]
  exact eq_zero_of_dvd_of_natDegree_lt hdvd (hdeg.trans_eq hpow.symm)

variable [CharZero k]

/-- A polynomial of degree strictly less than `M` whose first `M`
iterated derivatives vanish at `a` is zero.  Vanishing of
`derivative^[0], …, derivative^[M-1]` is multiplicity at least `M`. -/
theorem polynomial_eq_zero_of_natDegree_lt_of_iterate_derivative_eval_eq_zero610
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
      exact polynomial_eq_zero_of_natDegree_lt_of_X_sub_C_pow_dvd610 p a
        (M' + 1) hdeg ((le_rootMultiplicity_iff hp).mp hle)

end PolynomialCeiling610

section DegreeZeroPoleCeiling610

variable {k : Type*} [Field k] [CharZero k]

/-- If `h0^n * rho` is the image of the zero polynomial, then `rho = 0`. -/
theorem ratFunc_eq_zero_of_pow_clearing_numerator_eq_zero610
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

/-- The pole-six clearing of a numerator that vanishes past its degree
along a linear scale is the zero rational function. -/
theorem ratFunc_eq_zero_of_poleSix_numerator_degree_lt_linear_order610
    (a : k) (h0 A0 : k[X]) (rho : RatFunc k) (M : ℕ)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho)
    (hdeg : A0.natDegree < M) (hdvd : h0 ^ M ∣ A0) : rho = 0 := by
  have hh0 : h0 ≠ 0 := by
    rintro rfl
    simp at hdegree
  exact ratFunc_eq_zero_of_pow_clearing_numerator_eq_zero610 h0 A0 rho 6
    hh0 hclear
    (polynomial_eq_zero_of_natDegree_lt_of_linear_pow_dvd610 A0 h0 M
      hdegree hdeg hdvd)

/-- Same RatFunc conclusion, with vanishing supplied as iterated
derivatives at the simple root. -/
theorem ratFunc_eq_zero_of_poleSix_numerator_degree_lt_iterate_derivative610
    (a : k) (h0 A0 : k[X]) (rho : RatFunc k) (M : ℕ)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho)
    (hdeg : A0.natDegree < M)
    (hvanish : ∀ n < M, (derivative^[n] A0).eval a = 0) : rho = 0 := by
  have hh0 : h0 ≠ 0 := by
    rintro rfl
    simp at hdegree
  exact ratFunc_eq_zero_of_pow_clearing_numerator_eq_zero610 h0 A0 rho 6
    hh0 hclear
    (polynomial_eq_zero_of_natDegree_lt_of_iterate_derivative_eval_eq_zero610
      A0 a M hdeg hvanish)

/-- A zero rational function cannot have the landed simple-pole
derivative `C j / h0` with `j ≠ 0`. -/
theorem localLinearPoleSix_simplePole_contradicts_eq_zero610
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

/-- Ceiling along a linear scale: if `h0^6 * rho` is polynomial of
degree `< M` and `h0^M` divides that numerator, then the simple-pole
equation `rho' = C j / h0` with `j ≠ 0` is impossible. -/
theorem localLinearPoleSix_ceiling_of_linear_order610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k) (M : ℕ)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hdeg : A0.natDegree < M) (hdvd : h0 ^ M ∣ A0) (hj : j ≠ 0) :
    False :=
  localLinearPoleSix_simplePole_contradicts_eq_zero610 j h0 rho hdegree
    hderiv hj
    (ratFunc_eq_zero_of_poleSix_numerator_degree_lt_linear_order610 a
      h0 A0 rho M hdegree hroot hclear hdeg hdvd)

/-- Ceiling with vanishing supplied as iterated derivatives.  A later
arm that evaluates the first `M` Taylor coefficients of the pole-six
numerator at `a` and knows `natDegree A0 < M` obtains `False`. -/
theorem localLinearPoleSix_ceiling_of_iterate_derivative_eval_eq_zero610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k) (M : ℕ)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hdeg : A0.natDegree < M)
    (hvanish : ∀ n < M, (derivative^[n] A0).eval a = 0)
    (hj : j ≠ 0) : False :=
  localLinearPoleSix_simplePole_contradicts_eq_zero610 j h0 rho hdegree
    hderiv hj
    (ratFunc_eq_zero_of_poleSix_numerator_degree_lt_iterate_derivative610
      a h0 A0 rho M hdegree hroot hclear hdeg hvanish)

#print axioms polynomial_eq_zero_of_natDegree_lt_of_X_sub_C_pow_dvd610
#print axioms polynomial_eq_zero_of_natDegree_lt_of_linear_pow_dvd610
#print axioms polynomial_eq_zero_of_natDegree_lt_of_iterate_derivative_eval_eq_zero610
#print axioms ratFunc_eq_zero_of_pow_clearing_numerator_eq_zero610
#print axioms ratFunc_eq_zero_of_poleSix_numerator_degree_lt_linear_order610
#print axioms ratFunc_eq_zero_of_poleSix_numerator_degree_lt_iterate_derivative610
#print axioms localLinearPoleSix_simplePole_contradicts_eq_zero610
#print axioms localLinearPoleSix_ceiling_of_linear_order610
#print axioms localLinearPoleSix_ceiling_of_iterate_derivative_eval_eq_zero610

end DegreeZeroPoleCeiling610

end Max11DegreeRoutes
