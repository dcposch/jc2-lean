import LowScale46AlignedComponentEndgame

/-! # Literal source-to-differential bridge for `(4,6)`

This module begins the remaining source handoff.  It maps a genuine
coefficient-polynomial Jacobian into the standard differential field `k(x)`
and proves the exact chain rule for the common affine depression.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SourceBracket

variable {k : Type*} [Field k] [CharZero k]

/-- The standard quotient-rule differential, regarded as a `k`-derivation.
The public differential instance already proves that every scalar in `k` is
constant; this wrapper only exposes the linearity expected by the normal-form
API. -/
noncomputable def ratFuncDerivativeLinear46 : RatFunc k →ₗ[k] RatFunc k where
  toFun := fun x => Differential.deriv x
  map_add' x y := by
    letI : Algebra ℤ (RatFunc k) := Ring.toIntAlgebra (RatFunc k)
    exact Differential.deriv.map_add x y
  map_smul' c x := by
    letI : Algebra ℤ (RatFunc k) := Ring.toIntAlgebra (RatFunc k)
    have hc : Differential.deriv (algebraMap k (RatFunc k) c) = 0 := by
      have hp := GCD369RatFuncDerivative (C c : k[X])
      simpa using hp
    rw [Algebra.smul_def, Algebra.smul_def, Derivation.leibniz, hc]
    simp

/-- The `k`-derivation form of the selected standard derivative on `k(x)`. -/
noncomputable def ratFuncDerivation46 :
    Derivation k (RatFunc k) (RatFunc k) := by
  letI : Algebra ℤ (RatFunc k) := Ring.toIntAlgebra (RatFunc k)
  exact Derivation.mk' ratFuncDerivativeLinear46 (by
    intro x y
    exact Differential.deriv.leibniz x y)

@[simp]
theorem ratFuncDerivation46_apply (x : RatFunc k) :
    ratFuncDerivation46 x = Differential.deriv x := rfl

theorem ratFuncDerivation46_polynomial (p : k[X]) :
    ratFuncDerivation46 (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (RatFunc k) p.derivative := by
  rw [ratFuncDerivation46_apply, GCD369RatFuncDerivative]

theorem coefficientDeriv_ratFuncDerivation46 (p : (RatFunc k)[X]) :
    coefficientDeriv ratFuncDerivation46 p = Differential.mapCoeffs p := by
  ext n
  simp [coeff_coefficientDeriv, ratFuncDerivation46_apply,
    Differential.coeff_mapCoeffs]

/-- View an outer polynomial in `y` with coefficients in `k[x]` as a
polynomial over the rational function field `k(x)`. -/
def sourceToRatFunc46 (p : k[X][X]) : (RatFunc k)[X] :=
  p.map (algebraMap k[X] (RatFunc k))

/-- The literal source Jacobian maps to the differential polynomial bracket
for the standard quotient-rule differential on `k(x)`. -/
theorem differentialJacobian_sourceToRatFunc46
    (p q : k[X][X]) (j : k)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    differentialJacobian ratFuncDerivation46
        (sourceToRatFunc46 p)
        (sourceToRatFunc46 q) = C (RatFunc.C j) := by
  have hmap := GCD369MapSourceBracket
    (L := RatFunc k) p q (C j) hD
  change Differential.mapCoeffs (sourceToRatFunc46 p) *
      derivative (sourceToRatFunc46 q) -
      derivative (sourceToRatFunc46 p) *
        Differential.mapCoeffs (sourceToRatFunc46 q) = C (RatFunc.C j)
  simpa [sourceToRatFunc46] using hmap

/-- After `y=(z-r)/h`, the differential bracket is exactly divided by `h`.
This is the source-facing chain-rule identity needed by the depressed normal
form, with no assumption that the depression is polynomial. -/
theorem differentialJacobian_affineDepress_sourceToRatFunc46
    (p q : k[X][X]) (j : k) (h r : RatFunc k) (hh : h ≠ 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    differentialJacobian ratFuncDerivation46
        (affineDepress46 h r (sourceToRatFunc46 p))
        (affineDepress46 h r (sourceToRatFunc46 q)) =
      C (RatFunc.C j / h) := by
  have hsource := differentialJacobian_sourceToRatFunc46 p q j hD
  have haffine := GCD369AffineBracket
    (sourceToRatFunc46 p) (sourceToRatFunc46 q) h r (RatFunc.C j) hh
    (by
      rw [differentialJacobian,
        coefficientDeriv_ratFuncDerivation46,
        coefficientDeriv_ratFuncDerivation46] at hsource
      exact hsource)
  have ht : (X - C r) * C h⁻¹ = C h⁻¹ * (X - C r) := by ring
  change Differential.mapCoeffs
        ((sourceToRatFunc46 p).comp ((X - C r) * C h⁻¹)) *
      derivative ((sourceToRatFunc46 q).comp ((X - C r) * C h⁻¹)) -
      derivative ((sourceToRatFunc46 p).comp ((X - C r) * C h⁻¹)) *
        Differential.mapCoeffs
          ((sourceToRatFunc46 q).comp ((X - C r) * C h⁻¹)) =
      C (RatFunc.C j / h)
  rw [ht]
  exact haffine

section RawCoefficientForms

/-- A degree-four mapped source with displayed leading coefficient is exactly
the raw quartic used by the depression calculation. -/
theorem sourceToRatFunc46_eq_rawQuartic
    (p : k[X][X]) (h : RatFunc k) (hp : p.natDegree = 4)
    (htop : algebraMap k[X] (RatFunc k) (p.coeff 4) = h ^ 4) :
    sourceToRatFunc46 p = rawQuartic46 h
      (algebraMap k[X] (RatFunc k) (p.coeff 3))
      (algebraMap k[X] (RatFunc k) (p.coeff 2))
      (algebraMap k[X] (RatFunc k) (p.coeff 1))
      (algebraMap k[X] (RatFunc k) (p.coeff 0)) := by
  ext n
  by_cases hn : n ≤ 4
  · interval_cases n <;>
      simp [sourceToRatFunc46, rawQuartic46, htop, coeff_add, coeff_C,
        coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow] <;>
      rw [← Polynomial.C_pow, coeff_C] <;> simp
  · have hn4 : 4 < n := by omega
    have hz : p.coeff n = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4' : n ≠ 4 := by omega
    simp [sourceToRatFunc46, rawQuartic46, hz, coeff_add, coeff_C,
      coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow,
      hn0, hn1, hn2, hn3, hn4', show n - 3 ≠ 0 by omega,
      show n - 2 ≠ 0 by omega, show 1 ≠ n by omega] <;>
      rw [← Polynomial.C_pow, coeff_C] <;>
      simp [show n - 4 ≠ 0 by omega]

/-- The analogous literal raw sextic expansion. -/
theorem sourceToRatFunc46_eq_rawSextic
    (q : k[X][X]) (h : RatFunc k) (hq : q.natDegree = 6)
    (htop : algebraMap k[X] (RatFunc k) (q.coeff 6) = h ^ 6) :
    sourceToRatFunc46 q = rawSextic46 h
      (algebraMap k[X] (RatFunc k) (q.coeff 5))
      (algebraMap k[X] (RatFunc k) (q.coeff 4))
      (algebraMap k[X] (RatFunc k) (q.coeff 3))
      (algebraMap k[X] (RatFunc k) (q.coeff 2))
      (algebraMap k[X] (RatFunc k) (q.coeff 1))
      (algebraMap k[X] (RatFunc k) (q.coeff 0)) := by
  ext n
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      simp [sourceToRatFunc46, rawSextic46, htop, coeff_add, coeff_C,
        coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow] <;>
      rw [← Polynomial.C_pow, coeff_C] <;> simp
  · have hn6 : 6 < n := by omega
    have hz : q.coeff n = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn5 : n ≠ 5 := by omega
    have hn6' : n ≠ 6 := by omega
    simp [sourceToRatFunc46, rawSextic46, hz, coeff_add, coeff_C,
      coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow,
      hn0, hn1, hn2, hn3, hn4, hn5, hn6',
      show n - 5 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show 1 ≠ n by omega] <;>
      rw [← Polynomial.C_pow, coeff_C] <;>
      simp [show n - 6 ≠ 0 by omega]

/-- Exact depressed quartic obtained from a literal degree-four source over
`k[x]`. -/
theorem affineDepress_sourceQuartic46
    (p : k[X][X]) (h r : RatFunc k) (hp : p.natDegree = 4) (hh : h ≠ 0)
    (htop : algebraMap k[X] (RatFunc k) (p.coeff 4) = h ^ 4)
    (hr : r = quarticDepressionR46 h
      (algebraMap k[X] (RatFunc k) (p.coeff 3))) :
    affineDepress46 h r (sourceToRatFunc46 p) =
      depressedQuartic46
        (depressedA46 h r (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2)))
        (depressedB46 h r (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1)))
        (depressedC46 h r (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))) := by
  rw [sourceToRatFunc46_eq_rawQuartic p h hp htop]
  exact affineDepress_rawQuartic46 _ _ _ _ _ _ hh hr

/-- Exact depressed sextic obtained from the same literal source change. -/
theorem affineDepress_sourceSextic46
    (q : k[X][X]) (h r : RatFunc k) (hq : q.natDegree = 6) (hh : h ≠ 0)
    (htop : algebraMap k[X] (RatFunc k) (q.coeff 6) = h ^ 6) :
    affineDepress46 h r (sourceToRatFunc46 q) =
      depressedSextic46
        (depressedL46 h r (algebraMap k[X] (RatFunc k) (q.coeff 5)))
        (depressedP46 h r (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4)))
        (depressedQ46 h r (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3)))
        (depressedR46 h r (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2)))
        (depressedS46 h r (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1)))
        (depressedT46 h r (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))
          (algebraMap k[X] (RatFunc k) (q.coeff 0))) := by
  rw [sourceToRatFunc46_eq_rawSextic q h hq htop]
  exact affineDepress_rawSextic46 _ _ _ _ _ _ _ _ hh

end RawCoefficientForms

section SquareAlignedPackage

/-- The exact depressed data needed downstream from a literal square aligned
source.  All coefficients live in `k(x)` and the bracket retains its literal
value `j/h`. -/
def SquareAlignedDepressedSourceData46
    (p q : k[X][X]) (j : k) (h : RatFunc k) : Prop :=
  ∃ r A B C0 L P0 Q0 R0 S0 T0 : RatFunc k,
    affineDepress46 h r (sourceToRatFunc46 p) =
        depressedQuartic46 A B C0 ∧
    affineDepress46 h r (sourceToRatFunc46 q) =
        depressedSextic46 L P0 Q0 R0 S0 T0 ∧
    L = 0 ∧
    differentialJacobian ratFuncDerivation46
        (depressedQuartic46 A B C0)
        (depressedSextic46 L P0 Q0 R0 S0 T0) =
      C (RatFunc.C j / h)

/-- A literal normalized `(4,6)` source whose common core is a polynomial
square and whose imprimitive discriminator vanishes supplies the exact
aligned depressed package. -/
theorem squareAlignedDepressedSourceData46
    (p q : k[X][X]) (H h0 : k[X]) (j : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 6)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq6 : q.coeff 6 = H ^ 3)
    (haligned : (3 : k[X]) * p.coeff 3 * H -
      (2 : k[X]) * q.coeff 5 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    SquareAlignedDepressedSourceData46 p q j
      (algebraMap k[X] (RatFunc k) h0) := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
  let r : RatFunc k := quarticDepressionR46 h a3
  let A := depressedA46 h r a3 a2
  let B := depressedB46 h r a3 a2 a1
  let C0 := depressedC46 h r a3 a2 a1 a0
  let L := depressedL46 h r b5
  let P0 := depressedP46 h r b5 b4
  let Q0 := depressedQ46 h r b5 b4 b3
  let R0 := depressedR46 h r b5 b4 b3 b2
  let S0 := depressedS46 h r b5 b4 b3 b2 b1
  let T0 := depressedT46 h r b5 b4 b3 b2 b1 b0
  have hh : h ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 4) = h ^ 4 := by
    simp only [hp4, hH, h, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 6) = h ^ 6 := by
    simp only [hq6, hH, h, map_pow]
    ring
  have hpDep : affineDepress46 h r (sourceToRatFunc46 p) =
      depressedQuartic46 A B C0 := by
    exact affineDepress_sourceQuartic46 p h r hp hh hpTop rfl
  have hqDep : affineDepress46 h r (sourceToRatFunc46 q) =
      depressedSextic46 L P0 Q0 R0 S0 T0 := by
    exact affineDepress_sourceSextic46 q h r hq hh hqTop
  have halignedRat : 3 * a3 * h ^ 2 - 2 * b5 = 0 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) haligned
    simp only [map_sub, map_mul, map_ofNat, map_zero, hH, map_pow] at hmapped
    simpa only [a3, b5, h] using hmapped
  have hL : L = 0 := by
    exact depressedL46_eq_zero_of_aligned h a3 b5 hh halignedRat
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc46
    p q j h r hh hD
  rw [hpDep, hqDep] at hbracket
  exact ⟨r, A, B, C0, L, P0, Q0, R0, S0, T0,
    hpDep, hqDep, hL, hbracket⟩

end SquareAlignedPackage

end SourceBracket

end Max11DegreeRoutes
