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
    r = quarticDepressionR46 h
      (algebraMap k[X] (RatFunc k) (p.coeff 3)) ∧
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
    rfl, hpDep, hqDep, hL, hbracket⟩

end SquareAlignedPackage

section AlignedIntegration

/-- The five upper coefficient equations extracted from an aligned depressed
bracket with constant right-hand side. -/
theorem alignedDepressedUpperRows46
    (A B C0 P0 Q0 R0 S0 T0 terminal : RatFunc k)
    (hbracket : differentialJacobian ratFuncDerivation46
        (depressedQuartic46 A B C0)
        (depressedSextic46 0 P0 Q0 R0 S0 T0) = C terminal) :
    (6 * ratFuncDerivation46 A - 4 * ratFuncDerivation46 P0 = 0) ∧
    (6 * ratFuncDerivation46 B - 4 * ratFuncDerivation46 Q0 = 0) ∧
    (-2 * A * ratFuncDerivation46 P0 + 4 * P0 * ratFuncDerivation46 A +
        6 * ratFuncDerivation46 C0 - 4 * ratFuncDerivation46 R0 = 0) ∧
    (-2 * A * ratFuncDerivation46 Q0 - B * ratFuncDerivation46 P0 +
        4 * P0 * ratFuncDerivation46 B + 3 * Q0 * ratFuncDerivation46 A -
        4 * ratFuncDerivation46 S0 = 0) ∧
    (-2 * A * ratFuncDerivation46 R0 - B * ratFuncDerivation46 Q0 +
        4 * P0 * ratFuncDerivation46 C0 + 3 * Q0 * ratFuncDerivation46 B +
        2 * R0 * ratFuncDerivation46 A - 4 * ratFuncDerivation46 T0 = 0) := by
  have hfull := hbracket
  rw [differentialJacobian_depressed46_eq ratFuncDerivation46
    0 P0 Q0 R0 S0 T0 A B C0 (by simp)] at hfull
  have h7 := congrArg (fun f : (RatFunc k)[X] => f.coeff 7) hfull
  have h6 := congrArg (fun f : (RatFunc k)[X] => f.coeff 6) hfull
  have h5 := congrArg (fun f : (RatFunc k)[X] => f.coeff 5) hfull
  have h4 := congrArg (fun f : (RatFunc k)[X] => f.coeff 4) hfull
  have h3 := congrArg (fun f : (RatFunc k)[X] => f.coeff 3) hfull
  norm_num [coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow] at h7 h6 h5 h4 h3
  refine ⟨h7, h6, ?_, ?_, ?_⟩
  · simp only [ratFuncDerivation46_apply]
    linear_combination h5
  · simp only [ratFuncDerivation46_apply]
    linear_combination h4
  · simp only [ratFuncDerivation46_apply]
    linear_combination h3

/-- The first residual left by the aligned upper rows. -/
def alignedAlphaResidual46 (A P0 : RatFunc k) : RatFunc k :=
  P0 - (3 / 2 : RatFunc k) * A

/-- The second residual left by the aligned upper rows. -/
def alignedBetaResidual46 (B Q0 : RatFunc k) : RatFunc k :=
  Q0 - (3 / 2 : RatFunc k) * B

/-- The third residual, after the first one has been isolated. -/
def alignedGammaResidual46
    (A C0 P0 R0 : RatFunc k) : RatFunc k :=
  R0 - (3 / 8 : RatFunc k) * A ^ 2 -
    alignedAlphaResidual46 A P0 * A - (3 / 2 : RatFunc k) * C0

/-- The fourth residual, after the first two have been isolated. -/
def alignedDeltaResidual46
    (A B P0 Q0 S0 : RatFunc k) : RatFunc k :=
  S0 - (3 / 4 : RatFunc k) * A * B -
    (3 / 4 : RatFunc k) * alignedBetaResidual46 B Q0 * A -
    alignedAlphaResidual46 A P0 * B

/-- The fifth residual, after the first three have been isolated. -/
def alignedEpsilonResidual46
    (A B C0 P0 Q0 R0 T0 : RatFunc k) : RatFunc k :=
  T0 - ((-1 / 16 : RatFunc k) * A ^ 3 +
    (3 / 4 : RatFunc k) * A * C0 +
    (1 / 2 : RatFunc k) * alignedGammaResidual46 A C0 P0 R0 * A +
    (3 / 8 : RatFunc k) * B ^ 2 +
    (3 / 4 : RatFunc k) * alignedBetaResidual46 B Q0 * B +
    alignedAlphaResidual46 A P0 * C0)

/-- The aligned upper rows successively force all five residuals to have
zero standard derivative. -/
theorem alignedDepressedResiduals_deriv_zero46
    (A B C0 P0 Q0 R0 S0 T0 terminal : RatFunc k)
    (hbracket : differentialJacobian ratFuncDerivation46
        (depressedQuartic46 A B C0)
        (depressedSextic46 0 P0 Q0 R0 S0 T0) = C terminal) :
    ratFuncDerivation46 (alignedAlphaResidual46 A P0) = 0 ∧
    ratFuncDerivation46 (alignedBetaResidual46 B Q0) = 0 ∧
    ratFuncDerivation46 (alignedGammaResidual46 A C0 P0 R0) = 0 ∧
    ratFuncDerivation46 (alignedDeltaResidual46 A B P0 Q0 S0) = 0 ∧
    ratFuncDerivation46 (alignedEpsilonResidual46 A B C0 P0 Q0 R0 T0) = 0 := by
  rcases alignedDepressedUpperRows46 A B C0 P0 Q0 R0 S0 T0 terminal
      hbracket with ⟨h7, h6, h5, h4, h3⟩
  have h2 : ratFuncDerivation46 (2 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 2
  have h3c : ratFuncDerivation46 (3 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 3
  have h4c : ratFuncDerivation46 (4 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 4
  have h8 : ratFuncDerivation46 (8 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 8
  have h16 : ratFuncDerivation46 (16 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 16
  have h12 : ratFuncDerivation46 (1 / 2 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h2]
  have h32 : ratFuncDerivation46 (3 / 2 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, h2, h3c]
  have h34 : ratFuncDerivation46 (3 / 4 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, h3c, h4c]
  have h38 : ratFuncDerivation46 (3 / 8 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, h3c, h8]
  have h116 : ratFuncDerivation46 (1 / 16 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h16]
  have hn116 : ratFuncDerivation46 (-1 / 16 : RatFunc k) = 0 := by
    rw [show (-1 / 16 : RatFunc k) = -(1 / 16) by ring, map_neg, h116,
      neg_zero]
  have halpha : ratFuncDerivation46 (alignedAlphaResidual46 A P0) = 0 := by
    simp only [alignedAlphaResidual46, map_sub, Derivation.leibniz, h32,
      zero_mul, add_zero]
    linear_combination (-1 / 4 : RatFunc k) * h7
  have hbeta : ratFuncDerivation46 (alignedBetaResidual46 B Q0) = 0 := by
    simp only [alignedBetaResidual46, map_sub, Derivation.leibniz, h32,
      zero_mul, add_zero]
    linear_combination (-1 / 4 : RatFunc k) * h6
  have hPderiv : ratFuncDerivation46 P0 =
      (3 / 2 : RatFunc k) * ratFuncDerivation46 A := by
    linear_combination (-1 / 4 : RatFunc k) * h7
  have hQderiv : ratFuncDerivation46 Q0 =
      (3 / 2 : RatFunc k) * ratFuncDerivation46 B := by
    linear_combination (-1 / 4 : RatFunc k) * h6
  have hRderiv : ratFuncDerivation46 R0 =
      (-3 / 4 : RatFunc k) * A * ratFuncDerivation46 A +
        P0 * ratFuncDerivation46 A +
        (3 / 2 : RatFunc k) * ratFuncDerivation46 C0 := by
    linear_combination (-1 / 4 : RatFunc k) * h5 -
      (A / 2 : RatFunc k) * hPderiv
  have hSderiv : ratFuncDerivation46 S0 =
      (-3 / 4 : RatFunc k) * A * ratFuncDerivation46 B -
        (3 / 8 : RatFunc k) * B * ratFuncDerivation46 A +
        P0 * ratFuncDerivation46 B +
        (3 / 4 : RatFunc k) * Q0 * ratFuncDerivation46 A := by
    linear_combination (-1 / 4 : RatFunc k) * h4 -
      (A / 2 : RatFunc k) * hQderiv -
      (B / 4 : RatFunc k) * hPderiv
  have hTderiv : ratFuncDerivation46 T0 =
      (-1 / 2 : RatFunc k) * A * ratFuncDerivation46 R0 -
        (1 / 4 : RatFunc k) * B * ratFuncDerivation46 Q0 +
        P0 * ratFuncDerivation46 C0 +
        (3 / 4 : RatFunc k) * Q0 * ratFuncDerivation46 B +
        (1 / 2 : RatFunc k) * R0 * ratFuncDerivation46 A := by
    linear_combination (-1 / 4 : RatFunc k) * h3
  have hgamma :
      ratFuncDerivation46 (alignedGammaResidual46 A C0 P0 R0) = 0 := by
    simp only [alignedGammaResidual46, map_sub, Derivation.leibniz,
      Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, h38, h32,
      halpha, zero_mul, zero_add, add_zero]
    rw [hRderiv]
    simp only [alignedAlphaResidual46]
    ring
  have hdelta :
      ratFuncDerivation46 (alignedDeltaResidual46 A B P0 Q0 S0) = 0 := by
    simp only [alignedDeltaResidual46, map_sub, Derivation.leibniz, h34,
      halpha, hbeta, zero_mul, zero_add, add_zero]
    rw [hSderiv]
    simp only [alignedAlphaResidual46, alignedBetaResidual46]
    ring
  have hepsilon :
      ratFuncDerivation46
        (alignedEpsilonResidual46 A B C0 P0 Q0 R0 T0) = 0 := by
    simp only [alignedEpsilonResidual46, map_sub, map_add, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
      smul_eq_mul, hn116, h34, h12, h38, hgamma, hbeta, halpha,
      zero_mul, zero_add, add_zero]
    rw [hTderiv, hRderiv, hQderiv]
    simp only [alignedGammaResidual46, alignedBetaResidual46,
      alignedAlphaResidual46]
    ring
  exact ⟨halpha, hbeta, hgamma, hdelta, hepsilon⟩

/-- The five upper rows of a literal aligned bracket integrate to the
reviewed normal form, with every integration parameter represented by an
element of the ground field `k`. -/
theorem alignedDepressedIntegratesOverGround46
    (A B C0 P0 Q0 R0 S0 T0 terminal : RatFunc k)
    (hbracket : differentialJacobian ratFuncDerivation46
        (depressedQuartic46 A B C0)
        (depressedSextic46 0 P0 Q0 R0 S0 T0) = C terminal) :
    ∃ alpha beta gamma delta epsilon : k,
      P0 = integratedP46 A (algebraMap k (RatFunc k) alpha) ∧
      Q0 = integratedQ46 0 A B (algebraMap k (RatFunc k) beta) ∧
      R0 = integratedR46 0 A B C0 (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) gamma) ∧
      S0 = integratedS46 0 A B C0 (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) beta) (algebraMap k (RatFunc k) delta) ∧
      T0 = integratedT46 0 A B C0 (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) beta) (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) epsilon) := by
  rcases alignedDepressedResiduals_deriv_zero46
      A B C0 P0 Q0 R0 S0 T0 terminal hbracket with
    ⟨halpha0, hbeta0, hgamma0, hdelta0, hepsilon0⟩
  have halphaD : Differential.deriv (alignedAlphaResidual46 A P0) = 0 := by
    simpa only [ratFuncDerivation46_apply] using halpha0
  have hbetaD : Differential.deriv (alignedBetaResidual46 B Q0) = 0 := by
    simpa only [ratFuncDerivation46_apply] using hbeta0
  have hgammaD :
      Differential.deriv (alignedGammaResidual46 A C0 P0 R0) = 0 := by
    simpa only [ratFuncDerivation46_apply] using hgamma0
  have hdeltaD :
      Differential.deriv (alignedDeltaResidual46 A B P0 Q0 S0) = 0 := by
    simpa only [ratFuncDerivation46_apply] using hdelta0
  have hepsilonD : Differential.deriv
      (alignedEpsilonResidual46 A B C0 P0 Q0 R0 T0) = 0 := by
    simpa only [ratFuncDerivation46_apply] using hepsilon0
  obtain ⟨alpha, halpha⟩ := GCD369RatFuncConstants
    (alignedAlphaResidual46 A P0) halphaD
  obtain ⟨beta, hbeta⟩ := GCD369RatFuncConstants
    (alignedBetaResidual46 B Q0) hbetaD
  obtain ⟨gamma, hgamma⟩ := GCD369RatFuncConstants
    (alignedGammaResidual46 A C0 P0 R0) hgammaD
  obtain ⟨delta, hdelta⟩ := GCD369RatFuncConstants
    (alignedDeltaResidual46 A B P0 Q0 S0) hdeltaD
  obtain ⟨epsilon, hepsilon⟩ := GCD369RatFuncConstants
    (alignedEpsilonResidual46 A B C0 P0 Q0 R0 T0) hepsilonD
  refine ⟨alpha, beta, gamma, delta, epsilon, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← halpha]
    simp only [integratedP46, alignedAlphaResidual46]
    ring
  · rw [← hbeta]
    simp only [integratedQ46, alignedBetaResidual46]
    ring
  · rw [← halpha, ← hgamma]
    simp only [integratedR46, alignedAlphaResidual46,
      alignedGammaResidual46]
    ring
  · rw [← halpha, ← hbeta, ← hdelta]
    simp only [integratedS46, alignedAlphaResidual46,
      alignedBetaResidual46, alignedDeltaResidual46]
    ring
  · rw [← halpha, ← hbeta, ← hgamma, ← hepsilon]
    simp only [integratedT46, alignedAlphaResidual46,
      alignedBetaResidual46, alignedGammaResidual46,
      alignedEpsilonResidual46]
    ring

/-- The entire aligned constant bracket therefore lands on the reviewed
coefficient curve over ground-field parameters; its last row is the exact
terminal one-form, not merely a proportionality statement. -/
theorem alignedDepressedCoefficientCurveData46
    (A B C0 P0 Q0 R0 S0 T0 terminal : RatFunc k)
    (hbracket : differentialJacobian ratFuncDerivation46
        (depressedQuartic46 A B C0)
        (depressedSextic46 0 P0 Q0 R0 S0 T0) = C terminal) :
    ∃ alpha beta gamma delta epsilon k2 k1 : k,
      P0 = integratedP46 A (algebraMap k (RatFunc k) alpha) ∧
      Q0 = integratedQ46 0 A B (algebraMap k (RatFunc k) beta) ∧
      R0 = integratedR46 0 A B C0 (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) gamma) ∧
      S0 = integratedS46 0 A B C0 (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) beta) (algebraMap k (RatFunc k) delta) ∧
      T0 = integratedT46 0 A B C0 (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) beta) (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) epsilon) ∧
      coefficientCurveTwo46 0 A B (A ^ 2 - 4 * C0)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) delta) =
        algebraMap k (RatFunc k) k2 ∧
      coefficientCurveOne46 0 A B (A ^ 2 - 4 * C0)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) delta) =
        algebraMap k (RatFunc k) k1 ∧
      eta46 0 A B (A ^ 2 - 4 * C0)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) delta)
          (ratFuncDerivation46 A) (ratFuncDerivation46 B)
          (ratFuncDerivation46 (A ^ 2 - 4 * C0)) = terminal := by
  obtain ⟨alpha, beta, gamma, delta, epsilon,
      hP, hQ, hR, hS, hT⟩ :=
    alignedDepressedIntegratesOverGround46
      A B C0 P0 Q0 R0 S0 T0 terminal hbracket
  let U : RatFunc k := A ^ 2 - 4 * C0
  have hC : discriminantC46 A U = C0 := by
    simp only [discriminantC46, U]
    ring
  have hconst (c : k) : ratFuncDerivation46 (RatFunc.C c) = 0 := by
    have hp := ratFuncDerivation46_polynomial (C c : k[X])
    simpa [RatFunc.algebraMap_C] using hp
  have hshape := differentialJacobian_integratedDiscriminant46_eq
    ratFuncDerivation46 0 A B U
      (algebraMap k (RatFunc k) alpha)
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta)
      (algebraMap k (RatFunc k) epsilon)
      (by simp) (by simpa [RatFunc.algebraMap_eq_C] using hconst alpha)
      (by simpa [RatFunc.algebraMap_eq_C] using hconst beta)
      (by simpa [RatFunc.algebraMap_eq_C] using hconst gamma)
      (by simpa [RatFunc.algebraMap_eq_C] using hconst delta)
      (by simpa [RatFunc.algebraMap_eq_C] using hconst epsilon)
  dsimp only at hshape
  rw [hC] at hshape
  have hbracket' := hbracket
  rw [hP, hQ, hR, hS, hT, hshape] at hbracket'
  have h2 := congrArg (fun f : (RatFunc k)[X] => f.coeff 2) hbracket'
  have h1 := congrArg (fun f : (RatFunc k)[X] => f.coeff 1) hbracket'
  have h0 := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) hbracket'
  norm_num [coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow] at h2 h1 h0
  have h2D : Differential.deriv
      (coefficientCurveTwo46 0 A B U
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta)) = 0 := by
    simpa only [ratFuncDerivation46_apply, RatFunc.algebraMap_eq_C] using h2
  have h1D : Differential.deriv
      (coefficientCurveOne46 0 A B U
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta)) = 0 := by
    simpa only [ratFuncDerivation46_apply, RatFunc.algebraMap_eq_C] using h1
  obtain ⟨k2, hk2⟩ := GCD369RatFuncConstants
    (coefficientCurveTwo46 0 A B U
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta)) h2D
  obtain ⟨k1, hk1⟩ := GCD369RatFuncConstants
    (coefficientCurveOne46 0 A B U
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta)) h1D
  refine ⟨alpha, beta, gamma, delta, epsilon, k2, k1,
    hP, hQ, hR, hS, hT, ?_, ?_, ?_⟩
  · simpa only [U]
  · simpa only [U]
  · simpa only [U, RatFunc.algebraMap_eq_C,
      ratFuncDerivation46_apply] using h0

section SourceBoundaries

/-- Evaluating at the center of the affine depression recovers the original
constant coefficient. -/
theorem eval_affineDepress46_center
    (h r : RatFunc k) (f : (RatFunc k)[X]) :
    (affineDepress46 h r f).eval r = f.coeff 0 := by
  simpa [affineDepress46] using (coeff_zero_eq_eval_zero f).symm

/-- At a nonzero scalar scale and polynomial center, affine depression
commutes exactly with the embedding `k[x] → k(x)`. -/
theorem affineDepress_source_constantScale_map46
    (f : k[X][X]) (t : k) (r0 : k[X]) (ht : t ≠ 0) :
    affineDepress46 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) r0) (sourceToRatFunc46 f) =
      (f.comp ((X - C r0) * C (C t⁻¹))).map
        (algebraMap k[X] (RatFunc k)) := by
  rw [Polynomial.map_comp]
  simp only [affineDepress46, sourceToRatFunc46, map_mul, map_sub,
    map_X, map_C, RatFunc.algebraMap_C]
  congr 2
  simp [ht]

/-- The two reviewed boundary functions of an integrated depressed literal
source are exactly images of explicit polynomials in `k[x]`. -/
theorem alignedDepressedLiteralBoundaries46
    (p q : k[X][X]) (h r A B C0 : RatFunc k)
    (alpha beta gamma delta epsilon : k)
    (hpDep : affineDepress46 h r (sourceToRatFunc46 p) =
      depressedQuartic46 A B C0)
    (hqDep : affineDepress46 h r (sourceToRatFunc46 q) =
      depressedSextic46 0
        (integratedP46 A (algebraMap k (RatFunc k) alpha))
        (integratedQ46 0 A B (algebraMap k (RatFunc k) beta))
        (integratedR46 0 A B C0 (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) gamma))
        (integratedS46 0 A B C0 (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) delta))
        (integratedT46 0 A B C0 (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) epsilon))) :
    boundaryD46 r (translatedQ46 r A) B (A ^ 2 - 4 * C0) =
        algebraMap k[X] (RatFunc k) (p.coeff 0) ∧
    boundaryE46 0 r (translatedQ46 r A) B (A ^ 2 - 4 * C0)
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta) =
      algebraMap k[X] (RatFunc k)
        (q.coeff 0 - C alpha * p.coeff 0 - C epsilon) := by
  let U : RatFunc k := A ^ 2 - 4 * C0
  have hC : discriminantC46 A U = C0 := by
    simp only [discriminantC46, U]
    ring
  have hpCenter := congrArg (fun f : (RatFunc k)[X] => f.eval r) hpDep
  have hqCenter := congrArg (fun f : (RatFunc k)[X] => f.eval r) hqDep
  rw [eval_affineDepress46_center] at hpCenter hqCenter
  simp only [sourceToRatFunc46, coeff_map] at hpCenter hqCenter
  have hDcurve :=
    eval_depressedQuartic46_discriminant_eq_boundaryD46 r A B U
  have hEcurve := eval_integratedSextic46_discriminant_eq_boundaryE46
    0 r A B U (algebraMap k (RatFunc k) alpha)
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta)
      (algebraMap k (RatFunc k) epsilon)
  dsimp only at hEcurve
  rw [hC] at hDcurve hEcurve
  constructor
  · simpa only [U] using hDcurve.symm.trans hpCenter.symm
  · have hboundary : boundaryE46 0 r (translatedQ46 r A) B U
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta) =
        algebraMap k[X] (RatFunc k) (q.coeff 0) -
          algebraMap k (RatFunc k) alpha *
            algebraMap k[X] (RatFunc k) (p.coeff 0) -
          algebraMap k (RatFunc k) epsilon := by
      rw [← hEcurve, ← hqCenter, ← hpCenter]
    rw [hboundary]
    simp only [map_sub, map_mul, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C]

end SourceBoundaries

section CompleteSquareSourcePackage

/-- The source-facing coefficient-curve package produced by an aligned
square-core `(4,6)` source.  Besides the exact depressed normal form, it
contains both curve rows, both literal polynomial boundaries, and the last
row after restoring the factor `h`. -/
structure SquareAlignedSourceCurveData46
    (p q : k[X][X]) (j : k) (h0 : k[X]) where
  r : RatFunc k
  A : RatFunc k
  B : RatFunc k
  C0 : RatFunc k
  alpha : k
  beta : k
  gamma : k
  delta : k
  epsilon : k
  k2 : k
  k1 : k
  center_eq : r = quarticDepressionR46
    (algebraMap k[X] (RatFunc k) h0)
    (algebraMap k[X] (RatFunc k) (p.coeff 3))
  quartic_eq :
    affineDepress46 (algebraMap k[X] (RatFunc k) h0) r
        (sourceToRatFunc46 p) = depressedQuartic46 A B C0
  sextic_eq :
    affineDepress46 (algebraMap k[X] (RatFunc k) h0) r
        (sourceToRatFunc46 q) =
      depressedSextic46 0
        (integratedP46 A (algebraMap k (RatFunc k) alpha))
        (integratedQ46 0 A B (algebraMap k (RatFunc k) beta))
        (integratedR46 0 A B C0 (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) gamma))
        (integratedS46 0 A B C0 (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) delta))
        (integratedT46 0 A B C0 (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) epsilon))
  curveTwo : coefficientCurveTwo46 0 A B (A ^ 2 - 4 * C0)
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta) =
    algebraMap k (RatFunc k) k2
  curveOne : coefficientCurveOne46 0 A B (A ^ 2 - 4 * C0)
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta) =
    algebraMap k (RatFunc k) k1
  boundaryD : boundaryD46 r (translatedQ46 r A) B (A ^ 2 - 4 * C0) =
    algebraMap k[X] (RatFunc k) (p.coeff 0)
  boundaryE : boundaryE46 0 r (translatedQ46 r A) B (A ^ 2 - 4 * C0)
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta) =
    algebraMap k[X] (RatFunc k)
      (q.coeff 0 - C alpha * p.coeff 0 - C epsilon)
  lastRow : algebraMap k[X] (RatFunc k) h0 *
      eta46 0 A B (A ^ 2 - 4 * C0)
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta)
        (ratFuncDerivation46 A) (ratFuncDerivation46 B)
        (ratFuncDerivation46 (A ^ 2 - 4 * C0)) = RatFunc.C j

/-- A literal square-core aligned source supplies every field and boundary
equation in `SquareAlignedSourceCurveData46`. -/
theorem squareAlignedSourceCurveData46
    (p q : k[X][X]) (H h0 : k[X]) (j : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 6)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq6 : q.coeff 6 = H ^ 3)
    (haligned : (3 : k[X]) * p.coeff 3 * H -
      (2 : k[X]) * q.coeff 5 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    Nonempty (SquareAlignedSourceCurveData46 p q j h0) := by
  obtain ⟨r, A, B, C0, L, P0, Q0, R0, S0, T0,
      hr, hpDep, hqDep, hL, hbracket⟩ :=
    squareAlignedDepressedSourceData46 p q H h0 j hp hq hh0 hH hp4 hq6
      haligned hD
  subst L
  obtain ⟨alpha, beta, gamma, delta, epsilon, k2, k1,
      hP, hQ, hR, hS, hT, hcurve2, hcurve1, heta⟩ :=
    alignedDepressedCoefficientCurveData46
      A B C0 P0 Q0 R0 S0 T0
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) hbracket
  have hqIntegrated :
      affineDepress46 (algebraMap k[X] (RatFunc k) h0) r
          (sourceToRatFunc46 q) =
        depressedSextic46 0
          (integratedP46 A (algebraMap k (RatFunc k) alpha))
          (integratedQ46 0 A B (algebraMap k (RatFunc k) beta))
          (integratedR46 0 A B C0 (algebraMap k (RatFunc k) alpha)
            (algebraMap k (RatFunc k) gamma))
          (integratedS46 0 A B C0 (algebraMap k (RatFunc k) alpha)
            (algebraMap k (RatFunc k) beta)
            (algebraMap k (RatFunc k) delta))
          (integratedT46 0 A B C0 (algebraMap k (RatFunc k) alpha)
            (algebraMap k (RatFunc k) beta)
            (algebraMap k (RatFunc k) gamma)
            (algebraMap k (RatFunc k) epsilon)) := by
    rw [hqDep, hP, hQ, hR, hS, hT]
  have hboundaries := alignedDepressedLiteralBoundaries46
    p q (algebraMap k[X] (RatFunc k) h0) r A B C0
      alpha beta gamma delta epsilon hpDep hqIntegrated
  have hhRat : algebraMap k[X] (RatFunc k) h0 ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh0
  have hlast : algebraMap k[X] (RatFunc k) h0 *
      eta46 0 A B (A ^ 2 - 4 * C0)
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta)
        (ratFuncDerivation46 A) (ratFuncDerivation46 B)
        (ratFuncDerivation46 (A ^ 2 - 4 * C0)) = RatFunc.C j := by
    rw [heta]
    field_simp
  exact ⟨{
    r := r
    A := A
    B := B
    C0 := C0
    alpha := alpha
    beta := beta
    gamma := gamma
    delta := delta
    epsilon := epsilon
    k2 := k2
    k1 := k1
    center_eq := hr
    quartic_eq := hpDep
    sextic_eq := hqIntegrated
    curveTwo := hcurve2
    curveOne := hcurve1
    boundaryD := hboundaries.1
    boundaryE := hboundaries.2
    lastRow := hlast
  }⟩

/-- The exact final component `beta=delta=k2=0` is impossible already at
the literal source level.  Hence every aligned square-core source lies in one
of the three strata still handled by the global pole/polynomial bridge. -/
theorem SquareAlignedSourceCurveData46.nonfinalStratum
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (S : SquareAlignedSourceCurveData46 p q j h0) (hj : j ≠ 0) :
    S.beta ≠ 0 ∨
      (S.beta = 0 ∧ S.delta ≠ 0) ∨
      (S.beta = 0 ∧ S.delta = 0 ∧ S.k2 ≠ 0) := by
  by_cases hbeta : S.beta = 0
  · by_cases hdelta : S.delta = 0
    · by_cases hk2 : S.k2 = 0
      · exfalso
        exact alignedZeroSquareComponent_standardDifferential_impossible46
          h0 (p.coeff 0)
          (q.coeff 0 - C S.alpha * p.coeff 0 - C S.epsilon)
          S.r S.A S.B (S.A ^ 2 - 4 * S.C0) S.gamma S.k1 j hj
          (by simpa [hbeta, hdelta, hk2] using S.curveTwo)
          (by simpa [hbeta, hdelta] using S.curveOne)
          S.boundaryD (by simpa [hbeta, hdelta] using S.boundaryE)
          (by simpa [hbeta, hdelta, ratFuncDerivation46_apply]
            using S.lastRow)
      · exact Or.inr (Or.inr ⟨hbeta, hdelta, hk2⟩)
    · exact Or.inr (Or.inl ⟨hbeta, hdelta⟩)
  · exact Or.inl hbeta

end CompleteSquareSourcePackage

end AlignedIntegration

end SourceBracket

end Max11DegreeRoutes
