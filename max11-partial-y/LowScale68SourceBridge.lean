import LowScale46SourceBridge
import LowScale68Depression

/-! # Literal source-to-differential bridge for `(6,8)`

This module reuses the standard quotient-rule derivation on `k(x)`, maps a
literal coefficient-polynomial Keller bracket into that differential field,
and connects degree-six/eight sources to the exact depressed normal form.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SourceBridge68

variable {k : Type*} [Field k] [CharZero k]

/-- The source map used for `(6,8)` is the same coefficient-field inclusion as
for `(4,6)`. -/
abbrev sourceToRatFunc68 (p : k[X][X]) : (RatFunc k)[X] :=
  sourceToRatFunc46 p

/-- The quotient-rule derivation used by the `(6,8)` normal form. -/
abbrev ratFuncDerivation68 : Derivation k (RatFunc k) (RatFunc k) :=
  ratFuncDerivation46

/-- A literal source Jacobian maps to the differential bracket on `k(x)`. -/
theorem differentialJacobian_sourceToRatFunc68
    (p q : k[X][X]) (j : k)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    differentialJacobian ratFuncDerivation68
        (sourceToRatFunc68 p) (sourceToRatFunc68 q) = C (RatFunc.C j) := by
  exact differentialJacobian_sourceToRatFunc46 p q j hD

/-- After the common change `y=(z-r)/h`, the source bracket is divided by
`h`. -/
theorem differentialJacobian_affineDepress_sourceToRatFunc68
    (p q : k[X][X]) (j : k) (h r : RatFunc k) (hh : h ≠ 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    differentialJacobian ratFuncDerivation68
        (affineDepress68 h r (sourceToRatFunc68 p))
        (affineDepress68 h r (sourceToRatFunc68 q)) =
      C (RatFunc.C j / h) := by
  simpa [affineDepress68, affineDepress46] using
    differentialJacobian_affineDepress_sourceToRatFunc46
      p q j h r hh hD

/-- A mapped degree-six source with leading coefficient `h^6` is exactly the
raw sextic used by the depression calculation. -/
theorem sourceToRatFunc68_eq_rawSextic
    (p : k[X][X]) (h : RatFunc k) (hp : p.natDegree = 6)
    (htop : algebraMap k[X] (RatFunc k) (p.coeff 6) = h ^ 6) :
    sourceToRatFunc68 p = rawSextic68 h
      (algebraMap k[X] (RatFunc k) (p.coeff 5))
      (algebraMap k[X] (RatFunc k) (p.coeff 4))
      (algebraMap k[X] (RatFunc k) (p.coeff 3))
      (algebraMap k[X] (RatFunc k) (p.coeff 2))
      (algebraMap k[X] (RatFunc k) (p.coeff 1))
      (algebraMap k[X] (RatFunc k) (p.coeff 0)) := by
  ext n
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      simp [sourceToRatFunc68, sourceToRatFunc46, rawSextic68, htop,
        coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow', coeff_X,
        coeff_X_pow] <;>
      rw [← Polynomial.C_pow, coeff_C] <;> simp
  · have hn6 : 6 < n := by omega
    have hz : p.coeff n = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn5 : n ≠ 5 := by omega
    have hn6' : n ≠ 6 := by omega
    simp [sourceToRatFunc68, sourceToRatFunc46, rawSextic68, hz,
      coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow', coeff_X,
      coeff_X_pow, hn0, hn1, hn2, hn3, hn4, hn5, hn6',
      show n - 5 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show 1 ≠ n by omega] <;>
      rw [← Polynomial.C_pow, coeff_C] <;>
      simp [show n - 6 ≠ 0 by omega]

/-- The analogous literal raw octic expansion. -/
theorem sourceToRatFunc68_eq_rawOctic
    (q : k[X][X]) (h : RatFunc k) (hq : q.natDegree = 8)
    (htop : algebraMap k[X] (RatFunc k) (q.coeff 8) = h ^ 8) :
    sourceToRatFunc68 q = rawOctic68 h
      (algebraMap k[X] (RatFunc k) (q.coeff 7))
      (algebraMap k[X] (RatFunc k) (q.coeff 6))
      (algebraMap k[X] (RatFunc k) (q.coeff 5))
      (algebraMap k[X] (RatFunc k) (q.coeff 4))
      (algebraMap k[X] (RatFunc k) (q.coeff 3))
      (algebraMap k[X] (RatFunc k) (q.coeff 2))
      (algebraMap k[X] (RatFunc k) (q.coeff 1))
      (algebraMap k[X] (RatFunc k) (q.coeff 0)) := by
  ext n
  by_cases hn : n ≤ 8
  · interval_cases n <;>
      simp [sourceToRatFunc68, sourceToRatFunc46, rawOctic68, htop,
        coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow', coeff_X,
        coeff_X_pow] <;>
      rw [← Polynomial.C_pow, coeff_C] <;> simp
  · have hn8 : 8 < n := by omega
    have hz : q.coeff n = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn5 : n ≠ 5 := by omega
    have hn6 : n ≠ 6 := by omega
    have hn7 : n ≠ 7 := by omega
    have hn8' : n ≠ 8 := by omega
    simp [sourceToRatFunc68, sourceToRatFunc46, rawOctic68, hz,
      coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow', coeff_X,
      coeff_X_pow, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8',
      show n - 7 ≠ 0 by omega, show n - 6 ≠ 0 by omega,
      show n - 5 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show 1 ≠ n by omega] <;>
      rw [← Polynomial.C_pow, coeff_C] <;>
      simp [show n - 8 ≠ 0 by omega]

/-- Exact depressed sextic obtained from a literal degree-six source. -/
theorem affineDepress_sourceSextic68
    (p : k[X][X]) (h r : RatFunc k) (hp : p.natDegree = 6) (hh : h ≠ 0)
    (htop : algebraMap k[X] (RatFunc k) (p.coeff 6) = h ^ 6)
    (hr : r = sexticDepressionR68 h
      (algebraMap k[X] (RatFunc k) (p.coeff 5))) :
    affineDepress68 h r (sourceToRatFunc68 p) =
      depressedSextic68
        (depressedA68 h r (algebraMap k[X] (RatFunc k) (p.coeff 5))
          (algebraMap k[X] (RatFunc k) (p.coeff 4)))
        (depressedB68 h r (algebraMap k[X] (RatFunc k) (p.coeff 5))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3)))
        (depressedC68 h r (algebraMap k[X] (RatFunc k) (p.coeff 5))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2)))
        (depressedD68 h r (algebraMap k[X] (RatFunc k) (p.coeff 5))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1)))
        (depressedE68 h r (algebraMap k[X] (RatFunc k) (p.coeff 5))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))) := by
  rw [sourceToRatFunc68_eq_rawSextic p h hp htop]
  exact affineDepress_rawSextic68 _ _ _ _ _ _ _ _ hh hr

/-- Exact depressed octic obtained from the same literal source change. -/
theorem affineDepress_sourceOctic68
    (q : k[X][X]) (h r : RatFunc k) (hq : q.natDegree = 8) (hh : h ≠ 0)
    (htop : algebraMap k[X] (RatFunc k) (q.coeff 8) = h ^ 8) :
    affineDepress68 h r (sourceToRatFunc68 q) =
      depressedOctic68
        (depressedL68 h r (algebraMap k[X] (RatFunc k) (q.coeff 7)))
        (depressedP68 h r (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6)))
        (depressedQ68 h r (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5)))
        (depressedR68 h r (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4)))
        (depressedS68 h r (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3)))
        (depressedT68 h r (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2)))
        (depressedU68 h r (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1)))
        (depressedV68 h r (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))
          (algebraMap k[X] (RatFunc k) (q.coeff 0))) := by
  rw [sourceToRatFunc68_eq_rawOctic q h hq htop]
  exact affineDepress_rawOctic68 _ _ _ _ _ _ _ _ _ _ hh

end SourceBridge68

#print axioms differentialJacobian_sourceToRatFunc68
#print axioms differentialJacobian_affineDepress_sourceToRatFunc68
#print axioms sourceToRatFunc68_eq_rawSextic
#print axioms sourceToRatFunc68_eq_rawOctic
#print axioms affineDepress_sourceSextic68
#print axioms affineDepress_sourceOctic68

end Max11DegreeRoutes
