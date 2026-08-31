import TargetNormalization

noncomputable section
open Polynomial

/-! # Literal handoff to the later Faber fibre

Once `d`, the retained high constants, and the first two Faber integrals
vanish, the target-normalized literal polynomial source lies on the exact
later `(rho3,rho4)` fibre.  The fifth lower row simultaneously supplies the
terminal rational ODE consumed by `GCD369CubeLaterRatFuncTerminalSource`.
-/

namespace GCD369CubePolynomialSource

/-- The literal target-normalized source, restricted to the zero early-load
stratum, produces the complete later Faber invariant source. -/
noncomputable def targetNormalizedLaterInvariantSource
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hd : S.faberConstantParameters.d = 0)
    (hc7 : S.faberConstantParameters.c7 = 0)
    (hc5 : S.faberConstantParameters.c5 = 0)
    (hc4 : S.faberConstantParameters.c4 = 0)
    (hc2 : S.faberConstantParameters.c2 = 0)
    (hc1 : S.faberConstantParameters.c1 -
      7 * S.faberConstantParameters.c7 *
        S.faberConstantParameters.c3 / 9 = 0)
    (hrho1 : (S.targetNormalizedFirstIntegralConstants hd).rho1 = 0)
    (hrho2 : (S.targetNormalizedFirstIntegralConstants hd).rho2 = 0) :
    GCD369CubeLaterInvariantSource (RatFunc k) := by
  let T := S.targetNormalizedSource
  let P := S.faberConstantParameters
  let N := S.targetNormalizedFaberNormalForm hd
  let R := S.targetNormalizedFirstIntegralConstants hd
  have hc10 : P.c1 = 0 := by
    simpa [P, hc7] using hc1
  exact {
    a0 := T.normalizedP.coeff 0
    a1 := T.normalizedP.coeff 1
    a2 := T.normalizedP.coeff 2
    a3 := T.normalizedP.coeff 3
    a4 := T.normalizedP.coeff 4
    rho3 := algebraMap k (RatFunc k) R.rho3
    rho4 := algebraMap k (RatFunc k) R.rho4
    hr1 := by
      have h := R.hrho1
      rw [hrho1, map_zero] at h
      simpa [T, N, targetNormalizedFaberNormalForm, P, hc7, hc5, hc4,
        hc2, hc10] using h
    hr2 := by
      have h := R.hrho2
      rw [hrho2, map_zero] at h
      simpa [T, N, targetNormalizedFaberNormalForm, P, hc7, hc5, hc4,
        hc2, hc10] using h
    hr3 := by
      have h := R.hrho3
      simpa [T, N, targetNormalizedFaberNormalForm, P, hc7, hc5, hc4,
        hc2, hc10] using h
    hr4 := by
      have h := R.hrho4
      simpa [T, N, targetNormalizedFaberNormalForm, P, hc7, hc5, hc4,
        hc2, hc10] using h
  }

/-- With an original DS boundary witness for the special zero-invariant
sheet, the same literal source produces the complete terminal source already
excluded by the rational-fibre theorem. -/
noncomputable def targetNormalizedLaterTerminalSource
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hd : S.faberConstantParameters.d = 0)
    (hc7 : S.faberConstantParameters.c7 = 0)
    (hc5 : S.faberConstantParameters.c5 = 0)
    (hc4 : S.faberConstantParameters.c4 = 0)
    (hc2 : S.faberConstantParameters.c2 = 0)
    (hc1 : S.faberConstantParameters.c1 -
      7 * S.faberConstantParameters.c7 *
        S.faberConstantParameters.c3 / 9 = 0)
    (hrho1 : (S.targetNormalizedFirstIntegralConstants hd).rho1 = 0)
    (hrho2 : (S.targetNormalizedFirstIntegralConstants hd).rho2 = 0)
    (boundary :
      6 * (S.targetNormalizedFirstIntegralConstants hd).rho3 = 0 →
      6 * (S.targetNormalizedFirstIntegralConstants hd).rho4 = 0 →
      GCD369CubeDSBoundarySource k) :
    GCD369CubeLaterRatFuncTerminalSource k := by
  let T := S.targetNormalizedSource
  let P := S.faberConstantParameters
  let N := S.targetNormalizedFaberNormalForm hd
  let R := S.targetNormalizedFirstIntegralConstants hd
  let L := S.targetNormalizedLaterInvariantSource hd hc7 hc5 hc4 hc2 hc1
    hrho1 hrho2
  have hc10 : P.c1 = 0 := by
    simpa [P, hc7] using hc1
  have hrow := T.faberLowerRowsOfNormalForm N
  have hrow5 :
      6 * GCD369CubeRatFuncDerivative
          (GCD369CubeFaberR5
            (T.normalizedP.coeff 0) (T.normalizedP.coeff 1)
            (T.normalizedP.coeff 2) (T.normalizedP.coeff 3)
            (T.normalizedP.coeff 4)
            N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) =
        algebraMap k (RatFunc k) T.j / T.sRat :=
    hrow.2.2.2.2
  have hsRat : T.sRat ≠ 0 := RatFunc.algebraMap_ne_zero T.hs
  have hterminal :
      T.sRat * GCD369CubeRatFuncDerivative
          (GCD369CubeFaberR5
            (T.normalizedP.coeff 0) (T.normalizedP.coeff 1)
            (T.normalizedP.coeff 2) (T.normalizedP.coeff 3)
            (T.normalizedP.coeff 4)
            N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) =
        algebraMap k (RatFunc k) (T.j / 6) := by
    calc
      T.sRat * GCD369CubeRatFuncDerivative
          (GCD369CubeFaberR5
            (T.normalizedP.coeff 0) (T.normalizedP.coeff 1)
            (T.normalizedP.coeff 2) (T.normalizedP.coeff 3)
            (T.normalizedP.coeff 4)
            N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) =
          T.sRat *
            (6 * GCD369CubeRatFuncDerivative
              (GCD369CubeFaberR5
                (T.normalizedP.coeff 0) (T.normalizedP.coeff 1)
                (T.normalizedP.coeff 2) (T.normalizedP.coeff 3)
                (T.normalizedP.coeff 4)
                N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1)) / 6 := by ring
      _ = T.sRat * (algebraMap k (RatFunc k) T.j / T.sRat) / 6 := by
        rw [hrow5]
      _ = algebraMap k (RatFunc k) (T.j / 6) := by
        rw [map_div₀, map_ofNat]
        field_simp [hsRat]
  exact {
    faber := L
    mu := 6 * R.rho3
    nu := 6 * R.rho4
    j := T.j / 6
    s := T.s
    hs := T.hs
    hj := div_ne_zero T.hj (by norm_num)
    hrho3const := by
      change 6 * algebraMap k (RatFunc k) R.rho3 =
        algebraMap k (RatFunc k) (6 * R.rho3)
      rw [map_mul, map_ofNat]
    hrho4const := by
      change 6 * algebraMap k (RatFunc k) R.rho4 =
        algebraMap k (RatFunc k) (6 * R.rho4)
      rw [map_mul, map_ofNat]
    hterminal := by
      simpa [T, L, targetNormalizedLaterInvariantSource, N,
        targetNormalizedFaberNormalForm, P, hc7, hc5, hc4, hc2, hc1,
        hc10, sRat] using hterminal
    boundary := by
      intro hmu hnu
      exact boundary (by simpa [R] using hmu) (by simpa [R] using hnu)
  }

/-- The zero-early-load stratum is impossible as soon as its fully zero
specialization supplies the original DS boundary forced at that pole. -/
theorem targetNormalizedLater_empty
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k)
    (hd : S.faberConstantParameters.d = 0)
    (hc7 : S.faberConstantParameters.c7 = 0)
    (hc5 : S.faberConstantParameters.c5 = 0)
    (hc4 : S.faberConstantParameters.c4 = 0)
    (hc2 : S.faberConstantParameters.c2 = 0)
    (hc1 : S.faberConstantParameters.c1 -
      7 * S.faberConstantParameters.c7 *
        S.faberConstantParameters.c3 / 9 = 0)
    (hrho1 : (S.targetNormalizedFirstIntegralConstants hd).rho1 = 0)
    (hrho2 : (S.targetNormalizedFirstIntegralConstants hd).rho2 = 0)
    (boundary :
      6 * (S.targetNormalizedFirstIntegralConstants hd).rho3 = 0 →
      6 * (S.targetNormalizedFirstIntegralConstants hd).rho4 = 0 →
      GCD369CubeDSBoundarySource k) : False :=
  (S.targetNormalizedLaterTerminalSource hd hc7 hc5 hc4 hc2 hc1
    hrho1 hrho2 boundary).empty

end GCD369CubePolynomialSource

#print axioms
  GCD369CubePolynomialSource.targetNormalizedLaterInvariantSource
#print axioms
  GCD369CubePolynomialSource.targetNormalizedLaterTerminalSource
#print axioms GCD369CubePolynomialSource.targetNormalizedLater_empty
