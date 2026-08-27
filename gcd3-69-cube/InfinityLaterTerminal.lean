import FaberLaterPolynomialExclusion

noncomputable section
open Polynomial

/-! # Constant-core terminal exclusion at infinity

On the constant-core infinity branch, the zero later-invariant fibre does
not need an original finite boundary witness.  Its Davenport--Stothers
component is a seventh power, and the constant-core rational primitive
exclusion closes that component directly.
-/

namespace GCD369CubeLaterInvariantSource

set_option maxHeartbeats 4000000 in
/-- The zero later-invariant rational fibre is empty when the polynomial
core is constant.  The common-cubic component has zero terminal value, while
the Davenport--Stothers component contradicts seventh-power exactness. -/
theorem zeroInvariantRatFuncConstantCoreTerminalExclusion
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubeLaterInvariantSource (RatFunc k))
    (j : k) (hj : j ≠ 0) (s : k[X]) (hs : s ≠ 0)
    (hsdegree : s.natDegree = 0)
    (hrho3 : S.rho3 = 0) (hrho4 : S.rho4 = 0)
    (hterminal :
      algebraMap k[X] (RatFunc k) s *
          GCD369CubeRatFuncDerivative
            (GCD369CubeFaberR5
              S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0) =
        algebraMap k (RatFunc k) j) : False := by
  have hjmap : algebraMap k (RatFunc k) j ≠ 0 := by
    rw [RatFunc.algebraMap_eq_C]
    simpa using RatFunc.C_injective.ne hj
  have hr3zero :
      GCD369CubeFaberR3
        S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 = 0 :=
    S.hr3.trans hrho3
  have hr4zero :
      GCD369CubeFaberR4
        S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 = 0 :=
    S.hr4.trans hrho4
  rcases GCD369CubeFaberLeadingComponentClassification
      S.a0 S.a1 S.a2 S.a3 S.a4 S.hr1 S.hr2 hr3zero hr4zero with
    hcommon | hds
  · rcases hcommon with ⟨u, v, ha4, ha3, ha2, ha1, ha0⟩
    have hr5zero :
        GCD369CubeFaberR5
          S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 = 0 := by
      rw [ha0, ha1, ha2, ha3, ha4]
      exact (GCD369CubeFaberCommonValues u v).2.2.2.2
    rw [hr5zero, GCD369CubeRatFuncDerivative_zero, mul_zero] at hterminal
    exact hjmap hterminal.symm
  · rcases hds with ⟨lambda, ha4, ha3, ha2, ha1, ha0⟩
    have hr5DS :
        GCD369CubeFaberR5
          S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
            (27 / 2) * lambda ^ 7 := by
      rw [ha0, ha1, ha2, ha3, ha4]
      exact (GCD369CubeFaberDSValues lambda).2.2.2.2
    have hlambda0 : lambda ≠ 0 := by
      intro hlambda0
      have hr5zero :
          GCD369CubeFaberR5
            S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 = 0 := by
        rw [hr5DS, hlambda0]
        norm_num
      rw [hr5zero, GCD369CubeRatFuncDerivative_zero, mul_zero] at hterminal
      exact hjmap hterminal.symm
    obtain ⟨LN, LB, hLB, hlambda, hlambdaReduced⟩ :=
      GCD369CubeRatFuncReducedPresentation lambda
    have hLN : LN ≠ 0 := by
      intro hLN
      apply hlambda0
      rw [hlambda, hLN]
      simp
    let P : k[X] := C (27 / 2) * LN ^ 7
    let Q : k[X] := LB ^ 7
    have hr5PQ :
        GCD369CubeFaberR5
            S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
          algebraMap k[X] (RatFunc k) P /
            algebraMap k[X] (RatFunc k) Q := by
      exact hr5DS.trans (GCD369CubeDSRatFuncFormula lambda LN LB hLB hlambda)
    have hQ : Q ≠ 0 := pow_ne_zero 7 hLB
    have hderivative := congrArg GCD369CubeRatFuncDerivative hr5PQ
    rw [GCD369CubeRatFuncDerivative_div P Q hQ] at hderivative
    rw [hderivative] at hterminal
    have hcleared :
        s * (derivative P * Q - P * derivative Q) = C j * Q ^ 2 := by
      apply RatFunc.algebraMap_injective k
      have hQmap : algebraMap k[X] (RatFunc k) Q ≠ 0 :=
        RatFunc.algebraMap_ne_zero hQ
      field_simp [hQmap] at hterminal
      simp only [map_mul, map_sub, map_pow, RatFunc.algebraMap_C]
      rw [← RatFunc.algebraMap_eq_C]
      simpa only [mul_comm] using hterminal
    have hscale : C (27 / 2 : k) ≠ 0 := C_ne_zero.mpr (by norm_num)
    have hsScaled : C (27 / 2 : k) * s ≠ 0 := mul_ne_zero hscale hs
    have hsScaledDegree : (C (27 / 2 : k) * s).natDegree = 0 := by
      rw [natDegree_C_mul (by norm_num : (27 / 2 : k) ≠ 0)]
      exact hsdegree
    apply GCD369CubeDSConstantCoreTerminalExclusion
      j hj (C (27 / 2 : k) * s) LN LB hsScaled hLN hLB
        hsScaledDegree hlambdaReduced
    dsimp only [P, Q] at hcleared
    simp only [derivative_mul, derivative_C, zero_mul, zero_add] at hcleared
    convert hcleared using 1 <;> ring

end GCD369CubeLaterInvariantSource

namespace GCD369CubePolynomialSource

/-- Once all early loads through `rho2` vanish, a constant-core literal
source is impossible.  Nonzero later invariants use the existing rational
terminal exclusions; the zero invariant fibre uses constant-core
seventh-power exactness. -/
theorem targetNormalizedLater_empty_of_constantCore
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k)
    (hsdegree : S.s.natDegree = 0)
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
    False := by
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
  have hterminalRaw :
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
  have hterminal :
      algebraMap k[X] (RatFunc k) T.s *
          GCD369CubeRatFuncDerivative
            (GCD369CubeFaberR5
              L.a0 L.a1 L.a2 L.a3 L.a4 0 0 0 0 0 0 0) =
        algebraMap k (RatFunc k) (T.j / 6) := by
    simpa [T, L, targetNormalizedLaterInvariantSource, N,
      targetNormalizedFaberNormalForm, P, hc7, hc5, hc4, hc2, hc1,
      hc10, sRat] using hterminalRaw
  have hrho3const :
      6 * L.rho3 = algebraMap k (RatFunc k) (6 * R.rho3) := by
    change 6 * algebraMap k (RatFunc k) R.rho3 =
      algebraMap k (RatFunc k) (6 * R.rho3)
    rw [map_mul, map_ofNat]
  have hrho4const :
      6 * L.rho4 = algebraMap k (RatFunc k) (6 * R.rho4) := by
    change 6 * algebraMap k (RatFunc k) R.rho4 =
      algebraMap k (RatFunc k) (6 * R.rho4)
    rw [map_mul, map_ofNat]
  have hj6 : T.j / 6 ≠ 0 := div_ne_zero T.hj (by norm_num)
  have hsdegreeT : T.s.natDegree = 0 := by
    simpa [T, targetNormalizedSource] using hsdegree
  apply L.ratFuncTerminalExclusion_of_zeroInvariant
    (6 * R.rho3) (6 * R.rho4) (T.j / 6) hj6 T.s T.hs
      hrho3const hrho4const hterminal
  intro hrho3zero hrho4zero
  exact L.zeroInvariantRatFuncConstantCoreTerminalExclusion
    (T.j / 6) hj6 T.s T.hs hsdegreeT hrho3zero hrho4zero hterminal

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeLaterInvariantSource.zeroInvariantRatFuncConstantCoreTerminalExclusion
#print axioms
  GCD369CubePolynomialSource.targetNormalizedLater_empty_of_constantCore
