import FaberLaterSource
import FiniteDSBoundaryContradiction

noncomputable section
open Polynomial

/-! # Boundary-free terminal exclusion for a literal polynomial source

The finite original-polynomial boundary rules out the zero-invariant
Davenport--Stothers sheet internally.  Consequently the target-normalized
later fibre is empty without a caller-supplied boundary witness.
-/

namespace GCD369CubeLaterInvariantSource

/-- Exhaust the later rational fibre when the caller supplies a contradiction
for the fully zero invariant specialization.  This is the boundary-free
analogue of `GCD369CubeLaterRatFuncTerminalSource.empty`. -/
theorem ratFuncTerminalExclusion_of_zeroInvariant
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (L : GCD369CubeLaterInvariantSource (RatFunc k))
    (mu nu j : k) (hj : j ≠ 0) (s : k[X]) (hs : s ≠ 0)
    (hrho3const : 6 * L.rho3 = algebraMap k (RatFunc k) mu)
    (hrho4const : 6 * L.rho4 = algebraMap k (RatFunc k) nu)
    (hterminal :
      algebraMap k[X] (RatFunc k) s *
          GCD369CubeRatFuncDerivative
            (GCD369CubeFaberR5
              L.a0 L.a1 L.a2 L.a3 L.a4 0 0 0 0 0 0 0) =
        algebraMap k (RatFunc k) j)
    (hzero : L.rho3 = 0 → L.rho4 = 0 → False) : False := by
  by_cases hnu : nu = 0
  · have hrho4 : L.rho4 = 0 := by
      have h := hrho4const
      rw [hnu, map_zero] at h
      linear_combination (1 / 6 : RatFunc k) * h
    by_cases hmu : mu = 0
    · have hrho3 : L.rho3 = 0 := by
        have h := hrho3const
        rw [hmu, map_zero] at h
        linear_combination (1 / 6 : RatFunc k) * h
      exact hzero hrho3 hrho4
    · exact L.unmixedEllipticRatFuncTerminalExclusion
        mu j hmu hj s hrho3const hrho4 hterminal
  · by_cases hmu : mu = 0
    · have hrho3 : L.rho3 = 0 := by
        have h := hrho3const
        rw [hmu, map_zero] at h
        linear_combination (1 / 6 : RatFunc k) * h
      exact L.mixedCuspRatFuncTerminalExclusion
        nu j hnu hj s hs hrho3 hrho4const hterminal
    · exact L.mixedEllipticRatFuncTerminalExclusion
        mu nu j hmu hnu hj s hrho3const hrho4const hterminal

end GCD369CubeLaterInvariantSource

namespace GCD369CubePolynomialSource

/-- Once all early loads through `rho2` vanish, a nonconstant literal source
is impossible.  The later elliptic and cusp fibres are handled by the
rational terminal theorem, and the zero fibre by its own finite pole. -/
theorem targetNormalizedLater_empty_without_boundary
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k)
    (hsdegree : 0 < S.s.natDegree)
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
  have hsdegreeT : 0 < T.s.natDegree := by
    simpa [T, targetNormalizedSource] using hsdegree
  obtain ⟨a, hpole⟩ :=
    T.finiteNormalizedCoeffPole_of_nonconstant hsdegreeT
  apply L.ratFuncTerminalExclusion_of_zeroInvariant
    (6 * R.rho3) (6 * R.rho4) (T.j / 6) hj6 T.s T.hs
      hrho3const hrho4const hterminal
  intro hrho3zero hrho4zero
  exact L.zero_empty_of_coeff_pole T
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    hrho3zero hrho4zero (T.j / 6) hj6 T.s T.hs hterminal a hpole

end GCD369CubePolynomialSource

#print axioms
  GCD369CubePolynomialSource.targetNormalizedLater_empty_without_boundary
#print axioms
  GCD369CubeLaterInvariantSource.ratFuncTerminalExclusion_of_zeroInvariant
