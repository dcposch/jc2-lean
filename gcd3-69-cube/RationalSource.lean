import SourceBridge

noncomputable section

open Polynomial

universe u

/-! # Rational-function terminal handoff

This module turns source-derived later-invariant formulas over `k(x)` into
the reduced polynomial presentations consumed by the terminal exclusions in
`Solution`.  It deliberately uses the canonical numerator and denominator;
no rational landing presentation is chosen by the caller.
-/

/-- Every rational function has its canonical reduced polynomial
numerator/denominator presentation, with no common finite zero. -/
theorem GCD369CubeRatFuncReducedPresentation
    {k : Type*} [Field k] (r : RatFunc k) :
    ∃ N B : k[X], B ≠ 0 ∧
      r = algebraMap k[X] (RatFunc k) N / algebraMap k[X] (RatFunc k) B ∧
      ∀ z : k, eval z N = 0 → eval z B ≠ 0 := by
  refine ⟨r.num, r.denom, r.denom_ne_zero,
    (RatFunc.num_div_denom r).symm, ?_⟩
  intro z hnum hden
  obtain ⟨A, B, hbezout⟩ := r.isCoprime_num_denom
  have heval := congrArg (fun p : k[X] => eval z p) hbezout
  simp only [eval_add, eval_mul, eval_one, hnum, hden, mul_zero, add_zero]
    at heval
  exact zero_ne_one heval

/-- The standard quotient-rule derivative on `k(x)`, defined directly on
fraction representatives. -/
noncomputable def GCD369CubeRatFuncDerivative
    {k : Type*} [Field k] (r : RatFunc k) : RatFunc k :=
  r.liftOn'
    (fun p q ↦
      (algebraMap k[X] (RatFunc k) q *
          algebraMap k[X] (RatFunc k) p.derivative -
        algebraMap k[X] (RatFunc k) p *
          algebraMap k[X] (RatFunc k) q.derivative) /
        algebraMap k[X] (RatFunc k) q ^ 2)
    (by
      intro p q a hq ha
      have hma : algebraMap k[X] (RatFunc k) a ≠ 0 :=
        RatFunc.algebraMap_ne_zero ha
      have hmq : algebraMap k[X] (RatFunc k) q ≠ 0 :=
        RatFunc.algebraMap_ne_zero hq
      simp only [derivative_mul, map_mul, map_add]
      field_simp [hma, hmq]
      ring)

/-- The source derivative satisfies the quotient rule on a polynomial
presentation. -/
theorem GCD369CubeRatFuncDerivative_div
    {k : Type*} [Field k] (p q : k[X]) (_hq : q ≠ 0) :
    GCD369CubeRatFuncDerivative
        (algebraMap k[X] (RatFunc k) p /
          algebraMap k[X] (RatFunc k) q) =
      (algebraMap k[X] (RatFunc k) q *
          algebraMap k[X] (RatFunc k) p.derivative -
        algebraMap k[X] (RatFunc k) p *
          algebraMap k[X] (RatFunc k) q.derivative) /
        algebraMap k[X] (RatFunc k) q ^ 2 := by
  unfold GCD369CubeRatFuncDerivative
  rw [RatFunc.liftOn'_div]
  intro a
  simp

/-- Substitution of a reduced rational cusp parameter gives exactly the
polynomial numerator and denominator used by the terminal theorem. -/
theorem GCD369CubeMixedCuspRatFuncFormula
    {k : Type*} [Field k] [CharZero k]
    (nu : k) (lambda : RatFunc k) (LN LB : k[X])
    (hLN : LN ≠ 0) (hLB : LB ≠ 0)
    (hlambda : lambda =
      algebraMap k[X] (RatFunc k) LN /
        algebraMap k[X] (RatFunc k) LB) :
    27 * lambda ^ 7 / 2 -
        (algebraMap k (RatFunc k) nu) ^ 2 / (1458 * lambda ^ 6) =
      algebraMap k[X] (RatFunc k)
          (C 19683 * LN ^ 13 - C (nu ^ 2) * LB ^ 13) /
        algebraMap k[X] (RatFunc k) (C 1458 * LN ^ 6 * LB ^ 7) := by
  have hLNmap : algebraMap k[X] (RatFunc k) LN ≠ 0 :=
    RatFunc.algebraMap_ne_zero hLN
  have hLBmap : algebraMap k[X] (RatFunc k) LB ≠ 0 :=
    RatFunc.algebraMap_ne_zero hLB
  rw [hlambda]
  simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
  field_simp [hLNmap, hLBmap]
  rw [← RatFunc.algebraMap_eq_C]
  simp only [map_ofNat]
  ring

namespace GCD369CubeLaterInvariantSource

set_option maxHeartbeats 4000000 in
/-- A singular mixed Faber source over `k(x)` cannot satisfy the terminal
Keller derivative equation.  The cusp parameter and its reduced polynomial
presentation are both constructed internally before applying the existing
all-core terminal exclusion. -/
theorem mixedCuspRatFuncTerminalExclusion
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubeLaterInvariantSource (RatFunc k))
    (nu j : k) (hnu : nu ≠ 0) (hj : j ≠ 0)
    (s : k[X]) (hs : s ≠ 0)
    (hrho3 : S.rho3 = 0)
    (hrho4const : 6 * S.rho4 = algebraMap k (RatFunc k) nu)
    (hterminal :
      algebraMap k[X] (RatFunc k) s *
          GCD369CubeRatFuncDerivative
            (GCD369CubeFaberR5
              S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0) =
        algebraMap k (RatFunc k) j) : False := by
  have hnumap : algebraMap k (RatFunc k) nu ≠ 0 := by
    rw [RatFunc.algebraMap_eq_C]
    simpa using RatFunc.C_injective.ne hnu
  have hrho4 : S.rho4 ≠ 0 := by
    intro hz
    apply hnumap
    rw [← hrho4const, hz]
    ring
  let A : RatFunc k := 4 * S.a2 - S.a4 ^ 2
  let B : RatFunc k := 2 * S.a1 - S.a3 * S.a4
  let w : RatFunc k := 4 * S.a0 - S.a3 ^ 2
  let V : RatFunc k := w + 8 * B ^ 2 / A
  let lambda : RatFunc k := V / A
  have hcusp := S.mixedCuspCoordinates hrho4 hrho3
  dsimp only at hcusp
  change A ≠ 0 ∧ V ≠ 0 ∧ lambda ≠ 0 ∧
    A = 24 * lambda ^ 2 ∧ V = 24 * lambda ^ 3 ∧
    GCD369CubeFaberR5 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
      27 * lambda ^ 7 / 2 - (6 * S.rho4) ^ 2 / (1458 * lambda ^ 6)
      at hcusp
  rcases hcusp with ⟨_hA, _hV, hlambda0, _hAlambda, _hVlambda, hr5⟩
  obtain ⟨LN, LB, hLB, hlambda, hlambdaReduced⟩ :=
    GCD369CubeRatFuncReducedPresentation lambda
  have hLN : LN ≠ 0 := by
    intro hLN
    apply hlambda0
    rw [hlambda, hLN]
    simp
  have hr5base :
      GCD369CubeFaberR5 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
        27 * lambda ^ 7 / 2 -
          (algebraMap k (RatFunc k) nu) ^ 2 / (1458 * lambda ^ 6) := by
    calc
      GCD369CubeFaberR5 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
          27 * lambda ^ 7 / 2 -
            (6 * S.rho4) ^ 2 / (1458 * lambda ^ 6) := hr5
      _ = 27 * lambda ^ 7 / 2 -
          (algebraMap k (RatFunc k) nu) ^ 2 / (1458 * lambda ^ 6) := by
        rw [hrho4const]
  let P : k[X] := C 19683 * LN ^ 13 - C (nu ^ 2) * LB ^ 13
  let Q : k[X] := C 1458 * LN ^ 6 * LB ^ 7
  have hr5PQ :
      GCD369CubeFaberR5 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
        algebraMap k[X] (RatFunc k) P /
          algebraMap k[X] (RatFunc k) Q := by
    exact hr5base.trans
      (GCD369CubeMixedCuspRatFuncFormula nu lambda LN LB hLN hLB hlambda)
  have hQ : Q ≠ 0 := by
    dsimp only [Q]
    exact mul_ne_zero
      (mul_ne_zero (C_ne_zero.mpr (by norm_num)) (pow_ne_zero 6 hLN))
      (pow_ne_zero 7 hLB)
  have hderivative := congrArg GCD369CubeRatFuncDerivative hr5PQ
  rw [GCD369CubeRatFuncDerivative_div P Q hQ] at hderivative
  rw [hderivative] at hterminal
  apply GCD369CubeMixedCuspAllCoreTerminalExclusion
    nu j hnu hj s LN LB hs hLN hLB hlambdaReduced
  dsimp only
  change s * (derivative P * Q - P * derivative Q) = C j * Q ^ 2
  apply RatFunc.algebraMap_injective k
  have hQmap : algebraMap k[X] (RatFunc k) Q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hQ
  field_simp [hQmap] at hterminal
  simp only [map_mul, map_sub, map_pow, RatFunc.algebraMap_C]
  rw [← RatFunc.algebraMap_eq_C]
  simpa only [mul_comm] using hterminal

end GCD369CubeLaterInvariantSource

#print axioms GCD369CubeRatFuncReducedPresentation
#print axioms GCD369CubeRatFuncDerivative_div
#print axioms GCD369CubeMixedCuspRatFuncFormula
#print axioms
  GCD369CubeLaterInvariantSource.mixedCuspRatFuncTerminalExclusion
