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

/-- The quotient-rule derivative annihilates zero. -/
theorem GCD369CubeRatFuncDerivative_zero
    {k : Type*} [Field k] :
    GCD369CubeRatFuncDerivative (0 : RatFunc k) = 0 := by
  rw [show (0 : RatFunc k) =
      algebraMap k[X] (RatFunc k) 0 /
        algebraMap k[X] (RatFunc k) 1 by simp]
  rw [GCD369CubeRatFuncDerivative_div 0 1 one_ne_zero]
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

/-- A reduced rational DS parameter presents its terminal seventh power
with the expected scalar numerator. -/
theorem GCD369CubeDSRatFuncFormula
    {k : Type*} [Field k] [CharZero k]
    (lambda : RatFunc k) (LN LB : k[X])
    (hLB : LB ≠ 0)
    (hlambda : lambda =
      algebraMap k[X] (RatFunc k) LN /
        algebraMap k[X] (RatFunc k) LB) :
    (27 / 2) * lambda ^ 7 =
      algebraMap k[X] (RatFunc k) (C (27 / 2) * LN ^ 7) /
        algebraMap k[X] (RatFunc k) (LB ^ 7) := by
  have hLBmap : algebraMap k[X] (RatFunc k) LB ≠ 0 :=
    RatFunc.algebraMap_ne_zero hLB
  rw [hlambda]
  simp only [map_mul, map_pow, RatFunc.algebraMap_C]
  field_simp [hLBmap]
  rw [← RatFunc.algebraMap_eq_C]
  simp only [map_ofNat, map_div₀]
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

set_option maxHeartbeats 4000000 in
/-- On the zero invariant fibre, the exact source classification rules out
the common-cubic component via its zero terminal value and routes the other
component to the DS seventh-power exclusion.  The reduced DS presentation is
constructed internally; only the original polynomial-boundary witness is
retained as an input. -/
theorem zeroInvariantRatFuncTerminalExclusion
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubeLaterInvariantSource (RatFunc k))
    (j : k) (hj : j ≠ 0) (s : k[X]) (hs : s ≠ 0)
    (hrho3 : S.rho3 = 0) (hrho4 : S.rho4 = 0)
    (hterminal :
      algebraMap k[X] (RatFunc k) s *
          GCD369CubeRatFuncDerivative
            (GCD369CubeFaberR5
              S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0) =
        algebraMap k (RatFunc k) j)
    (hboundary : ∃ r : k,
      eval r (X ^ 6 + C 4 * X ^ 4 + C 10 * X ^ 2 + C 6 : k[X]) = 0 ∧
      eval r (X ^ 9 + C 6 * X ^ 7 + C 21 * X ^ 5 + C 35 * X ^ 3 +
        C (63 / 2) * X : k[X]) = 0) : False := by
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
    have hQ : Q ≠ 0 := by
      exact pow_ne_zero 7 hLB
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
    apply GCD369CubeDSAllCoreTerminalExclusion
      j hj (C (27 / 2 : k) * s) LN LB hsScaled hLN hLB
        hlambdaReduced ?_ hboundary
    dsimp only [P, Q] at hcleared
    simp only [derivative_mul, derivative_C, zero_mul, zero_add] at hcleared
    convert hcleared using 1 <;> ring

/-- A nonzero terminal derivative eliminates the zero-bracket alternative
from the exact unmixed source split.  Hence every surviving unmixed source
lies on the explicit elliptic sheet, with no sheet choice supplied by the
caller. -/
theorem unmixedEllipticCoordinatesOfTerminal
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeLaterInvariantSource (RatFunc k))
    (j : k) (hj : j ≠ 0) (s : k[X])
    (hrho4 : S.rho4 = 0)
    (hterminal :
      algebraMap k[X] (RatFunc k) s *
          GCD369CubeRatFuncDerivative
            (GCD369CubeFaberR5
              S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0) =
        algebraMap k (RatFunc k) j) :
    S.a3 = 0 ∧ S.a1 = 0 ∧
      384 * S.a2 ^ 3 - 432 * S.a2 ^ 2 * S.a4 ^ 2 +
          144 * S.a2 * S.a4 ^ 4 - 15 * S.a4 ^ 6 +
          6144 * S.rho3 = 0 ∧
      48 * S.a0 - 12 * S.a2 * S.a4 + 3 * S.a4 ^ 3 = 0 := by
  have hjmap : algebraMap k (RatFunc k) j ≠ 0 := by
    rw [RatFunc.algebraMap_eq_C]
    simpa using RatFunc.C_injective.ne hj
  have hsheets := S.unmixedCoordinates hrho4
  dsimp only at hsheets
  rcases hsheets with hzero | helliptic
  · rcases hzero with ⟨hA, hB, _hquadratic⟩
    have hr5zero := S.zeroSheetTerminalValue hA hB
    rw [hr5zero, GCD369CubeRatFuncDerivative_zero, mul_zero] at hterminal
    exact False.elim (hjmap hterminal.symm)
  · exact helliptic

end GCD369CubeLaterInvariantSource

#print axioms GCD369CubeRatFuncReducedPresentation
#print axioms GCD369CubeRatFuncDerivative_div
#print axioms GCD369CubeRatFuncDerivative_zero
#print axioms GCD369CubeMixedCuspRatFuncFormula
#print axioms GCD369CubeDSRatFuncFormula
#print axioms
  GCD369CubeLaterInvariantSource.mixedCuspRatFuncTerminalExclusion
#print axioms
  GCD369CubeLaterInvariantSource.zeroInvariantRatFuncTerminalExclusion
#print axioms
  GCD369CubeLaterInvariantSource.unmixedEllipticCoordinatesOfTerminal
