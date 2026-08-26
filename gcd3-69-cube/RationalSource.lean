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

/-- The quotient-rule derivative annihilates embedded base-field
constants. -/
theorem GCD369CubeRatFuncDerivative_C
    {k : Type*} [Field k] (c : k) :
    GCD369CubeRatFuncDerivative (algebraMap k (RatFunc k) c) = 0 := by
  rw [show algebraMap k (RatFunc k) c =
      algebraMap k[X] (RatFunc k) (C c) /
        algebraMap k[X] (RatFunc k) 1 by
    simp [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]]
  rw [GCD369CubeRatFuncDerivative_div (C c) 1 one_ne_zero]
  simp

/-- The terminal Faber invariant commutes with embedding the base field into
its rational-function field. -/
theorem GCD369CubeFaberR5_C
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1 : k) :
    GCD369CubeFaberR5
        (algebraMap k (RatFunc k) a0) (algebraMap k (RatFunc k) a1)
        (algebraMap k (RatFunc k) a2) (algebraMap k (RatFunc k) a3)
        (algebraMap k (RatFunc k) a4) (algebraMap k (RatFunc k) d)
        (algebraMap k (RatFunc k) c7) (algebraMap k (RatFunc k) c5)
        (algebraMap k (RatFunc k) c4) (algebraMap k (RatFunc k) c3)
        (algebraMap k (RatFunc k) c2) (algebraMap k (RatFunc k) c1) =
      algebraMap k (RatFunc k)
        (GCD369CubeFaberR5 a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1) := by
  dsimp only [GCD369CubeFaberR5]
  simp only [map_add, map_sub, map_mul, map_pow, map_div₀, map_ofNat]

set_option maxHeartbeats 4000000 in
/-- A nonzero rational point on a nondegenerate `(2,3,6)` curve has a
canonical weighted polynomial presentation.  The curve equation forces the
two monic canonical denominators `Q,S` to satisfy `Q² = S³`; cancellation
then produces the common denominator `D` with weights three and two. -/
theorem GCD369CubeRatFuncWeightedPresentation
    {k : Type*} [Field k]
    (u v w : k) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (Yc Xc : RatFunc k) (hYc : Yc ≠ 0) (hXc : Xc ≠ 0)
    (hcurve :
      algebraMap k (RatFunc k) u * Yc ^ 2 +
          algebraMap k (RatFunc k) v * Xc ^ 3 +
          algebraMap k (RatFunc k) w = 0) :
    ∃ M N D : k[X], M ≠ 0 ∧ N ≠ 0 ∧ D ≠ 0 ∧
      IsCoprime M N ∧
      Yc = algebraMap k[X] (RatFunc k) M /
        algebraMap k[X] (RatFunc k) (D ^ 3) ∧
      Xc = algebraMap k[X] (RatFunc k) N /
        algebraMap k[X] (RatFunc k) (D ^ 2) := by
  let P : k[X] := Yc.num
  let Q : k[X] := Yc.denom
  let R : k[X] := Xc.num
  let S : k[X] := Xc.denom
  have hP : P ≠ 0 := by
    exact RatFunc.num_ne_zero hYc
  have hQ : Q ≠ 0 := by
    exact RatFunc.denom_ne_zero Yc
  have hR : R ≠ 0 := by
    exact RatFunc.num_ne_zero hXc
  have hS : S ≠ 0 := by
    exact RatFunc.denom_ne_zero Xc
  have hPQ : IsCoprime P Q := Yc.isCoprime_num_denom
  have hRS : IsCoprime R S := Xc.isCoprime_num_denom
  have hQmap : algebraMap k[X] (RatFunc k) Q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hQ
  have hSmap : algebraMap k[X] (RatFunc k) S ≠ 0 :=
    RatFunc.algebraMap_ne_zero hS
  have hclear :
      C u * P ^ 2 * S ^ 3 + C v * R ^ 3 * Q ^ 2 +
          C w * Q ^ 2 * S ^ 3 = 0 := by
    apply RatFunc.algebraMap_injective k
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_mul, map_mul,
      map_pow, map_pow, map_mul, map_mul, map_pow, map_pow, map_zero,
      RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_C]
    rw [← RatFunc.algebraMap_eq_C]
    rw [← RatFunc.num_div_denom Yc, ← RatFunc.num_div_denom Xc]
      at hcurve
    change algebraMap k (RatFunc k) u *
          (algebraMap k[X] (RatFunc k) P /
            algebraMap k[X] (RatFunc k) Q) ^ 2 +
        algebraMap k (RatFunc k) v *
          (algebraMap k[X] (RatFunc k) R /
            algebraMap k[X] (RatFunc k) S) ^ 3 +
        algebraMap k (RatFunc k) w = 0 at hcurve
    field_simp [hQmap, hSmap] at hcurve
    convert hcurve using 1 <;> ring
  have hS3dvdQ2 : S ^ 3 ∣ Q ^ 2 := by
    have hdvd : S ^ 3 ∣ C v * R ^ 3 * Q ^ 2 := by
      have heq : C v * R ^ 3 * Q ^ 2 =
          -(C u * P ^ 2 * S ^ 3 + C w * Q ^ 2 * S ^ 3) := by
        linear_combination hclear
      rw [heq]
      apply dvd_neg.mpr
      apply dvd_add
      · exact ⟨C u * P ^ 2, by ring⟩
      · exact ⟨C w * Q ^ 2, by ring⟩
    have hcop : IsCoprime (S ^ 3) (C v * R ^ 3) := by
      rw [isCoprime_mul_unit_left_right
        (Polynomial.isUnit_C.mpr hv.isUnit)]
      exact hRS.symm.pow
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hQ2dvdS3 : Q ^ 2 ∣ S ^ 3 := by
    have hdvd : Q ^ 2 ∣ C u * P ^ 2 * S ^ 3 := by
      have heq : C u * P ^ 2 * S ^ 3 =
          -(C v * R ^ 3 * Q ^ 2 + C w * Q ^ 2 * S ^ 3) := by
        linear_combination hclear
      rw [heq]
      apply dvd_neg.mpr
      apply dvd_add
      · exact ⟨C v * R ^ 3, by ring⟩
      · exact ⟨C w * S ^ 3, by ring⟩
    have hcop : IsCoprime (Q ^ 2) (C u * P ^ 2) := by
      rw [isCoprime_mul_unit_left_right
        (Polynomial.isUnit_C.mpr hu.isUnit)]
      exact hPQ.symm.pow
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hSmonic : (S ^ 3).Monic := by
    exact (RatFunc.monic_denom Xc).pow 3
  have hQmonic : (Q ^ 2).Monic := by
    exact (RatFunc.monic_denom Yc).pow 2
  have hdenom : S ^ 3 = Q ^ 2 :=
    eq_of_monic_of_associated hSmonic hQmonic
      (associated_of_dvd_dvd hS3dvdQ2 hQ2dvdS3)
  have hS2dvdQ2 : S ^ 2 ∣ Q ^ 2 := by
    rw [← hdenom]
    exact ⟨S, by ring⟩
  obtain ⟨D, hQD⟩ :=
    (IsIntegrallyClosed.pow_dvd_pow_iff (R := k[X])
      (by norm_num : 2 ≠ 0)).mp hS2dvdQ2
  have hSD : S = D ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hS)
    calc
      S ^ 2 * S = S ^ 3 := by ring
      _ = Q ^ 2 := hdenom
      _ = (S * D) ^ 2 := by rw [hQD]
      _ = S ^ 2 * D ^ 2 := by ring
  have hQD3 : Q = D ^ 3 := by
    rw [hQD, hSD]
    ring
  have hD : D ≠ 0 := by
    intro hD
    apply hQ
    rw [hQD3, hD, zero_pow (by norm_num : 3 ≠ 0)]
  have hweighted :
      C u * P ^ 2 + C v * R ^ 3 + C w * D ^ 6 = 0 := by
    have hmul :
        (C u * P ^ 2 + C v * R ^ 3 + C w * D ^ 6) * D ^ 6 = 0 := by
      rw [hQD3, hSD] at hclear
      convert hclear using 1 <;> ring
    exact mul_right_cancel₀ (pow_ne_zero 6 hD) (hmul.trans (zero_mul _).symm)
  have hPD : IsCoprime P D := by
    apply (IsCoprime.pow_right_iff (m := 3) (by norm_num)).mp
    rwa [← hQD3]
  have hDPterms : IsCoprime (C w * D ^ 6) (C u * P ^ 2) := by
    rw [isCoprime_mul_units_left (Polynomial.isUnit_C.mpr hw.isUnit)
      (Polynomial.isUnit_C.mpr hu.isUnit)]
    exact hPD.symm.pow
  have hPRterms : IsCoprime (C u * P ^ 2) (C v * R ^ 3) := by
    have hsum : IsCoprime (C u * P ^ 2)
        (C w * D ^ 6 + C u * P ^ 2) := by
      simpa [mul_one] using (hDPterms.add_mul_left_left 1).symm
    have heq : C v * R ^ 3 = -(C w * D ^ 6 + C u * P ^ 2) := by
      linear_combination hweighted
    rw [heq]
    exact hsum.neg_right
  have hPR : IsCoprime P R := by
    apply (IsCoprime.pow_iff (m := 2) (n := 3)
      (by norm_num) (by norm_num)).mp
    exact (isCoprime_mul_units_left (Polynomial.isUnit_C.mpr hu.isUnit)
      (Polynomial.isUnit_C.mpr hv.isUnit) _ _).mp hPRterms
  refine ⟨P, R, D, hP, hR, hD, hPR, ?_, ?_⟩
  · rw [← RatFunc.num_div_denom Yc]
    change algebraMap k[X] (RatFunc k) P /
        algebraMap k[X] (RatFunc k) Q = _
    rw [hQD3]
  · rw [← RatFunc.num_div_denom Xc]
    change algebraMap k[X] (RatFunc k) R /
        algebraMap k[X] (RatFunc k) S = _
    rw [hSD]

/-- A weighted reduced polynomial presentation of a rational point on a
nondegenerate `(2,3,6)` curve is constant.  This is the exact algebraic
replacement for the smooth `P¹ → E` genus argument once such a presentation
has been constructed. -/
theorem GCD369CubeRatFuncEllipticConstancy
    {k : Type*} [Field k] [CharZero k]
    (u v w : k) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (Yc Xc : RatFunc k) (M N D : k[X])
    (hM : M ≠ 0) (hN : N ≠ 0) (hD : D ≠ 0)
    (hMN : IsCoprime M N)
    (hY : Yc = algebraMap k[X] (RatFunc k) M /
      algebraMap k[X] (RatFunc k) (D ^ 3))
    (hX : Xc = algebraMap k[X] (RatFunc k) N /
      algebraMap k[X] (RatFunc k) (D ^ 2))
    (hcurve :
      algebraMap k (RatFunc k) u * Yc ^ 2 +
          algebraMap k (RatFunc k) v * Xc ^ 3 +
          algebraMap k (RatFunc k) w = 0) :
    ∃ y0 x0 : k,
      Yc = algebraMap k (RatFunc k) y0 ∧
      Xc = algebraMap k (RatFunc k) x0 := by
  have hDmap : algebraMap k[X] (RatFunc k) D ≠ 0 :=
    RatFunc.algebraMap_ne_zero hD
  have hpoly : C u * M ^ 2 + C v * N ^ 3 + C w * D ^ 6 = 0 := by
    apply RatFunc.algebraMap_injective k
    rw [map_add, map_add, map_mul, map_pow, map_mul, map_pow, map_mul,
      map_pow, map_zero, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_C]
    rw [← RatFunc.algebraMap_eq_C]
    rw [hY, hX] at hcurve
    simp only [map_pow] at hcurve
    field_simp [hDmap] at hcurve
    convert hcurve using 1 <;> ring
  obtain ⟨hMdegree, hNdegree, hDdegree⟩ := Polynomial.flt_catalan
    (by norm_num : 2 ≠ 0) (by norm_num : 3 ≠ 0) (by norm_num : 6 ≠ 0)
    (by norm_num : 3 * 6 + 6 * 2 + 2 * 3 ≤ 2 * 3 * 6)
    (by norm_num : (2 : k) ≠ 0) (by norm_num : (3 : k) ≠ 0)
    (by norm_num : (6 : k) ≠ 0) hM hN hD hMN hu hv hw hpoly
  let m : k := M.coeff 0
  let n : k := N.coeff 0
  let d : k := D.coeff 0
  have hMC : M = C m := eq_C_of_natDegree_eq_zero hMdegree
  have hNC : N = C n := eq_C_of_natDegree_eq_zero hNdegree
  have hDC : D = C d := eq_C_of_natDegree_eq_zero hDdegree
  have hd : d ≠ 0 := by
    intro hd
    apply hD
    rw [hDC, hd, map_zero]
  refine ⟨m / d ^ 3, n / d ^ 2, ?_, ?_⟩
  · rw [hY, hMC, hDC, map_pow, RatFunc.algebraMap_C,
      RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, ← map_pow, ← map_div₀]
  · rw [hX, hNC, hDC, map_pow, RatFunc.algebraMap_C,
      RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, ← map_pow, ← map_div₀]

/-- Every rational-function point with both affine coordinates nonzero on a
nondegenerate `(2,3,6)` curve is constant.  The weighted presentation is
constructed canonically from its reduced numerator and denominator. -/
theorem GCD369CubeRatFuncEllipticConstancyOfNonzero
    {k : Type*} [Field k] [CharZero k]
    (u v w : k) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (Yc Xc : RatFunc k) (hYc : Yc ≠ 0) (hXc : Xc ≠ 0)
    (hcurve :
      algebraMap k (RatFunc k) u * Yc ^ 2 +
          algebraMap k (RatFunc k) v * Xc ^ 3 +
          algebraMap k (RatFunc k) w = 0) :
    ∃ y0 x0 : k,
      Yc = algebraMap k (RatFunc k) y0 ∧
      Xc = algebraMap k (RatFunc k) x0 := by
  obtain ⟨M, N, D, hM, hN, hD, hMN, hY, hX⟩ :=
    GCD369CubeRatFuncWeightedPresentation u v w hu hv hw Yc Xc
      hYc hXc hcurve
  exact GCD369CubeRatFuncEllipticConstancy u v w hu hv hw
    Yc Xc M N D hM hN hD hMN hY hX hcurve

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
/-- The smooth mixed source fibre is terminally empty once its rational
point is supplied in a weighted reduced `(2,3,6)` presentation.  Constancy
and the contradiction are derived internally. -/
theorem mixedEllipticRatFuncTerminalExclusionOfPresentation
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeLaterInvariantSource (RatFunc k))
    (mu nu j : k) (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hj : j ≠ 0)
    (s : k[X])
    (hrho3const : 6 * S.rho3 = algebraMap k (RatFunc k) mu)
    (hrho4const : 6 * S.rho4 = algebraMap k (RatFunc k) nu)
    (hterminal :
      algebraMap k[X] (RatFunc k) s *
          GCD369CubeRatFuncDerivative
            (GCD369CubeFaberR5
              S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0) =
        algebraMap k (RatFunc k) j)
    (M N D : k[X]) (hM : M ≠ 0) (hN : N ≠ 0) (hD : D ≠ 0)
    (hMN : IsCoprime M N)
    (hVpresentation :
      let A := 4 * S.a2 - S.a4 ^ 2
      let B := 2 * S.a1 - S.a3 * S.a4
      let w := 4 * S.a0 - S.a3 ^ 2
      let V := w + 8 * B ^ 2 / A
      V = algebraMap k[X] (RatFunc k) M /
        algebraMap k[X] (RatFunc k) (D ^ 3))
    (hApresentation :
      4 * S.a2 - S.a4 ^ 2 =
        algebraMap k[X] (RatFunc k) N /
          algebraMap k[X] (RatFunc k) (D ^ 2)) : False := by
  have hnumap : algebraMap k (RatFunc k) nu ≠ 0 := by
    rw [RatFunc.algebraMap_eq_C]
    simpa using RatFunc.C_injective.ne hnu
  have hjmap : algebraMap k (RatFunc k) j ≠ 0 := by
    rw [RatFunc.algebraMap_eq_C]
    simpa using RatFunc.C_injective.ne hj
  have hrho4 : S.rho4 ≠ 0 := by
    intro hz
    apply hnumap
    rw [← hrho4const, hz]
    ring
  let A : RatFunc k := 4 * S.a2 - S.a4 ^ 2
  let B : RatFunc k := 2 * S.a1 - S.a3 * S.a4
  let w : RatFunc k := 4 * S.a0 - S.a3 ^ 2
  let V : RatFunc k := w + 8 * B ^ 2 / A
  change V = algebraMap k[X] (RatFunc k) M /
    algebraMap k[X] (RatFunc k) (D ^ 3) at hVpresentation
  change A = algebraMap k[X] (RatFunc k) N /
    algebraMap k[X] (RatFunc k) (D ^ 2) at hApresentation
  have hmixed := S.mixedCoordinates hrho4
  dsimp only at hmixed
  change A ≠ 0 ∧
    S.rho4 = -3 * A ^ 2 * B / 512 ∧
    S.rho3 = (24 * V ^ 2 - A ^ 3) / 1024 ∧
    GCD369CubeFaberR5 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
      A * (A * V - 12 * B ^ 2) / 1024 at hmixed
  rcases hmixed with ⟨_hA, _hrho4formula, hrho3formula, _hr5formula⟩
  have hrho3clear : 1024 * S.rho3 = 24 * V ^ 2 - A ^ 3 := by
    rw [hrho3formula]
    ring
  have hcurveRaw :
      72 * V ^ 2 - 3 * A ^ 3 - 512 * (6 * S.rho3) = 0 := by
    linear_combination
      (norm := ring_nf (config := { zetaDelta := false })) -3 * hrho3clear
  have hcurve :
      algebraMap k (RatFunc k) (72 : k) * V ^ 2 +
          algebraMap k (RatFunc k) (-3 : k) * A ^ 3 +
          algebraMap k (RatFunc k) (-512 * mu) = 0 := by
    simp only [map_mul, map_neg, map_ofNat]
    rw [← hrho3const]
    simpa only [sub_eq_add_neg, neg_mul] using hcurveRaw
  obtain ⟨v0, a0, hVC, hAC⟩ := GCD369CubeRatFuncEllipticConstancy
    (72 : k) (-3 : k) (-512 * mu) (by norm_num) (by norm_num)
      (mul_ne_zero (by norm_num) hmu) V A M N D hM hN hD hMN
      hVpresentation hApresentation hcurve
  have hr5formula := S.mixedTerminalFormula hrho4
  dsimp only at hr5formula
  change GCD369CubeFaberR5
      S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
    A ^ 2 * V / 1024 - 256 * (6 * S.rho4) ^ 2 / (27 * A ^ 3)
      at hr5formula
  let r50 : k := a0 ^ 2 * v0 / 1024 - 256 * nu ^ 2 / (27 * a0 ^ 3)
  have hr5C :
      GCD369CubeFaberR5
          S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
        algebraMap k (RatFunc k) r50 := by
    rw [hr5formula, hAC, hVC, hrho4const]
    dsimp only [r50]
    simp only [map_sub, map_mul, map_pow, map_div₀, map_ofNat]
  rw [hr5C, GCD369CubeRatFuncDerivative_C, mul_zero] at hterminal
  exact hjmap hterminal.symm

set_option maxHeartbeats 4000000 in
/-- The smooth mixed source fibre is terminally empty over `k(x)`, with its
weighted reduced presentation constructed internally from the actual source
coordinates. -/
theorem mixedEllipticRatFuncTerminalExclusion
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeLaterInvariantSource (RatFunc k))
    (mu nu j : k) (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hj : j ≠ 0)
    (s : k[X])
    (hrho3const : 6 * S.rho3 = algebraMap k (RatFunc k) mu)
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
  have hjmap : algebraMap k (RatFunc k) j ≠ 0 := by
    rw [RatFunc.algebraMap_eq_C]
    simpa using RatFunc.C_injective.ne hj
  have hrho4 : S.rho4 ≠ 0 := by
    intro hz
    apply hnumap
    rw [← hrho4const, hz]
    ring
  let A : RatFunc k := 4 * S.a2 - S.a4 ^ 2
  let B : RatFunc k := 2 * S.a1 - S.a3 * S.a4
  let w : RatFunc k := 4 * S.a0 - S.a3 ^ 2
  let V : RatFunc k := w + 8 * B ^ 2 / A
  have hmixed := S.mixedCoordinates hrho4
  dsimp only at hmixed
  change A ≠ 0 ∧
    S.rho4 = -3 * A ^ 2 * B / 512 ∧
    S.rho3 = (24 * V ^ 2 - A ^ 3) / 1024 ∧
    GCD369CubeFaberR5 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
      A * (A * V - 12 * B ^ 2) / 1024 at hmixed
  rcases hmixed with ⟨hA, _hrho4formula, hrho3formula, _hr5formula⟩
  have hrho3clear : 1024 * S.rho3 = 24 * V ^ 2 - A ^ 3 := by
    rw [hrho3formula]
    ring
  have hcurveRaw :
      72 * V ^ 2 - 3 * A ^ 3 - 512 * (6 * S.rho3) = 0 := by
    linear_combination
      (norm := ring_nf (config := { zetaDelta := false })) -3 * hrho3clear
  have hcurve :
      algebraMap k (RatFunc k) (72 : k) * V ^ 2 +
          algebraMap k (RatFunc k) (-3 : k) * A ^ 3 +
          algebraMap k (RatFunc k) (-512 * mu) = 0 := by
    simp only [map_mul, map_neg, map_ofNat]
    rw [← hrho3const]
    simpa only [sub_eq_add_neg, neg_mul] using hcurveRaw
  have hr5formula := S.mixedTerminalFormula hrho4
  dsimp only at hr5formula
  change GCD369CubeFaberR5
      S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
    A ^ 2 * V / 1024 - 256 * (6 * S.rho4) ^ 2 / (27 * A ^ 3)
      at hr5formula
  rcases eq_or_ne V 0 with hV | hV
  · let a3 : k := -(512 / 3) * mu
    have hA3raw : A ^ 3 = -(512 / 3) * (6 * S.rho3) := by
      rw [hV] at hrho3clear
      linear_combination
        (norm := ring_nf (config := { zetaDelta := false })) hrho3clear
    have hA3 : A ^ 3 = algebraMap k (RatFunc k) a3 := by
      rw [hA3raw, hrho3const]
      dsimp only [a3]
      simp only [map_neg, map_mul, map_div₀, map_ofNat]
    let r50 : k := -256 * nu ^ 2 / (27 * a3)
    have hr5C :
        GCD369CubeFaberR5
            S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
          algebraMap k (RatFunc k) r50 := by
      rw [hr5formula, hV, hA3, hrho4const]
      dsimp only [r50]
      simp only [mul_zero, zero_div, zero_sub, map_neg, map_mul, map_pow,
        map_div₀, map_ofNat]
      ring
    rw [hr5C, GCD369CubeRatFuncDerivative_C, mul_zero] at hterminal
    exact hjmap hterminal.symm
  · obtain ⟨v0, a0, hVC, hAC⟩ :=
      GCD369CubeRatFuncEllipticConstancyOfNonzero
        (72 : k) (-3 : k) (-512 * mu) (by norm_num) (by norm_num)
          (mul_ne_zero (by norm_num) hmu) V A hV hA hcurve
    let r50 : k := a0 ^ 2 * v0 / 1024 - 256 * nu ^ 2 / (27 * a0 ^ 3)
    have hr5C :
        GCD369CubeFaberR5
            S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
          algebraMap k (RatFunc k) r50 := by
      rw [hr5formula, hAC, hVC, hrho4const]
      dsimp only [r50]
      simp only [map_sub, map_mul, map_pow, map_div₀, map_ofNat]
    rw [hr5C, GCD369CubeRatFuncDerivative_C, mul_zero] at hterminal
    exact hjmap hterminal.symm

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

/-- Source-facing coordinate form of the surviving unmixed elliptic fibre. -/
theorem unmixedEllipticCurveOfTerminal
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
    let Xc := 8 * S.a2 - 2 * S.a4 ^ 2
    let Yc := 3 * S.a4 * Xc
    S.a3 = 0 ∧ S.a1 = 0 ∧
      (48 * S.a0 - 12 * S.a2 * S.a4 + 3 * S.a4 ^ 3 = 0) ∧
      Yc ^ 2 = 3 * Xc ^ 3 + 4096 * (6 * S.rho3) := by
  dsimp only
  obtain ⟨ha3, ha1, hsheet, hlinear⟩ :=
    S.unmixedEllipticCoordinatesOfTerminal j hj s hrho4 hterminal
  exact ⟨ha3, ha1, hlinear, S.unmixedEllipticCurve hsheet⟩

set_option maxHeartbeats 4000000 in
/-- The surviving unmixed elliptic source sheet is terminally empty over
`k(x)`.  Its weighted presentation and constancy are derived internally; a
zero `Y` coordinate collapses directly to zero terminal value. -/
theorem unmixedEllipticRatFuncTerminalExclusion
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeLaterInvariantSource (RatFunc k))
    (mu j : k) (hmu : mu ≠ 0) (hj : j ≠ 0) (s : k[X])
    (hrho3const : 6 * S.rho3 = algebraMap k (RatFunc k) mu)
    (hrho4 : S.rho4 = 0)
    (hterminal :
      algebraMap k[X] (RatFunc k) s *
          GCD369CubeRatFuncDerivative
            (GCD369CubeFaberR5
              S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0) =
        algebraMap k (RatFunc k) j) : False := by
  have hmumap : algebraMap k (RatFunc k) mu ≠ 0 := by
    rw [RatFunc.algebraMap_eq_C]
    simpa using RatFunc.C_injective.ne hmu
  have hjmap : algebraMap k (RatFunc k) j ≠ 0 := by
    rw [RatFunc.algebraMap_eq_C]
    simpa using RatFunc.C_injective.ne hj
  let Xc : RatFunc k := 8 * S.a2 - 2 * S.a4 ^ 2
  let Yc : RatFunc k := 3 * S.a4 * Xc
  have helliptic :=
    S.unmixedEllipticCurveOfTerminal j hj s hrho4 hterminal
  dsimp only at helliptic
  change S.a3 = 0 ∧ S.a1 = 0 ∧
      (48 * S.a0 - 12 * S.a2 * S.a4 + 3 * S.a4 ^ 3 = 0) ∧
      Yc ^ 2 = 3 * Xc ^ 3 + 4096 * (6 * S.rho3) at helliptic
  rcases helliptic with ⟨ha3, ha1, hlinear, hcurveSource⟩
  have hXc : Xc ≠ 0 := by
    intro hX
    have hY : Yc = 0 := by
      dsimp only [Yc]
      rw [hX]
      ring
    have hbad :
        (4096 : RatFunc k) * algebraMap k (RatFunc k) mu = 0 := by
      rw [hX, hY, hrho3const] at hcurveSource
      simpa using hcurveSource.symm
    exact (mul_ne_zero (by norm_num) hmumap) hbad
  have hcurve :
      algebraMap k (RatFunc k) (1 : k) * Yc ^ 2 +
          algebraMap k (RatFunc k) (-3 : k) * Xc ^ 3 +
          algebraMap k (RatFunc k) (-4096 * mu) = 0 := by
    simp only [map_one, one_mul, map_neg, map_ofNat, map_mul]
    rw [← hrho3const]
    linear_combination hcurveSource
  rcases eq_or_ne Yc 0 with hYc | hYc
  · have ha4prod : S.a4 * Xc = 0 := by
      dsimp only [Yc] at hYc
      linear_combination (1 / 3 : RatFunc k) * hYc
    have ha4 : S.a4 = 0 := (mul_eq_zero.mp ha4prod).resolve_right hXc
    have ha0 : S.a0 = 0 := by
      rw [ha4] at hlinear
      linear_combination (1 / 48 : RatFunc k) * hlinear
    have hr5zero :
        GCD369CubeFaberR5
            S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 = 0 := by
      rw [ha0, ha1, ha3, ha4]
      simp [GCD369CubeFaberR5]
    rw [hr5zero, GCD369CubeRatFuncDerivative_zero, mul_zero] at hterminal
    exact hjmap hterminal.symm
  · obtain ⟨y0, x0, hYC, hXC⟩ :=
      GCD369CubeRatFuncEllipticConstancyOfNonzero
        (1 : k) (-3 : k) (-4096 * mu) one_ne_zero (by norm_num)
          (mul_ne_zero (by norm_num) hmu) Yc Xc hYc hXc hcurve
    have hx0 : x0 ≠ 0 := by
      intro hx0
      apply hXc
      rw [hXC, hx0, map_zero]
    have hx0map : algebraMap k (RatFunc k) x0 ≠ 0 := by
      rw [RatFunc.algebraMap_eq_C]
      simpa using RatFunc.C_injective.ne hx0
    let a4b : k := y0 / (3 * x0)
    have hYrel :
        algebraMap k (RatFunc k) y0 =
          3 * S.a4 * algebraMap k (RatFunc k) x0 := by
      calc
        algebraMap k (RatFunc k) y0 = Yc := hYC.symm
        _ = 3 * S.a4 * Xc := rfl
        _ = 3 * S.a4 * algebraMap k (RatFunc k) x0 := by rw [hXC]
    have ha4C : S.a4 = algebraMap k (RatFunc k) a4b := by
      dsimp only [a4b]
      rw [map_div₀, map_mul, map_ofNat]
      apply (eq_div_iff (mul_ne_zero (by norm_num) hx0map)).2
      rw [hYrel]
      ring
    let a2b : k := (x0 + 2 * a4b ^ 2) / 8
    have hXrel :
        algebraMap k (RatFunc k) x0 =
          8 * S.a2 - 2 * (algebraMap k (RatFunc k) a4b) ^ 2 := by
      calc
        algebraMap k (RatFunc k) x0 = Xc := hXC.symm
        _ = 8 * S.a2 - 2 * S.a4 ^ 2 := rfl
        _ = 8 * S.a2 - 2 * (algebraMap k (RatFunc k) a4b) ^ 2 := by
          rw [ha4C]
    have ha2base : 8 * a2b = x0 + 2 * a4b ^ 2 := by
      dsimp only [a2b]
      ring
    have ha2map := congrArg (algebraMap k (RatFunc k)) ha2base
    simp only [map_mul, map_add, map_pow, map_ofNat] at ha2map
    have ha2C : S.a2 = algebraMap k (RatFunc k) a2b := by
      linear_combination (-1 / 8 : RatFunc k) * hXrel +
        (-1 / 8 : RatFunc k) * ha2map
    let a0b : k := (12 * a2b * a4b - 3 * a4b ^ 3) / 48
    have ha0base : 48 * a0b = 12 * a2b * a4b - 3 * a4b ^ 3 := by
      dsimp only [a0b]
      ring
    have ha0map := congrArg (algebraMap k (RatFunc k)) ha0base
    simp only [map_sub, map_mul, map_pow, map_ofNat] at ha0map
    have ha0C : S.a0 = algebraMap k (RatFunc k) a0b := by
      rw [ha2C, ha4C] at hlinear
      linear_combination (1 / 48 : RatFunc k) * hlinear +
        (-1 / 48 : RatFunc k) * ha0map
    let r50 : k := GCD369CubeFaberR5
      a0b 0 a2b 0 a4b 0 0 0 0 0 0 0
    have hr5C :
        GCD369CubeFaberR5
            S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
          algebraMap k (RatFunc k) r50 := by
      rw [ha0C, ha1, ha2C, ha3, ha4C]
      dsimp only [r50]
      simpa only [map_zero] using
        (GCD369CubeFaberR5_C a0b 0 a2b 0 a4b 0 0 0 0 0 0 0)
    rw [hr5C, GCD369CubeRatFuncDerivative_C, mul_zero] at hterminal
    exact hjmap hterminal.symm

end GCD369CubeLaterInvariantSource

#print axioms GCD369CubeRatFuncReducedPresentation
#print axioms GCD369CubeRatFuncDerivative_div
#print axioms GCD369CubeRatFuncDerivative_zero
#print axioms GCD369CubeRatFuncDerivative_C
#print axioms GCD369CubeFaberR5_C
#print axioms GCD369CubeRatFuncWeightedPresentation
#print axioms GCD369CubeRatFuncEllipticConstancy
#print axioms GCD369CubeRatFuncEllipticConstancyOfNonzero
#print axioms GCD369CubeMixedCuspRatFuncFormula
#print axioms GCD369CubeDSRatFuncFormula
#print axioms
  GCD369CubeLaterInvariantSource.mixedCuspRatFuncTerminalExclusion
#print axioms
  GCD369CubeLaterInvariantSource.mixedEllipticRatFuncTerminalExclusionOfPresentation
#print axioms
  GCD369CubeLaterInvariantSource.mixedEllipticRatFuncTerminalExclusion
#print axioms
  GCD369CubeLaterInvariantSource.zeroInvariantRatFuncTerminalExclusion
#print axioms
  GCD369CubeLaterInvariantSource.unmixedEllipticCoordinatesOfTerminal
#print axioms
  GCD369CubeLaterInvariantSource.unmixedEllipticCurveOfTerminal
#print axioms
  GCD369CubeLaterInvariantSource.unmixedEllipticRatFuncTerminalExclusion
