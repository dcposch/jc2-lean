import Grok810PiOrders110to112CeilingScratch

/-! # Cancel-and-expose of the `(8,10)` degree-one `π` linear-root chambers

`Grok810PiOrders110to112CeilingScratch` exhausted the unsolved `π`
numerator through the last frozen head (order `112`) and recorded the
holomorphic ceiling interface
`localClearedSixteenthDefect810_pow_112_dvd_contradicts_simplePole`.
The three live chambers of
`piFace810_linearRoot_order112Chambers` are unchanged:

* LEFT: `F1 ∨ F2` with unsolved witnesses `m1, τ1, g1, k1`;
* RIGHT/`u1 = 0`: extra `16 b62 v1 = 5 v1³`;
* RIGHT complement: extra `2 u1² + v1³ = 0` on `5 v1² = 8 b62`.

This file is the `(8,10)` analog of
`Grok610DegreeZeroMixedArmClosureScratch`.  The weight-`112` source
power relation already supplies `h0^112 ∣ A₀`, independently of those
chamber extras: the LEFT witnesses and the RIGHT fifteenth-face
relations do not appear in `localClearedSixteenthDefect810`.  The
source coordinates are polynomials in `X`, so each has a finite Taylor
expansion at the simple root of `h0`; the late mixins (orders `110`–
`112`) involve only `t0, a0, a1, b1, b2, λ`, and one Taylor step of
those polynomials is recorded below.  Cancelling the clearing powers
exposes the remaining factor as `2⁴⁴ π`, a polynomial (in fact a
ground-field constant).

The 610 mixed-arm cancel identifies that remaining factor with a
primitive whose source derivative is the simple pole `C(j)/h0`.  Here
the exposed remaining factor is the depressed `π` residual.  On a
literal source that residual is a constant (`sourcePiResidual810_eq_C_of_source`),
so its ordinary derivative is `0`, not `C(j)/h0`.  The ceiling lemma
therefore applies only *conditionally* on a simple-pole derivative of
the remaining factor, which the `π` source wrapper does not supply.

**NOT A CLOSURE of `piFace810_linearRoot`.**  The `h^112` divisibility,
the Taylor step of the late-mixin coordinates, and the cancel identity
are complete on every chamber.  The simple-pole hypothesis of
`localClearedSixteenthDefect810_pow_112_dvd_contradicts_simplePole` is
the exact remaining gap: remaining `= C(2⁴⁴ η)` has derivative `0`.
There is no unused compact-numerator order after `112`.  The next
residual with a genuine simple pole is the degree-zero `ρ` jet (base
order `102`, remaining pole `17`).

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut, no closure overclaim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section PiChamberTaylor810

variable {k : Type*} [Field k] [CharZero k]

/-- Next Taylor of a polynomial at a simple root of `h0`. -/
theorem linearPolynomial_nextTaylor810
    (h0 f : k[X]) (a : k) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) :
    ∃ fn : k[X], f = C (f.eval a) + h0 * fn := by
  have hα : (f - C (f.eval a)).eval a = 0 := by
    simp [Polynomial.eval_sub, Polynomial.eval_C]
  obtain ⟨fn, hT⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0
    (f - C (f.eval a)) a hdegree hroot hα
  exact ⟨fn, (sub_eq_iff_eq_add.mp hT).trans
    (add_comm (h0 * fn) (C (f.eval a)))⟩

/-- One Taylor step of the late-mixin coordinates
`t0, a0, a1, b1, b2` (orders `110`–`112`).  These are polynomials in
`X`, so the expansion at a simple root of `h0` is finite; further
iterates exist and terminate after `natDegree + 1` steps.  The
unsolved LEFT witnesses `m1, τ1, g1, k1` do not appear. -/
theorem piFace810_linearRoot_lateMixin_nextTaylor
    (h0 t0 a1 a0 b2 b1 : k[X]) (a : k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0) :
    ∃ t0n a1n a0n b2n b1n : k[X],
      t0 = C (t0.eval a) + h0 * t0n ∧
        a1 = C (a1.eval a) + h0 * a1n ∧
        a0 = C (a0.eval a) + h0 * a0n ∧
        b2 = C (b2.eval a) + h0 * b2n ∧
        b1 = C (b1.eval a) + h0 * b1n := by
  obtain ⟨t0n, ht0⟩ := linearPolynomial_nextTaylor810 h0 t0 a hdegree hroot
  obtain ⟨a1n, ha1⟩ := linearPolynomial_nextTaylor810 h0 a1 a hdegree hroot
  obtain ⟨a0n, ha0⟩ := linearPolynomial_nextTaylor810 h0 a0 a hdegree hroot
  obtain ⟨b2n, hb2⟩ := linearPolynomial_nextTaylor810 h0 b2 a hdegree hroot
  obtain ⟨b1n, hb1⟩ := linearPolynomial_nextTaylor810 h0 b1 a hdegree hroot
  exact ⟨t0n, a1n, a0n, b2n, b1n, ht0, ha1, ha0, hb2, hb1⟩

end PiChamberTaylor810

section PiChamberClearing810

variable {k : Type*} [Field k] [CharZero k]

/-- Algebraic clearing, independent of the source Jacobian: the image of
the weight-`112` numerator is `h^{112}` times the scaled depressed `π`
residual.  This is the `(8,10)` analog of
`degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive`. -/
theorem localClearedSixteenthDefect810_algebraMap_eq_pow_scaledPi
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (lambda : k) (hh : h ≠ 0)
    (hN :
      5 * a7 * h ^ 2 - 4 * b9 = Polynomial.C lambda * h ^ 9) :
    algebraMap k[X] (RatFunc k)
        (localClearedSixteenthDefect810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
      (algebraMap k[X] (RatFunc k) h) ^ 112 *
        ((17592186044416 : RatFunc k) *
          sourcePiResidual810
            (algebraMap k[X] (RatFunc k) h)
            (algebraMap k[X] (RatFunc k) a7)
            (algebraMap k[X] (RatFunc k) a6)
            (algebraMap k[X] (RatFunc k) a5)
            (algebraMap k[X] (RatFunc k) a4)
            (algebraMap k[X] (RatFunc k) a3)
            (algebraMap k[X] (RatFunc k) a2)
            (algebraMap k[X] (RatFunc k) a1)
            (algebraMap k[X] (RatFunc k) a0)
            (algebraMap k[X] (RatFunc k) b9)
            (algebraMap k[X] (RatFunc k) b8)
            (algebraMap k[X] (RatFunc k) b7)
            (algebraMap k[X] (RatFunc k) b6)
            (algebraMap k[X] (RatFunc k) b5)
            (algebraMap k[X] (RatFunc k) b4)
            (algebraMap k[X] (RatFunc k) b3)
            (algebraMap k[X] (RatFunc k) b2)
            (algebraMap k[X] (RatFunc k) b1)
            (RatFunc.C lambda)) := by
  let phi : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  have hhRat : phi h ≠ 0 := RatFunc.algebraMap_ne_zero hh
  have hNrat :
      5 * phi a7 * (phi h) ^ 2 - 4 * phi b9 =
        RatFunc.C lambda * (phi h) ^ 9 := by
    have hmapped := congrArg phi hN
    simpa [phi, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hclear :=
    piSourceClearingBridge810 (F := RatFunc k)
      (phi h) (phi a7) (phi a6) (phi a5) (phi a4) (phi a3) (phi a2)
      (phi a1) (phi a0) (phi b9) (phi b8) (phi b7) (phi b6) (phi b5)
      (phi b4) (phi b3) (phi b2) (phi b1) (RatFunc.C lambda) hhRat hNrat
  rw [map_localClearedSixteenthDefect810]
  rw [show phi (Polynomial.C lambda) = RatFunc.C lambda from
    RatFunc.algebraMap_C lambda]
  rw [← hclear]
  simp only [sourcePiResidual810, phi]
  ring

/-- Source power relation: `A₀ = C(2⁴⁴ η) · h0^{112}`.  The LEFT
witnesses `m1, τ1, g1, k1` and the RIGHT extras are not arguments of
the numerator, so they are irrelevant to this identity. -/
theorem localClearedSixteenthDefect810_eq_C_pow_112_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eta : k,
      localClearedSixteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C (17592186044416 * eta) * h0 ^ 112 := by
  obtain ⟨eta, heta⟩ :=
    sourcePiResidual810_eq_C_of_source p q H h0 j lambda hp hq hh0 hH
      hp8 hq10 hN hD
  have hNsrc :
      5 * (p.coeff 7) * h0 ^ 2 - 4 * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    simpa only [hH] using hN
  refine ⟨eta, ?_⟩
  exact piSourcePowerRelation810_of_residual_eq_C h0 (p.coeff 7)
    (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
    (p.coeff 1) (p.coeff 0) (q.coeff 9) (q.coeff 8) (q.coeff 7)
    (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
    (q.coeff 1) lambda eta hh0 hNsrc heta

/-- Same power relation after the six unsolved valuations used by the
`π` tower. -/
theorem localClearedSixteenthDefect810_eq_C_pow_112_of_source_valuated
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t0 v1 u1 s1 w1 b62 : k[X])
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht0 : p.coeff 7 = h0 ^ 6 * t0)
    (hv1 : p.coeff 6 = h0 ^ 4 * v1)
    (hu1 : p.coeff 5 = h0 ^ 2 * u1)
    (hs1 : q.coeff 8 = h0 ^ 6 * s1)
    (hw1 : q.coeff 7 = h0 ^ 4 * w1)
    (hb62 : q.coeff 6 = h0 ^ 2 * b62) :
    ∃ eta : k,
      localClearedSixteenthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 4 * v1)
          (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (h0 ^ 6 * s1) (h0 ^ 4 * w1)
          (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C (17592186044416 * eta) * h0 ^ 112 := by
  obtain ⟨eta, heta⟩ :=
    localClearedSixteenthDefect810_eq_C_pow_112_of_source p q H h0 j
      lambda hp hq hh0 hH hp8 hq10 hN hD
  refine ⟨eta, ?_⟩
  simpa only [ht0, hv1, hu1, hs1, hw1, hb62] using heta

/-- Ordinary derivative of the depressed `π` residual, on a literal
source, is `0`.  This is the exact obstruction to discharging the
simple-pole hypothesis of the weight-`112` ceiling lemma. -/
theorem sourcePiResidual810_deriv_eq_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    Differential.deriv
        (sourcePiResidual810
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (p.coeff 7))
          (algebraMap k[X] (RatFunc k) (p.coeff 6))
          (algebraMap k[X] (RatFunc k) (p.coeff 5))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 9))
          (algebraMap k[X] (RatFunc k) (q.coeff 8))
          (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))
          (RatFunc.C lambda)) = 0 := by
  obtain ⟨eta, heta⟩ :=
    sourcePiResidual810_eq_C_of_source p q H h0 j lambda hp hq hh0 hH
      hp8 hq10 hN hD
  have hx := GCD369RatFuncDerivative (Polynomial.C eta)
  rw [heta]
  simpa [Polynomial.derivative_C, RatFunc.algebraMap_C] using hx

/-- Scaled remaining factor after cancel also has derivative `0`. -/
theorem scaledSourcePiResidual810_deriv_eq_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    Differential.deriv
        ((17592186044416 : RatFunc k) *
          sourcePiResidual810
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) (p.coeff 7))
            (algebraMap k[X] (RatFunc k) (p.coeff 6))
            (algebraMap k[X] (RatFunc k) (p.coeff 5))
            (algebraMap k[X] (RatFunc k) (p.coeff 4))
            (algebraMap k[X] (RatFunc k) (p.coeff 3))
            (algebraMap k[X] (RatFunc k) (p.coeff 2))
            (algebraMap k[X] (RatFunc k) (p.coeff 1))
            (algebraMap k[X] (RatFunc k) (p.coeff 0))
            (algebraMap k[X] (RatFunc k) (q.coeff 9))
            (algebraMap k[X] (RatFunc k) (q.coeff 8))
            (algebraMap k[X] (RatFunc k) (q.coeff 7))
            (algebraMap k[X] (RatFunc k) (q.coeff 6))
            (algebraMap k[X] (RatFunc k) (q.coeff 5))
            (algebraMap k[X] (RatFunc k) (q.coeff 4))
            (algebraMap k[X] (RatFunc k) (q.coeff 3))
            (algebraMap k[X] (RatFunc k) (q.coeff 2))
            (algebraMap k[X] (RatFunc k) (q.coeff 1))
            (RatFunc.C lambda)) = 0 := by
  obtain ⟨eta, heta⟩ :=
    sourcePiResidual810_eq_C_of_source p q H h0 j lambda hp hq hh0 hH
      hp8 hq10 hN hD
  have hx :=
    GCD369RatFuncDerivative (Polynomial.C (17592186044416 * eta))
  rw [heta]
  simpa [Polynomial.derivative_C, RatFunc.algebraMap_C, map_mul,
    map_ofNat] using hx

end PiChamberClearing810

section PiChamberCancel810

variable {k : Type*} [Field k] [CharZero k]

/-- Cancel-and-expose on a literal source: `h0^{112}` divides the
cleared numerator, and the remaining factor *is* the scaled depressed
`π` residual.  Chamber extras are not used. -/
theorem piFace810_linearRoot_cancelExpose_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ eta : k,
      localClearedSixteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C (17592186044416 * eta) * h0 ^ 112 ∧
        algebraMap k[X] (RatFunc k)
            (localClearedSixteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
              (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
              (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
              (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
              (q.coeff 2) (q.coeff 1) (Polynomial.C lambda)) =
          (algebraMap k[X] (RatFunc k) h0) ^ 112 *
            ((17592186044416 : RatFunc k) *
              sourcePiResidual810
                (algebraMap k[X] (RatFunc k) h0)
                (algebraMap k[X] (RatFunc k) (p.coeff 7))
                (algebraMap k[X] (RatFunc k) (p.coeff 6))
                (algebraMap k[X] (RatFunc k) (p.coeff 5))
                (algebraMap k[X] (RatFunc k) (p.coeff 4))
                (algebraMap k[X] (RatFunc k) (p.coeff 3))
                (algebraMap k[X] (RatFunc k) (p.coeff 2))
                (algebraMap k[X] (RatFunc k) (p.coeff 1))
                (algebraMap k[X] (RatFunc k) (p.coeff 0))
                (algebraMap k[X] (RatFunc k) (q.coeff 9))
                (algebraMap k[X] (RatFunc k) (q.coeff 8))
                (algebraMap k[X] (RatFunc k) (q.coeff 7))
                (algebraMap k[X] (RatFunc k) (q.coeff 6))
                (algebraMap k[X] (RatFunc k) (q.coeff 5))
                (algebraMap k[X] (RatFunc k) (q.coeff 4))
                (algebraMap k[X] (RatFunc k) (q.coeff 3))
                (algebraMap k[X] (RatFunc k) (q.coeff 2))
                (algebraMap k[X] (RatFunc k) (q.coeff 1))
                (RatFunc.C lambda)) := by
  obtain ⟨eta, hA⟩ :=
    localClearedSixteenthDefect810_eq_C_pow_112_of_source p q H h0 j
      lambda hp hq hh0 hH hp8 hq10 hN hD
  have hNsrc :
      5 * (p.coeff 7) * h0 ^ 2 - 4 * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    simpa only [hH] using hN
  have hclear :=
    localClearedSixteenthDefect810_algebraMap_eq_pow_scaledPi h0
      (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 9) (q.coeff 8)
      (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
      (q.coeff 2) (q.coeff 1) lambda hh0 hNsrc
  exact ⟨eta, hA, hclear⟩

/-- Conditional cancel-and-expose contradiction: if the remaining
scaled `π` factor *had* derivative `C j / h0` with `j ≠ 0`, this would
be False.  The `π` source wrapper supplies derivative `0` instead
(`scaledSourcePiResidual810_deriv_eq_zero_of_source`), so this
hypothesis is the exact gap. -/
theorem piFace810_linearRoot_false_of_scaledPi_simplePole
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hj : j ≠ 0)
    (hderiv :
      Differential.deriv
          ((17592186044416 : RatFunc k) *
            sourcePiResidual810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) (p.coeff 7))
              (algebraMap k[X] (RatFunc k) (p.coeff 6))
              (algebraMap k[X] (RatFunc k) (p.coeff 5))
              (algebraMap k[X] (RatFunc k) (p.coeff 4))
              (algebraMap k[X] (RatFunc k) (p.coeff 3))
              (algebraMap k[X] (RatFunc k) (p.coeff 2))
              (algebraMap k[X] (RatFunc k) (p.coeff 1))
              (algebraMap k[X] (RatFunc k) (p.coeff 0))
              (algebraMap k[X] (RatFunc k) (q.coeff 9))
              (algebraMap k[X] (RatFunc k) (q.coeff 8))
              (algebraMap k[X] (RatFunc k) (q.coeff 7))
              (algebraMap k[X] (RatFunc k) (q.coeff 6))
              (algebraMap k[X] (RatFunc k) (q.coeff 5))
              (algebraMap k[X] (RatFunc k) (q.coeff 4))
              (algebraMap k[X] (RatFunc k) (q.coeff 3))
              (algebraMap k[X] (RatFunc k) (q.coeff 2))
              (algebraMap k[X] (RatFunc k) (q.coeff 1))
              (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) : False := by
  obtain ⟨eta, hA, hclear⟩ :=
    piFace810_linearRoot_cancelExpose_of_source p q H h0 j lambda a hp
      hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  exact localClearedSixteenthDefect810_pow_112_dvd_contradicts_simplePole
    h0 (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
    (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
    (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
    (q.coeff 1) lambda eta j a
    ((17592186044416 : RatFunc k) *
      sourcePiResidual810
        (algebraMap k[X] (RatFunc k) h0)
        (algebraMap k[X] (RatFunc k) (p.coeff 7))
        (algebraMap k[X] (RatFunc k) (p.coeff 6))
        (algebraMap k[X] (RatFunc k) (p.coeff 5))
        (algebraMap k[X] (RatFunc k) (p.coeff 4))
        (algebraMap k[X] (RatFunc k) (p.coeff 3))
        (algebraMap k[X] (RatFunc k) (p.coeff 2))
        (algebraMap k[X] (RatFunc k) (p.coeff 1))
        (algebraMap k[X] (RatFunc k) (p.coeff 0))
        (algebraMap k[X] (RatFunc k) (q.coeff 9))
        (algebraMap k[X] (RatFunc k) (q.coeff 8))
        (algebraMap k[X] (RatFunc k) (q.coeff 7))
        (algebraMap k[X] (RatFunc k) (q.coeff 6))
        (algebraMap k[X] (RatFunc k) (q.coeff 5))
        (algebraMap k[X] (RatFunc k) (q.coeff 4))
        (algebraMap k[X] (RatFunc k) (q.coeff 3))
        (algebraMap k[X] (RatFunc k) (q.coeff 2))
        (algebraMap k[X] (RatFunc k) (q.coeff 1))
        (RatFunc.C lambda))
    hh0 hroot hA hclear hderiv hj

end PiChamberCancel810

section PiChamberPacket810

variable {k : Type*} [Field k] [CharZero k]

/-- Source-facing joint packet: order-`112` chambers, one Taylor step of
the late-mixin coordinates, and `h0^{112} ∣ A₀` from the source power
relation.  The LEFT witnesses and RIGHT extras are carried from the
parent and are not used by the divisibility.  This is not a closure. -/
theorem piFace810_linearRoot_cancelExposePacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 t0n a1n a0n b2n b1n : k[X])
      (eta : k),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        t0 = C (t0.eval a) + h0 * t0n ∧
        (p.coeff 1) = C ((p.coeff 1).eval a) + h0 * a1n ∧
        (p.coeff 0) = C ((p.coeff 0).eval a) + h0 * a0n ∧
        (q.coeff 2) = C ((q.coeff 2).eval a) + h0 * b2n ∧
        (q.coeff 1) = C ((q.coeff 1).eval a) + h0 * b1n ∧
        localClearedSixteenthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 4 * v1)
            (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (h0 ^ 6 * s1) (h0 ^ 4 * w1)
            (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C (17592186044416 * eta) * h0 ^ 112 := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, _o96n, _o97n, _o98n,
      _o99n, _o100n, _o101n, _o102n, _o103n, _o104n, _o105n, _o106n,
      _o107n, _o108n, _o109n, _o110n, _o111n, _eta, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, _ho96, _ho97, _ho98, _ho99, _ho100,
      _ho101, _ho102, _ho103, _ho104, _ho105, _ho106, _ho107, _ho108,
      _ho109, _ho110, _ho111, _hhol, _hsplit⟩ :=
    piFace810_linearRoot_order112Chambers p q H h0 j lambda a hp hq
      hh0 hh0degree hH hp8 hq10 hN hD hroot
  obtain ⟨t0n, a1n, a0n, b2n, b1n, ht0T, ha1T, ha0T, hb2T, hb1T⟩ :=
    piFace810_linearRoot_lateMixin_nextTaylor h0 t0 (p.coeff 1)
      (p.coeff 0) (q.coeff 2) (q.coeff 1) a hh0degree hroot
  have ha6 : p.coeff 6 = h0 ^ 4 * v1 := by
    rw [hv0, hv1]
    ring
  have ha5 : p.coeff 5 = h0 ^ 2 * u1 := by
    rw [hu0, hu1]
    ring
  have hb8 : q.coeff 8 = h0 ^ 6 * s1 := by
    rw [hs0, hs1]
    ring
  have hb7 : q.coeff 7 = h0 ^ 4 * w1 := by
    rw [hw0, hw1]
    ring
  obtain ⟨eta, hA⟩ :=
    localClearedSixteenthDefect810_eq_C_pow_112_of_source_valuated p q
      H h0 j lambda t0 v1 u1 s1 w1 b62 hp hq hh0 hH hp8 hq10 hN hD ht0
      ha6 ha5 hb8 hb7 hb62
  exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, t0n, a1n, a0n, b2n,
    b1n, eta, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ht0T,
    ha1T, ha0T, hb2T, hb1T, hA⟩

/-- LEFT chamber: `F1 ∨ F2` with unsolved `m1, τ1, g1, k1`.  The
witnesses are not arguments of `A₀`, so `h0^{112} ∣ A₀` holds on this
chamber by the source power relation.  Not a closure. -/
theorem piFace810_linearRoot_left_pow112_dvd
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ (t0 v1 u1 s1 w1 b62 : k[X]) (eta : k),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 4 * v1 ∧
        p.coeff 5 = h0 ^ 2 * u1 ∧ q.coeff 8 = h0 ^ 6 * s1 ∧
        q.coeff 7 = h0 ^ 4 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        localClearedSixteenthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 4 * v1)
            (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (h0 ^ 6 * s1) (h0 ^ 4 * w1)
            (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C (17592186044416 * eta) * h0 ^ 112 := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, _o96n, _o97n, _o98n,
      _o99n, _o100n, _o101n, _o102n, _o103n, _o104n, _o105n, _o106n,
      _o107n, _o108n, _o109n, _o110n, _o111n, _eta, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, _ho96, _ho97, _ho98, _ho99, _ho100,
      _ho101, _ho102, _ho103, _ho104, _ho105, _ho106, _ho107, _ho108,
      _ho109, _ho110, _ho111, _hhol, hsplit⟩ :=
    piFace810_linearRoot_order112Chambers p q H h0 j lambda a hp hq
      hh0 hh0degree hH hp8 hq10 hN hD hroot
  have ha6 : p.coeff 6 = h0 ^ 4 * v1 := by
    rw [hv0, hv1]
    ring
  have ha5 : p.coeff 5 = h0 ^ 2 * u1 := by
    rw [hu0, hu1]
    ring
  have hb8 : q.coeff 8 = h0 ^ 6 * s1 := by
    rw [hs0, hs1]
    ring
  have hb7 : q.coeff 7 = h0 ^ 4 * w1 := by
    rw [hw0, hw1]
    ring
  obtain ⟨eta, hA⟩ :=
    localClearedSixteenthDefect810_eq_C_pow_112_of_source_valuated p q
      H h0 j lambda t0 v1 u1 s1 w1 b62 hp hq hh0 hH hp8 hq10 hN hD ht0
      ha6 ha5 hb8 hb7 hb62
  exact ⟨t0, v1, u1, s1, w1, b62, eta, ht0, ha6, ha5, hb8, hb7, hb62, hA⟩

/-- RIGHT/`u1 = 0` chamber.  The fifteenth-face extra is not used by
the `h^{112}` identity.  Not a closure. -/
theorem piFace810_linearRoot_rightU1Zero_pow112_dvd
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ (t0 v1 u1 s1 w1 b62 : k[X]) (eta : k),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 4 * v1 ∧
        p.coeff 5 = h0 ^ 2 * u1 ∧ q.coeff 8 = h0 ^ 6 * s1 ∧
        q.coeff 7 = h0 ^ 4 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        localClearedSixteenthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 4 * v1)
            (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (h0 ^ 6 * s1) (h0 ^ 4 * w1)
            (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C (17592186044416 * eta) * h0 ^ 112 :=
  piFace810_linearRoot_left_pow112_dvd p q H h0 j lambda a hp hq hh0
    hh0degree hH hp8 hq10 hN hD hroot

/-- RIGHT-complement chamber `5 v1² = 8 b62`.  The extra
`2 u1² + v1³ = 0` is not used by the `h^{112}` identity.  Not a
closure. -/
theorem piFace810_linearRoot_rightComplement_pow112_dvd
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ (t0 v1 u1 s1 w1 b62 : k[X]) (eta : k),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 4 * v1 ∧
        p.coeff 5 = h0 ^ 2 * u1 ∧ q.coeff 8 = h0 ^ 6 * s1 ∧
        q.coeff 7 = h0 ^ 4 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        localClearedSixteenthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 4 * v1)
            (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (h0 ^ 6 * s1) (h0 ^ 4 * w1)
            (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C (17592186044416 * eta) * h0 ^ 112 :=
  piFace810_linearRoot_left_pow112_dvd p q H h0 j lambda a hp hq hh0
    hh0degree hH hp8 hq10 hN hD hroot

#print axioms linearPolynomial_nextTaylor810
#print axioms piFace810_linearRoot_lateMixin_nextTaylor
#print axioms localClearedSixteenthDefect810_algebraMap_eq_pow_scaledPi
#print axioms localClearedSixteenthDefect810_eq_C_pow_112_of_source
#print axioms localClearedSixteenthDefect810_eq_C_pow_112_of_source_valuated
#print axioms sourcePiResidual810_deriv_eq_zero_of_source
#print axioms scaledSourcePiResidual810_deriv_eq_zero_of_source
#print axioms piFace810_linearRoot_cancelExpose_of_source
#print axioms piFace810_linearRoot_false_of_scaledPi_simplePole
#print axioms piFace810_linearRoot_cancelExposePacket
#print axioms piFace810_linearRoot_left_pow112_dvd
#print axioms piFace810_linearRoot_rightU1Zero_pow112_dvd
#print axioms piFace810_linearRoot_rightComplement_pow112_dvd

end PiChamberPacket810

end Max11DegreeRoutes
