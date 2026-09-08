import Grok610DegreeZeroOrder75CeilingScratch

/-! # Mixed-arm closure of the `(6,10)` degree-zero linear-root chamber

`Grok610DegreeZeroOrder75CeilingScratch` closed arms `(a)(b)(c)` of
`degreeZeroFace610_linearRoot_order75Grandchildren` by cancelling all
six clearing powers after `h0^6 ∣` the jet quotient, exposing `rho` as
a polynomial, which cannot have derivative `C j / h0` with `j ≠ 0`.

The only surviving arm is `(d)`: the mixed `q41 = 0` tower at `M = 4`
(`h0^4 ∣ Q`), residual `o71n(a) + MixedOrderThree(a) = 0`, with
`q41n = C(q41n(a)) + h0 · q41nn` and `p32` nonzero at the split
carrying the five-term cofactor
`10*p32^2*q53 + (18*p32*w1 - 27*p21)*q3 = 0` and the eight-term
`q41n`-linear residual.

The jet quotient has `h`-degree at most `6`.  This file advances the
mixed tower through mixed orders `73`, `74`, `75`.  Each step peels the
remaining factor (pole-two, then pole-one, then the holomorphic
remainder) and names one more Taylor coefficient of `q41` honestly.
The mixed structure does **not** cap below `h^6`: after mixed order
`74` one has `h0^6 ∣` the jet quotient, which is frozen exhaustion.
Cancelling the six clearing powers exposes `rho` as a polynomial, and
`j ≠ 0` is impossible, so arm `(d)` is False.

**CLOSED:** arm `(d)` (mixed `q41 = 0` tower).
**CLOSED:** the whole linear-root chamber `degreeZeroFace610`, combined
with the order-`75` file (arms `(a)(b)(c)` already False there).

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section DegreeZeroMixedArmPeel610

variable {k : Type*} [Field k] [CharZero k]

/-- Next Taylor of a polynomial at a simple root of `h0`. -/
theorem linearPolynomial_nextTaylor610
    (h0 f : k[X]) (a : k) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) :
    ∃ fn : k[X], f = C (f.eval a) + h0 * fn := by
  have hα : (f - C (f.eval a)).eval a = 0 := by
    simp [Polynomial.eval_sub, Polynomial.eval_C]
  obtain ⟨fn, hT⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0
    (f - C (f.eval a)) a hdegree hroot hα
  exact ⟨fn, (sub_eq_iff_eq_add.mp hT).trans
    (add_comm (h0 * fn) (C (f.eval a)))⟩

/-- Mixed orders `73`, `74`, `75` of the `q41 = 0` tower.  Starting
from the landed `M = 4` vanishing, pole-two peels mixed order `73`
(naming `q41'''`), pole-one peels mixed order `74` (naming `q41''''`),
and the remaining factor after `h0^6` is the mixed order-`75`
holomorphic remainder (naming `q41'''''`).  This is frozen exhaustion:
the jet quotient has `h`-degree at most `6`. -/
theorem degreeZeroPostCollapseQ41ZeroMixedOrderSixHead610_dvd_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hq41 : q41.eval a = 0)
    (hderiv :
      Differential.deriv
          ((58498535041007616 : RatFunc k) *
            degreeZeroPostCollapsePrimitive610
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) a42)
              (algebraMap k[X] (RatFunc k) p32)
              (algebraMap k[X] (RatFunc k) p21)
              (algebraMap k[X] (RatFunc k) p1)
              (algebraMap k[X] (RatFunc k) p0)
              (algebraMap k[X] (RatFunc k) s2)
              (algebraMap k[X] (RatFunc k) u2)
              (algebraMap k[X] (RatFunc k) b63)
              (algebraMap k[X] (RatFunc k) q53)
              (algebraMap k[X] (RatFunc k) q41)
              (algebraMap k[X] (RatFunc k) q3)
              (algebraMap k[X] (RatFunc k) q2)
              (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ q41n q41nn q41nnn q41nnnn q41nnnnn : k[X],
      q41 = h0 * q41n ∧
        q41n = C (q41n.eval a) + h0 * q41nn ∧
        q41nn = C (q41nn.eval a) + h0 * q41nnn ∧
        q41nnn = C (q41nnn.eval a) + h0 * q41nnnn ∧
        q41nnnn = C (q41nnnn.eval a) + h0 * q41nnnnn ∧
        h0 ^ 6 ∣
          degreeZeroPostCollapseJetQuotient610 h0 w1 a42 p32 p21 p1 p0
            s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda) := by
  obtain ⟨q41n, q41nn, _o70n, _o71n, hq41eq, hTaylor, _ho70, _ho71,
      _hmix, hdvd⟩ :=
    degreeZeroPostCollapseQ41ZeroMixedOrderThree610_zero_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hq41 hderiv
  obtain ⟨q41nnn, hq41nnTaylor⟩ :=
    linearPolynomial_nextTaylor610 h0 q41nn a hdegree hroot
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let quotient : k[X] := degreeZeroPostCollapseJetQuotient610 h0 w1 a42
    p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  let rho : RatFunc k :=
    (58498535041007616 : RatFunc k) *
      degreeZeroPostCollapsePrimitive610 hRF
        (algebraMap k[X] (RatFunc k) w1)
        (algebraMap k[X] (RatFunc k) a42)
        (algebraMap k[X] (RatFunc k) p32)
        (algebraMap k[X] (RatFunc k) p21)
        (algebraMap k[X] (RatFunc k) p1)
        (algebraMap k[X] (RatFunc k) p0)
        (algebraMap k[X] (RatFunc k) s2)
        (algebraMap k[X] (RatFunc k) u2)
        (algebraMap k[X] (RatFunc k) b63)
        (algebraMap k[X] (RatFunc k) q53)
        (algebraMap k[X] (RatFunc k) q41)
        (algebraMap k[X] (RatFunc k) q3)
        (algebraMap k[X] (RatFunc k) q2)
        (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hbridge := degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive
    hRF (algebraMap k[X] (RatFunc k) w1)
    (algebraMap k[X] (RatFunc k) a42)
    (algebraMap k[X] (RatFunc k) p32)
    (algebraMap k[X] (RatFunc k) p21)
    (algebraMap k[X] (RatFunc k) p1)
    (algebraMap k[X] (RatFunc k) p0)
    (algebraMap k[X] (RatFunc k) s2)
    (algebraMap k[X] (RatFunc k) u2)
    (algebraMap k[X] (RatFunc k) b63)
    (algebraMap k[X] (RatFunc k) q53)
    (algebraMap k[X] (RatFunc k) q41)
    (algebraMap k[X] (RatFunc k) q3)
    (algebraMap k[X] (RatFunc k) q2)
    (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroPostCollapseJetQuotient610_map
    (algebraMap k[X] (RatFunc k)) h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53
      q41 q3 q2 q1 (Polynomial.C lambda)
  have hclear : algebraMap k[X] (RatFunc k) quotient = hRF ^ 6 * rho := by
    dsimp only [quotient, rho]
    rw [hmap]
    simp only [RatFunc.algebraMap_C]
    rw [mul_comm (hRF ^ 6), ← div_eq_iff (pow_ne_zero 6 hhRF)]
    simpa only [hRF] using hbridge
  obtain ⟨Q4, hQ4raw⟩ := hdvd
  have hQ4 : quotient = h0 ^ 4 * Q4 := by
    simpa [quotient] using hQ4raw
  have hclear2 : algebraMap k[X] (RatFunc k) Q4 = hRF ^ 2 * rho :=
    algebraMap_cancel_four_of_six_clearing610 h0 Q4 rho hh0 (by
      simpa [hQ4] using hclear)
  -- Mixed order `73`: pole-two forces the remaining factor after
  -- `h0^4` to vanish, mixing `q41'''`.
  have hQ4zero : Q4.eval a = 0 :=
    localLinearPoleTwo_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q4 rho hdegree hroot hclear2 (by simpa [rho, hRF] using hderiv)
  obtain ⟨Q5, hQ5⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q4 a
    hdegree hroot hQ4zero
  obtain ⟨q41nnnn, hq41nnnTaylor⟩ :=
    linearPolynomial_nextTaylor610 h0 q41nnn a hdegree hroot
  have hQ5quot : quotient = h0 ^ 5 * Q5 := by
    calc
      quotient = h0 ^ 4 * Q4 := hQ4
      _ = h0 ^ 4 * (h0 * Q5) := by rw [hQ5]
      _ = h0 ^ 5 * Q5 := by ring
  have hclear1 : algebraMap k[X] (RatFunc k) Q5 = hRF ^ 1 * rho :=
    algebraMap_cancel_five_of_six_clearing610 h0 Q5 rho hh0 (by
      simpa [hQ5quot] using hclear)
  -- Mixed order `74`: pole-one forces the remaining factor after
  -- `h0^5` to vanish, mixing `q41''''`.
  have hQ5zero : Q5.eval a = 0 :=
    localLinearPoleOne_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      Q5 rho hdegree hroot hclear1 (by simpa [rho, hRF] using hderiv)
  obtain ⟨Q6, hQ6⟩ := linearPolynomial_dvd_of_eval_eq_zero_610 h0 Q5 a
    hdegree hroot hQ5zero
  obtain ⟨q41nnnnn, hq41nnnnTaylor⟩ :=
    linearPolynomial_nextTaylor610 h0 q41nnnn a hdegree hroot
  -- Mixed order `75`: the remaining factor after `h0^6` is the last
  -- frozen head (holomorphic remainder).
  refine ⟨q41n, q41nn, q41nnn, q41nnnn, q41nnnnn, hq41eq, hTaylor,
    hq41nnTaylor, hq41nnnTaylor, hq41nnnnTaylor, ?_⟩
  refine ⟨Q6, ?_⟩
  calc
    quotient = h0 ^ 5 * Q5 := hQ5quot
    _ = h0 ^ 5 * (h0 * Q6) := by rw [hQ6]
    _ = h0 ^ 6 * Q6 := by ring

/-- **CLOSED.** Arm `(d)`: mixed `q41(a) = 0` tower.  Frozen exhaustion
is `h0^6`; the remaining factor is `rho` and `j ≠ 0` is impossible. -/
theorem degreeZeroPostCollapseQ41ZeroMixedOrderSixHead610_false_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hq41 : q41.eval a = 0)
    (hderiv :
      Differential.deriv
          ((58498535041007616 : RatFunc k) *
            degreeZeroPostCollapsePrimitive610
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) a42)
              (algebraMap k[X] (RatFunc k) p32)
              (algebraMap k[X] (RatFunc k) p21)
              (algebraMap k[X] (RatFunc k) p1)
              (algebraMap k[X] (RatFunc k) p0)
              (algebraMap k[X] (RatFunc k) s2)
              (algebraMap k[X] (RatFunc k) u2)
              (algebraMap k[X] (RatFunc k) b63)
              (algebraMap k[X] (RatFunc k) q53)
              (algebraMap k[X] (RatFunc k) q41)
              (algebraMap k[X] (RatFunc k) q3)
              (algebraMap k[X] (RatFunc k) q2)
              (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨_q41n, _q41nn, _q41nnn, _q41nnnn, _q41nnnnn, _hq41eq,
      _hTaylor, _hT3, _hT4, _hT5, hdvd⟩ :=
    degreeZeroPostCollapseQ41ZeroMixedOrderSixHead610_dvd_of_primitiveDeriv
      h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
      hdegree hroot hq41 hderiv
  exact degreeZeroPostCollapseJetQuotient610_pow_six_dvd_contradicts_simplePole
    h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda j a hh0
    hroot hdvd hderiv hj

theorem degreeZeroPostCollapseQ41ZeroMixedOrderSixHead610_false_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X])
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hj : j ≠ 0)
    (hw : p.coeff 5 = h0 ^ 5 * w1)
    (hp4deep : p.coeff 4 = h0 ^ 4 * a42)
    (hp3deep : p.coeff 3 = h0 ^ 2 * p32)
    (hp2deep : p.coeff 2 = h0 * p21)
    (hq8deep : q.coeff 8 = h0 ^ 8 * s2)
    (hq7deep : q.coeff 7 = h0 ^ 6 * u2)
    (hq6deep : q.coeff 6 = h0 ^ 5 * b63)
    (hq5deep : q.coeff 5 = h0 ^ 3 * q53)
    (hq4deep : q.coeff 4 = h0 * q41)
    (hq41 : q41.eval a = 0) : False := by
  have hjscaled : (58498535041007616 : k) * j ≠ 0 :=
    mul_ne_zero (by norm_num) hj
  exact degreeZeroPostCollapseQ41ZeroMixedOrderSixHead610_false_of_primitiveDeriv
    h0 w1 a42 p32 p21 (p.coeff 1) (p.coeff 0) s2 u2 b63 q53 q41
    (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
    (58498535041007616 * j) a hh0 hh0degree hroot hq41
    (degreeZeroPostCollapsePrimitive610_deriv_eq_simplePole_of_source
      p q H h0 j lambda w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0 hH
      hp6 hq10 hN hD hw hp4deep hp3deep hp2deep hq8deep hq7deep hq6deep
      hq5deep hq4deep)
    hjscaled

end DegreeZeroMixedArmPeel610

section DegreeZeroLinearRootChamber610

variable {k : Type*} [Field k] [CharZero k]

/-- **CLOSED.** Source-facing joint packet of the `(6,10)` degree-zero
linear-root chamber.  Arms `(a)(b)(c)` are False in the order-`75`
file; arm `(d)` is False above.  Combined, every linear-root arm of
`degreeZeroFace610` is False. -/
theorem degreeZeroFace610_linearRoot
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) (hj : j ≠ 0) :
    False := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep,
      hDarm⟩ :=
    degreeZeroFace610_linearRoot_order75Grandchildren p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda hj
  obtain ⟨hq41, _hfive, _q41n, _q41nn, _o70n, _o71n, _hq41eq, _hTaylor,
      _ho70, _ho71, _hmix, _hred⟩ := hDarm
  exact degreeZeroPostCollapseQ41ZeroMixedOrderSixHead610_false_of_source
    p q H h0 j lambda a w1 a42 p32 p21 s2 u2 b63 q53 q41 hp hq hh0
    hh0degree hH hp6 hq10 hN hD hroot hj hw hp4deep hp3deep hp2deep
    hq8deep hq7deep hq6deep hq5deep hq4deep hq41

#print axioms linearPolynomial_nextTaylor610
#print axioms degreeZeroPostCollapseQ41ZeroMixedOrderSixHead610_dvd_of_primitiveDeriv
#print axioms degreeZeroPostCollapseQ41ZeroMixedOrderSixHead610_false_of_primitiveDeriv
#print axioms degreeZeroPostCollapseQ41ZeroMixedOrderSixHead610_false_of_source
#print axioms degreeZeroFace610_linearRoot

end DegreeZeroLinearRootChamber610

end Max11DegreeRoutes
