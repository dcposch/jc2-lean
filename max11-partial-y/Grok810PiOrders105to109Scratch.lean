import Grok810PiOrders100to104Scratch

/-! # Orders `105` through `109` of the `(8,10)` degree-one `π` tower

`Grok810PiOrders100to104Scratch` leaves three live chambers after the
unsolved order-`104` coefficient is extracted:

* LEFT: `o103n(a) + Order104(a) = 0` with the frozen mixin and unsolved
  witnesses `m1, τ1, g1, k1`;
* RIGHT/`u1 = 0`: the fifteenth-face extra `16 b62 v1 = 5 v1³` mixed
  with the next coefficient;
* RIGHT complement: the extra `2 u1² + v1³ = 0` on `5 v1² = 8 b62`.

This file continues the unsolved tail through orders `105`, `106`,
`107`, `108`, and `109` in one module.  Each order `k` is the `h⁰`
coefficient of the previous Plus remainder, equivalently the
`h^(k-97)` coefficient of the unsolved tail and the `h^(k-96)`
coefficient of the factored residual after the order-`96` head.  The
four scalar load solves are not inserted as polynomial identities, and
the old scalar-solved jet is not imported.  Witnesses stay unsolved.

The landed fifteenth-face extras are carried from the parent: on
RIGHT/`u1 = 0` the mixed extra is `16 b62 v1 = 5 v1³`; on the complement
`5 v1² = 8 b62` it is `2 u1² + v1³ = 0`.  Those scalar conclusions of
the named residuals are not re-evaluated against the source-facing
residual.  No chamber is closed.  The next unused compact-numerator
order is `110`.  Orders `110`, `111`, and `112` remain after this
batch, then the cancel-and-expose endgame.

Vanishing is recorded in the `h0`-divisibility shape the ceiling lemma
consumes: `Head = h0 · o96n`, then `o(n-1)n + Order n = h0 · on n` for
`n = 97, …, 108`, and `o108n(a) + Order109(a) = 0`.  Intermediate
orders record the same shape truncated at that order.  The tower
ceiling is order `112` from the weight-`112` source power relation;
orders `96` through `112` exhaust the unsolved head before the
cancel-and-expose endgame (`ρ` polynomial versus `ρ' = j/h0`).  This
file does not close any chamber.

No total-degree or twice-prime theorem is used.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 1600000000
set_option linter.unusedVariables false

section PiOrder105Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`105` mixin: the `h⁰` coefficient of the order-`104` Plus
remainder, equivalently the `h^8` coefficient of the unsolved tail
and the `h^9` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder105810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2502741196800 : R) * t0 ^ 7 * a0 * lambda
    - (16818420842496 : R) * t0 ^ 5 * v1 * a0 * lambda
    + (16017543659520 : R) * t0 ^ 4 * u1 * a0 * lambda
    + (32035087319040 : R) * t0 ^ 3 * v1 ^ 2 * a0 * lambda
    - (15075335208960 : R) * t0 ^ 3 * a4 * a0 * lambda
    - (15075335208960 : R) * t0 ^ 3 * a3 * a1 * lambda
    - (7537667604480 : R) * t0 ^ 3 * a2 ^ 2 * lambda
    - (45226005626880 : R) * t0 ^ 2 * v1 * u1 * a0 * lambda
    - (15075335208960 : R) * t0 * v1 ^ 3 * a0 * lambda
    + (27831388078080 : R) * t0 * v1 * a4 * a0 * lambda
    + (27831388078080 : R) * t0 * v1 * a3 * a1 * lambda
    + (13915694039040 : R) * t0 * v1 * a2 ^ 2 * lambda
    + (13915694039040 : R) * t0 * u1 ^ 2 * a0 * lambda
    + (13915694039040 : R) * v1 ^ 2 * u1 * a0 * lambda
    - (12369505812480 : R) * u1 * a4 * a0 * lambda
    - (12369505812480 : R) * u1 * a3 * a1 * lambda
    - (6184752906240 : R) * u1 * a2 ^ 2 * lambda

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after `h` is removed from the order-`104` Plus
remainder. -/
def piLeftUnsolvedOrder105Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 6 * a0 ^ 2
    + (9895604649984 : R) * h ^ 5 * a1 * a0 * lambda
    + (5497558138880 : R) * h ^ 4 * t0 * a1 * a0
    + (17592186044416 : R) * h ^ 4 * a1 * b1
    + (35184372088832 : R) * h ^ 4 * a0 * b2
    - (12369505812480 : R) * h ^ 3 * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * h ^ 3 * t0 * a1 ^ 2 * lambda
    - (4398046511104 : R) * h ^ 2 * t0 * a2 * b1
    - (8796093022208 : R) * h ^ 2 * t0 * a1 * b2
    - (13194139533312 : R) * h ^ 2 * t0 * a0 * b3
    + (54975581388800 : R) * h ^ 2 * v1 * a2 * a0
    + (27487790694400 : R) * h ^ 2 * v1 * a1 ^ 2
    - (35184372088832 : R) * h ^ 2 * a2 * a0 * s1
    - (17592186044416 : R) * h ^ 2 * a1 ^ 2 * s1
    + (13915694039040 : R) * h * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * h * t0 ^ 2 * a2 * a1 * lambda
    - (12369505812480 : R) * h * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * h * v1 * a2 * a1 * lambda
    - (2576980377600 : R) * t0 ^ 3 * a3 * a0
    - (2576980377600 : R) * t0 ^ 3 * a2 * a1
    + (2748779069440 : R) * t0 ^ 2 * a3 * b1
    + (5497558138880 : R) * t0 ^ 2 * a2 * b2
    + (8246337208320 : R) * t0 ^ 2 * a1 * b3
    + (10995116277760 : R) * t0 ^ 2 * a0 * b4
    - (61847529062400 : R) * t0 * v1 * a3 * a0
    - (61847529062400 : R) * t0 * v1 * a2 * a1
    + (43980465111040 : R) * t0 * a3 * a0 * s1
    + (43980465111040 : R) * t0 * a2 * a1 * s1
    - (4398046511104 : R) * v1 * a3 * b1
    - (8796093022208 : R) * v1 * a2 * b2
    - (13194139533312 : R) * v1 * a1 * b3
    - (17592186044416 : R) * v1 * a0 * b4
    + (54975581388800 : R) * u1 * a3 * a0
    + (54975581388800 : R) * u1 * a2 * a1
    - (30786325577728 : R) * a3 * a0 * w1
    - (30786325577728 : R) * a2 * a1 * w1

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder104Plus810_of_order105
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder104Plus810, piLeftUnsolvedOrder105810,
    piLeftUnsolvedOrder105Plus810]
  ring

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder104Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder104Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder104Plus810_of_order105]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedTail810_of_order105
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 9 * piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order104, piLeftUnsolvedOrder104Plus810_of_order105]
  ring

/-- Order-`105` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder105810_t0u1Zero
    (v1 : R) : R :=
    0

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder105810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder105810_t0u1Zero v1 := by
  simp only [piLeftUnsolvedOrder105810,
    piLeftUnsolvedOrder105810_t0u1Zero, ht0, hu1]
  try ring

/-- Integer `1`-clearing of the LEFT order-`105` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder105810 (t0 v1 u1 a3 a2 a1 a0 b62 lambda : R) : R :=
    (2708849295360 : R) * t0 ^ 7 * a0 * lambda
    - (18612240777216 : R) * t0 ^ 5 * v1 * a0 * lambda
    + (19955491799040 : R) * t0 ^ 4 * u1 * a0 * lambda
    + (36528696852480 : R) * t0 ^ 3 * v1 ^ 2 * a0 * lambda
    - (15075335208960 : R) * t0 ^ 3 * a3 * a1 * lambda
    - (7537667604480 : R) * t0 ^ 3 * a2 ^ 2 * lambda
    - (12060268167168 : R) * t0 ^ 3 * a0 * b62 * lambda
    - (53343493816320 : R) * t0 ^ 2 * v1 * u1 * a0 * lambda
    - (18554258718720 : R) * t0 * v1 ^ 3 * a0 * lambda
    + (27831388078080 : R) * t0 * v1 * a3 * a1 * lambda
    + (13915694039040 : R) * t0 * v1 * a2 ^ 2 * lambda
    + (22265110462464 : R) * t0 * v1 * a0 * b62 * lambda
    + (17008070492160 : R) * t0 * u1 ^ 2 * a0 * lambda
    + (15461882265600 : R) * v1 ^ 2 * u1 * a0 * lambda
    - (12369505812480 : R) * u1 * a3 * a1 * lambda
    - (6184752906240 : R) * u1 * a2 ^ 2 * lambda
    - (9895604649984 : R) * u1 * a0 * b62 * lambda

/-- Integer `1`-clearing of the RIGHT/`u1 = 0` order-`105`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder105810 (v1 b62 : R) : R :=
    0

/-- Frozen order-`105` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder105810
    (v1 u1 a3 a2 a1 a0 lambda : R) : R :=
    (9277129359360 : R) * v1 ^ 2 * u1 * a0 * lambda
    - (12369505812480 : R) * u1 * a3 * a1 * lambda
    - (6184752906240 : R) * u1 * a2 ^ 2 * lambda

/-- Cofactor of `2 u1² + v1³` in the cleared complement mixin. -/
def piLeftUnsolvedRightComplementOrder105U1Cofactor810
    (v1 u1 a3 a2 a1 a0 lambda : R) : R :=
    0

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `2 u1² + v1³ = 0` specializes the complement
order-`105` mixin. -/
theorem piLeftUnsolvedRightComplementOrder105810_u1rel
    (v1 u1 a3 a2 a1 a0 lambda : R) :
    (2 : R) * piLeftUnsolvedRightComplementOrder105810 v1 u1 a3 a2 a1 a0 lambda =
      ((2 : R) * u1 ^ 2 + v1 ^ 3) *
          piLeftUnsolvedRightComplementOrder105U1Cofactor810
            v1 u1 a3 a2 a1 a0 lambda +
        (18554258718720 : R) * v1 ^ 2 * u1 * a0 * lambda
        - (24739011624960 : R) * u1 * a3 * a1 * lambda
        - (12369505812480 : R) * u1 * a2 ^ 2 * lambda := by
  simp only [piLeftUnsolvedRightComplementOrder105810,
    piLeftUnsolvedRightComplementOrder105U1Cofactor810]
  ring

end PiOrder105Frozen810

section PiOrder105Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 1600000000 in
theorem map_piLeftUnsolvedOrder105810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder105810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder105810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder105810

end PiOrder105Map810

section PiOrder105Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder105810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder105810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder105810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder105810_eval

end PiOrder105Eval810
section PiOrder105Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1600000000 in
/-- Remaining power vanishing after the unsolved order-`104` residual is
peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the
shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder105810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) = h * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o104n ∧
        o104n.eval a +
            piLeftUnsolvedOrder105810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, hmix⟩ :=
    piLeftUnsolvedOrder104810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o103n +
          piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder104810_eval]
    exact hmix
  obtain ⟨o104n, ho104⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o103n +
        piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
      a hdegree hroot hsum0
  have h96 : h ^ 96 ≠ 0 := pow_ne_zero 96 hh
  have hquot :
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) +
        h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 16 := by
    apply mul_left_cancel₀ h96
    rw [← localClearedSixteenthDefect810_left_unsolved_factored]
    rw [hpower]
    ring
  have hcancel :
      o96n +
          piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
            b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 15 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
              b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
              w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho]
        ring
      _ = Polynomial.C eta * h ^ 16 := hquot
      _ = h * (Polynomial.C eta * h ^ 15) := by ring
  have hplus14 :
      o97n +
          piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 14 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho97]
        ring
      _ = o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedTail810_of_order97]
        ring
      _ = Polynomial.C eta * h ^ 15 := hcancel
      _ = h * (Polynomial.C eta * h ^ 14) := by ring
  have hplus13 :
      o98n +
          piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 13 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho98]
        ring
      _ = o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder97Plus810_of_order98]
        ring
      _ = Polynomial.C eta * h ^ 14 := hplus14
      _ = h * (Polynomial.C eta * h ^ 13) := by ring
  have hplus12 :
      o99n +
          piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 12 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho99]
        ring
      _ = o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder98Plus810_of_order99]
        ring
      _ = Polynomial.C eta * h ^ 13 := hplus13
      _ = h * (Polynomial.C eta * h ^ 12) := by ring
  have hplus11 :
      o100n +
          piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 11 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho100]
        ring
      _ = o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder99Plus810_of_order100]
        ring
      _ = Polynomial.C eta * h ^ 12 := hplus12
      _ = h * (Polynomial.C eta * h ^ 11) := by ring
  have hplus10 :
      o101n +
          piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 10 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho101]
        ring
      _ = o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder100Plus810_of_order101]
        ring
      _ = Polynomial.C eta * h ^ 11 := hplus11
      _ = h * (Polynomial.C eta * h ^ 10) := by ring
  have hplus9 :
      o102n +
          piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 9 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho102]
        ring
      _ = o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder101Plus810_of_order102]
        ring
      _ = Polynomial.C eta * h ^ 10 := hplus10
      _ = h * (Polynomial.C eta * h ^ 9) := by ring
  have hplus8 :
      o103n +
          piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 8 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho103]
        ring
      _ = o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder102Plus810_of_order103]
        ring
      _ = Polynomial.C eta * h ^ 9 := hplus9
      _ = h * (Polynomial.C eta * h ^ 8) := by ring
  have hplus7 :
      o104n +
          piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 7 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o104n +
            piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho104]
        ring
      _ = o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder103Plus810_of_order104]
        ring
      _ = Polynomial.C eta * h ^ 8 := hplus8
      _ = h * (Polynomial.C eta * h ^ 7) := by ring
  have htail :
      (piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder104Plus810_of_order105]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus7
  rw [← piLeftUnsolvedOrder105810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`105` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder105810_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (t0 v1 u1 s1 w1 b62 : k[X])
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (ht0 : p.coeff 7 = h0 ^ 6 * t0)
    (hv1 : p.coeff 6 = h0 ^ 4 * v1)
    (hu1 : p.coeff 5 = h0 ^ 2 * u1)
    (hs1 : q.coeff 8 = h0 ^ 6 * s1)
    (hw1 : q.coeff 7 = h0 ^ 4 * w1)
    (hb62 : q.coeff 6 = h0 ^ 2 * b62) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62 (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o104n ∧
        o104n.eval a +
            piLeftUnsolvedOrder105810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 := by
  obtain ⟨eta, heta⟩ :=
    sourcePiResidual810_eq_C_of_source p q H h0 j lambda hp hq hh0 hH
      hp8 hq10 hN hD
  have hNpeel :
      5 * (h0 ^ 6 * t0) * h0 ^ 2 - 4 * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    simpa only [ht0, hH] using hN
  have hpi :
      sourcePiResidual810
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * t0))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * v1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * u1))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 9))
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * s1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * w1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * b62))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))
          (RatFunc.C lambda) =
        algebraMap k (RatFunc k) eta := by
    simpa only [ht0, hv1, hu1, hs1, hw1, hb62] using heta
  have hpower :=
    piSourcePowerRelation810_of_residual_eq_C h0 (h0 ^ 6 * t0)
      (h0 ^ 4 * v1) (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 9) (h0 ^ 6 * s1)
      (h0 ^ 4 * w1) (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda eta hh0 hNpeel hpi
  exact piLeftUnsolvedOrder105810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`105` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order105Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n o102n o103n o104n : k[X]),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
            (q.coeff 1) (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o104n ∧
        o104n.eval a +
            piLeftUnsolvedOrder105810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : k[X]),
              (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                    (5 : k[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : k[X]) * w1 - (160 : k[X]) * u1 -
                    (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : k) * lambda * t0.eval a = 0 ∧
                (4 : k) * tau1.eval a +
                    (9 : k) * lambda * (t0.eval a) ^ 2 +
                  (144 : k) * lambda * v1.eval a = 0) ∧
            (∃ g1 : k[X],
              (2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
                    (35 : k[X]) * t0 ^ 4 -
                    (240 : k[X]) * t0 ^ 2 * v1 +
                    (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : k) * g1.eval a +
                    (3 : k) * lambda *
                      ((7 : k) * (t0.eval a) ^ 3 -
                        (48 : k) * t0.eval a * v1.eval a -
                        (384 : k) * u1.eval a) = 0) ∧
            (∃ k1 : k[X],
              (81920 : k[X]) * (p.coeff 4) * t0 +
                    (131072 : k[X]) * (q.coeff 5) -
                    (98304 : k[X]) * b62 * t0 +
                    (2912 : k[X]) * t0 ^ 5 -
                    (20480 : k[X]) * t0 ^ 3 * v1 +
                    (46080 : k[X]) * t0 ^ 2 * u1 +
                    (30720 : k[X]) * t0 * v1 ^ 2 -
                    (40960 : k[X]) * u1 * v1 =
                  h0 * k1)) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            (40 : k) * (p.coeff 4).eval a - (32 : k) * b62.eval a +
              (5 : k) * (v1.eval a) ^ 2 = 0 ∧
            (16 : k) * (q.coeff 5).eval a =
              (5 : k) * u1.eval a * v1.eval a ∧
            ((u1.eval a = 0 ∧ o96n.eval a = 0 ∧
                (16 : k) * b62.eval a * v1.eval a =
                  (5 : k) * (v1.eval a) ^ 3) ∨
              ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a =
                  0 ∧
                (2 : k) * (u1.eval a) ^ 2 + (v1.eval a) ^ 3 =
                  0)))) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, hmix104, hsplit⟩ :=
    piFace810_linearRoot_order104Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n', o102n', o103n', o104n, ho', ho97', ho98', ho99', ho100', ho101', ho102', ho103', ho104, hmix105⟩ :=
    piLeftUnsolvedOrder105810_zero_of_source p q H h0 j lambda a t0 v1
      u1 s1 w1 b62 hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot ht0 ha6
      ha5 hb8 hb7 hb62
  have ho96eq : o96n = o96n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o96n = piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
          (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) (Polynomial.C lambda) := ho96.symm
      _ = h0 * o96n' := ho'
  subst ho96eq
  have ho97eq : o97n = o97n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o97n = o96n +
          piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho97.symm
      _ = h0 * o97n' := ho97'
  subst ho97eq
  have ho98eq : o98n = o98n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o98n = o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho98.symm
      _ = h0 * o98n' := ho98'
  subst ho98eq
  have ho99eq : o99n = o99n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o99n = o98n +
          piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho99.symm
      _ = h0 * o99n' := ho99'
  subst ho99eq
  have ho100eq : o100n = o100n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o100n = o99n +
          piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho100.symm
      _ = h0 * o100n' := ho100'
  subst ho100eq
  have ho101eq : o101n = o101n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o101n = o100n +
          piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho101.symm
      _ = h0 * o101n' := ho101'
  subst ho101eq
  have ho102eq : o102n = o102n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o102n = o101n +
          piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho102.symm
      _ = h0 * o102n' := ho102'
  subst ho102eq
  have ho103eq : o103n = o103n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o103n = o102n +
          piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho103.symm
      _ = h0 * o103n' := ho103'
  subst ho103eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, hmix105, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder104Plus810_of_order105
#print axioms piLeftUnsolvedOrder105810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder105810_zero_of_power
#print axioms piLeftUnsolvedOrder105810_zero_of_source
#print axioms piFace810_linearRoot_order105Chambers
#print axioms piLeftUnsolvedRightComplementOrder105810_u1rel

end PiOrder105Source810
section PiOrder106Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`106` mixin: the `h⁰` coefficient of the order-`105` Plus
remainder, equivalently the `h^9` coefficient of the unsolved tail
and the `h^10` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder106810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2576980377600 : R) * t0 ^ 3 * a3 * a0
    - (2576980377600 : R) * t0 ^ 3 * a2 * a1
    + (2748779069440 : R) * t0 ^ 2 * a3 * b1
    + (5497558138880 : R) * t0 ^ 2 * a2 * b2
    + (8246337208320 : R) * t0 ^ 2 * a1 * b3
    + (10995116277760 : R) * t0 ^ 2 * a0 * b4
    - (61847529062400 : R) * t0 * v1 * a3 * a0
    - (61847529062400 : R) * t0 * v1 * a2 * a1
    + (43980465111040 : R) * t0 * a3 * a0 * s1
    + (43980465111040 : R) * t0 * a2 * a1 * s1
    - (4398046511104 : R) * v1 * a3 * b1
    - (8796093022208 : R) * v1 * a2 * b2
    - (13194139533312 : R) * v1 * a1 * b3
    - (17592186044416 : R) * v1 * a0 * b4
    + (54975581388800 : R) * u1 * a3 * a0
    + (54975581388800 : R) * u1 * a2 * a1
    - (30786325577728 : R) * a3 * a0 * w1
    - (30786325577728 : R) * a2 * a1 * w1

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after `h` is removed from the order-`105` Plus
remainder. -/
def piLeftUnsolvedOrder106Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 5 * a0 ^ 2
    + (9895604649984 : R) * h ^ 4 * a1 * a0 * lambda
    + (5497558138880 : R) * h ^ 3 * t0 * a1 * a0
    + (17592186044416 : R) * h ^ 3 * a1 * b1
    + (35184372088832 : R) * h ^ 3 * a0 * b2
    - (12369505812480 : R) * h ^ 2 * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * h ^ 2 * t0 * a1 ^ 2 * lambda
    - (4398046511104 : R) * h * t0 * a2 * b1
    - (8796093022208 : R) * h * t0 * a1 * b2
    - (13194139533312 : R) * h * t0 * a0 * b3
    + (54975581388800 : R) * h * v1 * a2 * a0
    + (27487790694400 : R) * h * v1 * a1 ^ 2
    - (35184372088832 : R) * h * a2 * a0 * s1
    - (17592186044416 : R) * h * a1 ^ 2 * s1
    + (13915694039040 : R) * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * t0 ^ 2 * a2 * a1 * lambda
    - (12369505812480 : R) * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * v1 * a2 * a1 * lambda

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder105Plus810_of_order106
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder105Plus810, piLeftUnsolvedOrder106810,
    piLeftUnsolvedOrder106Plus810]
  ring

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder105Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder105Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder105Plus810_of_order106]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedTail810_of_order106
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 9 * piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 10 * piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order105, piLeftUnsolvedOrder105Plus810_of_order106]
  ring

/-- Order-`106` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder106810_t0u1Zero
    (v1 a3 a2 a1 a0 w1 b4 b3 b2 b1 : R) : R :=
    - (4398046511104 : R) * v1 * a3 * b1
    - (8796093022208 : R) * v1 * a2 * b2
    - (13194139533312 : R) * v1 * a1 * b3
    - (17592186044416 : R) * v1 * a0 * b4
    - (30786325577728 : R) * a3 * a0 * w1
    - (30786325577728 : R) * a2 * a1 * w1

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder106810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder106810_t0u1Zero v1 a3 a2 a1 a0 w1 b4 b3 b2 b1 := by
  simp only [piLeftUnsolvedOrder106810,
    piLeftUnsolvedOrder106810_t0u1Zero, ht0, hu1]
  try ring

/-- Integer `1`-clearing of the LEFT order-`106` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder106810 (t0 v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 : R) : R :=
    (5497558138880 : R) * t0 ^ 3 * a3 * a0
    + (5497558138880 : R) * t0 ^ 3 * a2 * a1
    + (2748779069440 : R) * t0 ^ 2 * a3 * b1
    + (5497558138880 : R) * t0 ^ 2 * a2 * b2
    + (8246337208320 : R) * t0 ^ 2 * a1 * b3
    + (10995116277760 : R) * t0 ^ 2 * a0 * b4
    - (16492674416640 : R) * t0 * v1 * a3 * a0
    - (16492674416640 : R) * t0 * v1 * a2 * a1
    - (4398046511104 : R) * v1 * a3 * b1
    - (8796093022208 : R) * v1 * a2 * b2
    - (13194139533312 : R) * v1 * a1 * b3
    - (17592186044416 : R) * v1 * a0 * b4
    + (16492674416640 : R) * u1 * a3 * a0
    + (16492674416640 : R) * u1 * a2 * a1

/-- Integer `1`-clearing of the RIGHT/`u1 = 0` order-`106`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder106810 (v1 a3 a2 a1 a0 b4 b3 b2 b1 b62 : R) : R :=
    - (4398046511104 : R) * v1 * a3 * b1
    - (8796093022208 : R) * v1 * a2 * b2
    - (13194139533312 : R) * v1 * a1 * b3
    - (17592186044416 : R) * v1 * a0 * b4

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedRightU1ZeroOrder106810_v1Zero
    (v1 a3 a2 a1 a0 b4 b3 b2 b1 b62 : R) (hv1 : v1 = 0) :
    piLeftUnsolvedRightU1ZeroOrder106810 v1 a3 a2 a1 a0 b4 b3 b2 b1 b62 = 0 := by
  simp only [piLeftUnsolvedRightU1ZeroOrder106810, hv1]
  try ring

/-- Cofactor of `16 b62 - 5 v1²` in the cleared RIGHT/`u1 = 0`
order-`106` mixin. -/
def piLeftUnsolvedRightU1ZeroOrder106B62Cofactor810
    (v1 a3 a2 a1 a0 b4 b3 b2 b1 b62 : R) : R :=
    0

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `16 b62 = 5 v1²` specializes the RIGHT/`u1 = 0`
order-`106` mixin. -/
theorem piLeftUnsolvedRightU1ZeroOrder106810_b62Law
    (v1 a3 a2 a1 a0 b4 b3 b2 b1 b62 : R) :
    (16 : R) * piLeftUnsolvedRightU1ZeroOrder106810 v1 a3 a2 a1 a0 b4 b3 b2 b1 b62 =
      ((16 : R) * b62 - (5 : R) * v1 ^ 2) *
          piLeftUnsolvedRightU1ZeroOrder106B62Cofactor810
            v1 a3 a2 a1 a0 b4 b3 b2 b1 b62 +
        - (70368744177664 : R) * v1 * a3 * b1
        - (140737488355328 : R) * v1 * a2 * b2
        - (211106232532992 : R) * v1 * a1 * b3
        - (281474976710656 : R) * v1 * a0 * b4 := by
  simp only [piLeftUnsolvedRightU1ZeroOrder106810,
    piLeftUnsolvedRightU1ZeroOrder106B62Cofactor810]
  ring

/-- Frozen order-`106` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder106810
    (v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 : R) : R :=
    - (4398046511104 : R) * v1 * a3 * b1
    - (8796093022208 : R) * v1 * a2 * b2
    - (13194139533312 : R) * v1 * a1 * b3
    - (17592186044416 : R) * v1 * a0 * b4
    + (16492674416640 : R) * u1 * a3 * a0
    + (16492674416640 : R) * u1 * a2 * a1

/-- Cofactor of `2 u1² + v1³` in the cleared complement mixin. -/
def piLeftUnsolvedRightComplementOrder106U1Cofactor810
    (v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 : R) : R :=
    0

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `2 u1² + v1³ = 0` specializes the complement
order-`106` mixin. -/
theorem piLeftUnsolvedRightComplementOrder106810_u1rel
    (v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 : R) :
    (2 : R) * piLeftUnsolvedRightComplementOrder106810 v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 =
      ((2 : R) * u1 ^ 2 + v1 ^ 3) *
          piLeftUnsolvedRightComplementOrder106U1Cofactor810
            v1 u1 a3 a2 a1 a0 b4 b3 b2 b1 +
        - (8796093022208 : R) * v1 * a3 * b1
        - (17592186044416 : R) * v1 * a2 * b2
        - (26388279066624 : R) * v1 * a1 * b3
        - (35184372088832 : R) * v1 * a0 * b4
        + (32985348833280 : R) * u1 * a3 * a0
        + (32985348833280 : R) * u1 * a2 * a1 := by
  simp only [piLeftUnsolvedRightComplementOrder106810,
    piLeftUnsolvedRightComplementOrder106U1Cofactor810]
  ring

end PiOrder106Frozen810

section PiOrder106Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 1600000000 in
theorem map_piLeftUnsolvedOrder106810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder106810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder106810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder106810

end PiOrder106Map810

section PiOrder106Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder106810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder106810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder106810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder106810_eval

end PiOrder106Eval810
section PiOrder106Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1600000000 in
/-- Remaining power vanishing after the unsolved order-`105` residual is
peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the
shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder106810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) = h * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o105n ∧
        o105n.eval a +
            piLeftUnsolvedOrder106810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, hmix⟩ :=
    piLeftUnsolvedOrder105810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o104n +
          piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder105810_eval]
    exact hmix
  obtain ⟨o105n, ho105⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o104n +
        piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
      a hdegree hroot hsum0
  have h96 : h ^ 96 ≠ 0 := pow_ne_zero 96 hh
  have hquot :
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) +
        h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 16 := by
    apply mul_left_cancel₀ h96
    rw [← localClearedSixteenthDefect810_left_unsolved_factored]
    rw [hpower]
    ring
  have hcancel :
      o96n +
          piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
            b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 15 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
              b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
              w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho]
        ring
      _ = Polynomial.C eta * h ^ 16 := hquot
      _ = h * (Polynomial.C eta * h ^ 15) := by ring
  have hplus14 :
      o97n +
          piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 14 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho97]
        ring
      _ = o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedTail810_of_order97]
        ring
      _ = Polynomial.C eta * h ^ 15 := hcancel
      _ = h * (Polynomial.C eta * h ^ 14) := by ring
  have hplus13 :
      o98n +
          piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 13 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho98]
        ring
      _ = o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder97Plus810_of_order98]
        ring
      _ = Polynomial.C eta * h ^ 14 := hplus14
      _ = h * (Polynomial.C eta * h ^ 13) := by ring
  have hplus12 :
      o99n +
          piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 12 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho99]
        ring
      _ = o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder98Plus810_of_order99]
        ring
      _ = Polynomial.C eta * h ^ 13 := hplus13
      _ = h * (Polynomial.C eta * h ^ 12) := by ring
  have hplus11 :
      o100n +
          piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 11 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho100]
        ring
      _ = o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder99Plus810_of_order100]
        ring
      _ = Polynomial.C eta * h ^ 12 := hplus12
      _ = h * (Polynomial.C eta * h ^ 11) := by ring
  have hplus10 :
      o101n +
          piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 10 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho101]
        ring
      _ = o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder100Plus810_of_order101]
        ring
      _ = Polynomial.C eta * h ^ 11 := hplus11
      _ = h * (Polynomial.C eta * h ^ 10) := by ring
  have hplus9 :
      o102n +
          piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 9 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho102]
        ring
      _ = o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder101Plus810_of_order102]
        ring
      _ = Polynomial.C eta * h ^ 10 := hplus10
      _ = h * (Polynomial.C eta * h ^ 9) := by ring
  have hplus8 :
      o103n +
          piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 8 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho103]
        ring
      _ = o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder102Plus810_of_order103]
        ring
      _ = Polynomial.C eta * h ^ 9 := hplus9
      _ = h * (Polynomial.C eta * h ^ 8) := by ring
  have hplus7 :
      o104n +
          piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 7 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o104n +
            piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho104]
        ring
      _ = o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder103Plus810_of_order104]
        ring
      _ = Polynomial.C eta * h ^ 8 := hplus8
      _ = h * (Polynomial.C eta * h ^ 7) := by ring
  have hplus6 :
      o105n +
          piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 6 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o105n +
            piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho105]
        ring
      _ = o104n +
            piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder104Plus810_of_order105]
        ring
      _ = Polynomial.C eta * h ^ 7 := hplus7
      _ = h * (Polynomial.C eta * h ^ 6) := by ring
  have htail :
      (piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder105Plus810_of_order106]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus6
  rw [← piLeftUnsolvedOrder106810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`106` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder106810_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (t0 v1 u1 s1 w1 b62 : k[X])
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (ht0 : p.coeff 7 = h0 ^ 6 * t0)
    (hv1 : p.coeff 6 = h0 ^ 4 * v1)
    (hu1 : p.coeff 5 = h0 ^ 2 * u1)
    (hs1 : q.coeff 8 = h0 ^ 6 * s1)
    (hw1 : q.coeff 7 = h0 ^ 4 * w1)
    (hb62 : q.coeff 6 = h0 ^ 2 * b62) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62 (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o105n ∧
        o105n.eval a +
            piLeftUnsolvedOrder106810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 := by
  obtain ⟨eta, heta⟩ :=
    sourcePiResidual810_eq_C_of_source p q H h0 j lambda hp hq hh0 hH
      hp8 hq10 hN hD
  have hNpeel :
      5 * (h0 ^ 6 * t0) * h0 ^ 2 - 4 * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    simpa only [ht0, hH] using hN
  have hpi :
      sourcePiResidual810
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * t0))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * v1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * u1))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 9))
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * s1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * w1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * b62))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))
          (RatFunc.C lambda) =
        algebraMap k (RatFunc k) eta := by
    simpa only [ht0, hv1, hu1, hs1, hw1, hb62] using heta
  have hpower :=
    piSourcePowerRelation810_of_residual_eq_C h0 (h0 ^ 6 * t0)
      (h0 ^ 4 * v1) (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 9) (h0 ^ 6 * s1)
      (h0 ^ 4 * w1) (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda eta hh0 hNpeel hpi
  exact piLeftUnsolvedOrder106810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`106` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order106Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n : k[X]),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
            (q.coeff 1) (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o105n ∧
        o105n.eval a +
            piLeftUnsolvedOrder106810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : k[X]),
              (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                    (5 : k[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : k[X]) * w1 - (160 : k[X]) * u1 -
                    (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : k) * lambda * t0.eval a = 0 ∧
                (4 : k) * tau1.eval a +
                    (9 : k) * lambda * (t0.eval a) ^ 2 +
                  (144 : k) * lambda * v1.eval a = 0) ∧
            (∃ g1 : k[X],
              (2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
                    (35 : k[X]) * t0 ^ 4 -
                    (240 : k[X]) * t0 ^ 2 * v1 +
                    (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : k) * g1.eval a +
                    (3 : k) * lambda *
                      ((7 : k) * (t0.eval a) ^ 3 -
                        (48 : k) * t0.eval a * v1.eval a -
                        (384 : k) * u1.eval a) = 0) ∧
            (∃ k1 : k[X],
              (81920 : k[X]) * (p.coeff 4) * t0 +
                    (131072 : k[X]) * (q.coeff 5) -
                    (98304 : k[X]) * b62 * t0 +
                    (2912 : k[X]) * t0 ^ 5 -
                    (20480 : k[X]) * t0 ^ 3 * v1 +
                    (46080 : k[X]) * t0 ^ 2 * u1 +
                    (30720 : k[X]) * t0 * v1 ^ 2 -
                    (40960 : k[X]) * u1 * v1 =
                  h0 * k1)) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            (40 : k) * (p.coeff 4).eval a - (32 : k) * b62.eval a +
              (5 : k) * (v1.eval a) ^ 2 = 0 ∧
            (16 : k) * (q.coeff 5).eval a =
              (5 : k) * u1.eval a * v1.eval a ∧
            ((u1.eval a = 0 ∧ o96n.eval a = 0 ∧
                (16 : k) * b62.eval a * v1.eval a =
                  (5 : k) * (v1.eval a) ^ 3) ∨
              ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a =
                  0 ∧
                (2 : k) * (u1.eval a) ^ 2 + (v1.eval a) ^ 3 =
                  0)))) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, hmix105, hsplit⟩ :=
    piFace810_linearRoot_order105Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n', o102n', o103n', o104n', o105n, ho', ho97', ho98', ho99', ho100', ho101', ho102', ho103', ho104', ho105, hmix106⟩ :=
    piLeftUnsolvedOrder106810_zero_of_source p q H h0 j lambda a t0 v1
      u1 s1 w1 b62 hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot ht0 ha6
      ha5 hb8 hb7 hb62
  have ho96eq : o96n = o96n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o96n = piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
          (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) (Polynomial.C lambda) := ho96.symm
      _ = h0 * o96n' := ho'
  subst ho96eq
  have ho97eq : o97n = o97n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o97n = o96n +
          piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho97.symm
      _ = h0 * o97n' := ho97'
  subst ho97eq
  have ho98eq : o98n = o98n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o98n = o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho98.symm
      _ = h0 * o98n' := ho98'
  subst ho98eq
  have ho99eq : o99n = o99n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o99n = o98n +
          piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho99.symm
      _ = h0 * o99n' := ho99'
  subst ho99eq
  have ho100eq : o100n = o100n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o100n = o99n +
          piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho100.symm
      _ = h0 * o100n' := ho100'
  subst ho100eq
  have ho101eq : o101n = o101n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o101n = o100n +
          piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho101.symm
      _ = h0 * o101n' := ho101'
  subst ho101eq
  have ho102eq : o102n = o102n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o102n = o101n +
          piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho102.symm
      _ = h0 * o102n' := ho102'
  subst ho102eq
  have ho103eq : o103n = o103n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o103n = o102n +
          piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho103.symm
      _ = h0 * o103n' := ho103'
  subst ho103eq
  have ho104eq : o104n = o104n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o104n = o103n +
          piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho104.symm
      _ = h0 * o104n' := ho104'
  subst ho104eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, hmix106, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder105Plus810_of_order106
#print axioms piLeftUnsolvedOrder106810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder106810_zero_of_power
#print axioms piLeftUnsolvedOrder106810_zero_of_source
#print axioms piFace810_linearRoot_order106Chambers
#print axioms piLeftUnsolvedRightU1ZeroOrder106810_b62Law
#print axioms piLeftUnsolvedRightComplementOrder106810_u1rel

end PiOrder106Source810
section PiOrder107Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`107` mixin: the `h⁰` coefficient of the order-`106` Plus
remainder, equivalently the `h^10` coefficient of the unsolved tail
and the `h^11` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder107810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (13915694039040 : R) * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * t0 ^ 2 * a2 * a1 * lambda
    - (12369505812480 : R) * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * v1 * a2 * a1 * lambda

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after `h` is removed from the order-`106` Plus
remainder. -/
def piLeftUnsolvedOrder107Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 4 * a0 ^ 2
    + (9895604649984 : R) * h ^ 3 * a1 * a0 * lambda
    + (5497558138880 : R) * h ^ 2 * t0 * a1 * a0
    + (17592186044416 : R) * h ^ 2 * a1 * b1
    + (35184372088832 : R) * h ^ 2 * a0 * b2
    - (12369505812480 : R) * h * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * h * t0 * a1 ^ 2 * lambda
    - (4398046511104 : R) * t0 * a2 * b1
    - (8796093022208 : R) * t0 * a1 * b2
    - (13194139533312 : R) * t0 * a0 * b3
    + (54975581388800 : R) * v1 * a2 * a0
    + (27487790694400 : R) * v1 * a1 ^ 2
    - (35184372088832 : R) * a2 * a0 * s1
    - (17592186044416 : R) * a1 ^ 2 * s1

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder106Plus810_of_order107
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder106Plus810, piLeftUnsolvedOrder107810,
    piLeftUnsolvedOrder107Plus810]
  ring

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder106Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder106Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder106Plus810_of_order107]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedTail810_of_order107
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 9 * piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 10 * piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 11 * piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order106, piLeftUnsolvedOrder106Plus810_of_order107]
  ring

/-- Order-`107` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder107810_t0u1Zero
    (v1 a3 a2 a1 a0 lambda : R) : R :=
    - (12369505812480 : R) * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * v1 * a2 * a1 * lambda

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder107810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder107810_t0u1Zero v1 a3 a2 a1 a0 lambda := by
  simp only [piLeftUnsolvedOrder107810,
    piLeftUnsolvedOrder107810_t0u1Zero, ht0, hu1]
  try ring

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedOrder107810_t0u1Zero_v1Zero
    (v1 a3 a2 a1 a0 lambda : R) (hv1 : v1 = 0) :
    piLeftUnsolvedOrder107810_t0u1Zero v1 a3 a2 a1 a0 lambda = 0 := by
  simp only [piLeftUnsolvedOrder107810_t0u1Zero, hv1]
  try ring

/-- Integer `1`-clearing of the LEFT order-`107` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder107810 (t0 v1 a3 a2 a1 a0 lambda : R) : R :=
    (13915694039040 : R) * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * t0 ^ 2 * a2 * a1 * lambda
    - (12369505812480 : R) * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * v1 * a2 * a1 * lambda

/-- Integer `1`-clearing of the RIGHT/`u1 = 0` order-`107`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder107810 (v1 a3 a2 a1 a0 lambda b62 : R) : R :=
    - (12369505812480 : R) * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * v1 * a2 * a1 * lambda

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedRightU1ZeroOrder107810_v1Zero
    (v1 a3 a2 a1 a0 lambda b62 : R) (hv1 : v1 = 0) :
    piLeftUnsolvedRightU1ZeroOrder107810 v1 a3 a2 a1 a0 lambda b62 = 0 := by
  simp only [piLeftUnsolvedRightU1ZeroOrder107810, hv1]
  try ring

/-- Cofactor of `16 b62 - 5 v1²` in the cleared RIGHT/`u1 = 0`
order-`107` mixin. -/
def piLeftUnsolvedRightU1ZeroOrder107B62Cofactor810
    (v1 a3 a2 a1 a0 lambda b62 : R) : R :=
    0

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `16 b62 = 5 v1²` specializes the RIGHT/`u1 = 0`
order-`107` mixin. -/
theorem piLeftUnsolvedRightU1ZeroOrder107810_b62Law
    (v1 a3 a2 a1 a0 lambda b62 : R) :
    (16 : R) * piLeftUnsolvedRightU1ZeroOrder107810 v1 a3 a2 a1 a0 lambda b62 =
      ((16 : R) * b62 - (5 : R) * v1 ^ 2) *
          piLeftUnsolvedRightU1ZeroOrder107B62Cofactor810
            v1 a3 a2 a1 a0 lambda b62 +
        - (197912092999680 : R) * v1 * a3 * a0 * lambda
        - (197912092999680 : R) * v1 * a2 * a1 * lambda := by
  simp only [piLeftUnsolvedRightU1ZeroOrder107810,
    piLeftUnsolvedRightU1ZeroOrder107B62Cofactor810]
  ring

/-- Frozen order-`107` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder107810
    (v1 a3 a2 a1 a0 lambda u1 : R) : R :=
    - (12369505812480 : R) * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * v1 * a2 * a1 * lambda

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedRightComplementOrder107810_v1Zero
    (v1 a3 a2 a1 a0 lambda u1 : R) (hv1 : v1 = 0) :
    piLeftUnsolvedRightComplementOrder107810 v1 a3 a2 a1 a0 lambda u1 = 0 := by
  simp only [piLeftUnsolvedRightComplementOrder107810, hv1]
  try ring

/-- Cofactor of `2 u1² + v1³` in the cleared complement mixin. -/
def piLeftUnsolvedRightComplementOrder107U1Cofactor810
    (v1 a3 a2 a1 a0 lambda u1 : R) : R :=
    0

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `2 u1² + v1³ = 0` specializes the complement
order-`107` mixin. -/
theorem piLeftUnsolvedRightComplementOrder107810_u1rel
    (v1 a3 a2 a1 a0 lambda u1 : R) :
    (2 : R) * piLeftUnsolvedRightComplementOrder107810 v1 a3 a2 a1 a0 lambda u1 =
      ((2 : R) * u1 ^ 2 + v1 ^ 3) *
          piLeftUnsolvedRightComplementOrder107U1Cofactor810
            v1 a3 a2 a1 a0 lambda u1 +
        - (24739011624960 : R) * v1 * a3 * a0 * lambda
        - (24739011624960 : R) * v1 * a2 * a1 * lambda := by
  simp only [piLeftUnsolvedRightComplementOrder107810,
    piLeftUnsolvedRightComplementOrder107U1Cofactor810]
  ring

end PiOrder107Frozen810

section PiOrder107Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 1600000000 in
theorem map_piLeftUnsolvedOrder107810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder107810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder107810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder107810

end PiOrder107Map810

section PiOrder107Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder107810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder107810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder107810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder107810_eval

end PiOrder107Eval810
section PiOrder107Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1600000000 in
/-- Remaining power vanishing after the unsolved order-`106` residual is
peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the
shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder107810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) = h * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o105n ∧
        o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o106n ∧
        o106n.eval a +
            piLeftUnsolvedOrder107810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, hmix⟩ :=
    piLeftUnsolvedOrder106810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o105n +
          piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder106810_eval]
    exact hmix
  obtain ⟨o106n, ho106⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o105n +
        piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
      a hdegree hroot hsum0
  have h96 : h ^ 96 ≠ 0 := pow_ne_zero 96 hh
  have hquot :
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) +
        h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 16 := by
    apply mul_left_cancel₀ h96
    rw [← localClearedSixteenthDefect810_left_unsolved_factored]
    rw [hpower]
    ring
  have hcancel :
      o96n +
          piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
            b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 15 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
              b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
              w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho]
        ring
      _ = Polynomial.C eta * h ^ 16 := hquot
      _ = h * (Polynomial.C eta * h ^ 15) := by ring
  have hplus14 :
      o97n +
          piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 14 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho97]
        ring
      _ = o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedTail810_of_order97]
        ring
      _ = Polynomial.C eta * h ^ 15 := hcancel
      _ = h * (Polynomial.C eta * h ^ 14) := by ring
  have hplus13 :
      o98n +
          piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 13 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho98]
        ring
      _ = o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder97Plus810_of_order98]
        ring
      _ = Polynomial.C eta * h ^ 14 := hplus14
      _ = h * (Polynomial.C eta * h ^ 13) := by ring
  have hplus12 :
      o99n +
          piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 12 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho99]
        ring
      _ = o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder98Plus810_of_order99]
        ring
      _ = Polynomial.C eta * h ^ 13 := hplus13
      _ = h * (Polynomial.C eta * h ^ 12) := by ring
  have hplus11 :
      o100n +
          piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 11 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho100]
        ring
      _ = o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder99Plus810_of_order100]
        ring
      _ = Polynomial.C eta * h ^ 12 := hplus12
      _ = h * (Polynomial.C eta * h ^ 11) := by ring
  have hplus10 :
      o101n +
          piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 10 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho101]
        ring
      _ = o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder100Plus810_of_order101]
        ring
      _ = Polynomial.C eta * h ^ 11 := hplus11
      _ = h * (Polynomial.C eta * h ^ 10) := by ring
  have hplus9 :
      o102n +
          piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 9 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho102]
        ring
      _ = o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder101Plus810_of_order102]
        ring
      _ = Polynomial.C eta * h ^ 10 := hplus10
      _ = h * (Polynomial.C eta * h ^ 9) := by ring
  have hplus8 :
      o103n +
          piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 8 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho103]
        ring
      _ = o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder102Plus810_of_order103]
        ring
      _ = Polynomial.C eta * h ^ 9 := hplus9
      _ = h * (Polynomial.C eta * h ^ 8) := by ring
  have hplus7 :
      o104n +
          piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 7 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o104n +
            piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho104]
        ring
      _ = o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder103Plus810_of_order104]
        ring
      _ = Polynomial.C eta * h ^ 8 := hplus8
      _ = h * (Polynomial.C eta * h ^ 7) := by ring
  have hplus6 :
      o105n +
          piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 6 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o105n +
            piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho105]
        ring
      _ = o104n +
            piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder104Plus810_of_order105]
        ring
      _ = Polynomial.C eta * h ^ 7 := hplus7
      _ = h * (Polynomial.C eta * h ^ 6) := by ring
  have hplus5 :
      o106n +
          piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 5 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o106n +
            piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho106]
        ring
      _ = o105n +
            piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder105Plus810_of_order106]
        ring
      _ = Polynomial.C eta * h ^ 6 := hplus6
      _ = h * (Polynomial.C eta * h ^ 5) := by ring
  have htail :
      (piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder106Plus810_of_order107]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus5
  rw [← piLeftUnsolvedOrder107810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`107` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder107810_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (t0 v1 u1 s1 w1 b62 : k[X])
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (ht0 : p.coeff 7 = h0 ^ 6 * t0)
    (hv1 : p.coeff 6 = h0 ^ 4 * v1)
    (hu1 : p.coeff 5 = h0 ^ 2 * u1)
    (hs1 : q.coeff 8 = h0 ^ 6 * s1)
    (hw1 : q.coeff 7 = h0 ^ 4 * w1)
    (hb62 : q.coeff 6 = h0 ^ 2 * b62) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62 (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o105n ∧
        o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o106n ∧
        o106n.eval a +
            piLeftUnsolvedOrder107810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 := by
  obtain ⟨eta, heta⟩ :=
    sourcePiResidual810_eq_C_of_source p q H h0 j lambda hp hq hh0 hH
      hp8 hq10 hN hD
  have hNpeel :
      5 * (h0 ^ 6 * t0) * h0 ^ 2 - 4 * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    simpa only [ht0, hH] using hN
  have hpi :
      sourcePiResidual810
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * t0))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * v1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * u1))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 9))
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * s1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * w1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * b62))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))
          (RatFunc.C lambda) =
        algebraMap k (RatFunc k) eta := by
    simpa only [ht0, hv1, hu1, hs1, hw1, hb62] using heta
  have hpower :=
    piSourcePowerRelation810_of_residual_eq_C h0 (h0 ^ 6 * t0)
      (h0 ^ 4 * v1) (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 9) (h0 ^ 6 * s1)
      (h0 ^ 4 * w1) (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda eta hh0 hNpeel hpi
  exact piLeftUnsolvedOrder107810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`107` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order107Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n : k[X]),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
            (q.coeff 1) (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o105n ∧
        o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o106n ∧
        o106n.eval a +
            piLeftUnsolvedOrder107810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : k[X]),
              (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                    (5 : k[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : k[X]) * w1 - (160 : k[X]) * u1 -
                    (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : k) * lambda * t0.eval a = 0 ∧
                (4 : k) * tau1.eval a +
                    (9 : k) * lambda * (t0.eval a) ^ 2 +
                  (144 : k) * lambda * v1.eval a = 0) ∧
            (∃ g1 : k[X],
              (2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
                    (35 : k[X]) * t0 ^ 4 -
                    (240 : k[X]) * t0 ^ 2 * v1 +
                    (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : k) * g1.eval a +
                    (3 : k) * lambda *
                      ((7 : k) * (t0.eval a) ^ 3 -
                        (48 : k) * t0.eval a * v1.eval a -
                        (384 : k) * u1.eval a) = 0) ∧
            (∃ k1 : k[X],
              (81920 : k[X]) * (p.coeff 4) * t0 +
                    (131072 : k[X]) * (q.coeff 5) -
                    (98304 : k[X]) * b62 * t0 +
                    (2912 : k[X]) * t0 ^ 5 -
                    (20480 : k[X]) * t0 ^ 3 * v1 +
                    (46080 : k[X]) * t0 ^ 2 * u1 +
                    (30720 : k[X]) * t0 * v1 ^ 2 -
                    (40960 : k[X]) * u1 * v1 =
                  h0 * k1)) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            (40 : k) * (p.coeff 4).eval a - (32 : k) * b62.eval a +
              (5 : k) * (v1.eval a) ^ 2 = 0 ∧
            (16 : k) * (q.coeff 5).eval a =
              (5 : k) * u1.eval a * v1.eval a ∧
            ((u1.eval a = 0 ∧ o96n.eval a = 0 ∧
                (16 : k) * b62.eval a * v1.eval a =
                  (5 : k) * (v1.eval a) ^ 3) ∨
              ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a =
                  0 ∧
                (2 : k) * (u1.eval a) ^ 2 + (v1.eval a) ^ 3 =
                  0)))) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, hmix106, hsplit⟩ :=
    piFace810_linearRoot_order106Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n', o102n', o103n', o104n', o105n', o106n, ho', ho97', ho98', ho99', ho100', ho101', ho102', ho103', ho104', ho105', ho106, hmix107⟩ :=
    piLeftUnsolvedOrder107810_zero_of_source p q H h0 j lambda a t0 v1
      u1 s1 w1 b62 hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot ht0 ha6
      ha5 hb8 hb7 hb62
  have ho96eq : o96n = o96n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o96n = piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
          (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) (Polynomial.C lambda) := ho96.symm
      _ = h0 * o96n' := ho'
  subst ho96eq
  have ho97eq : o97n = o97n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o97n = o96n +
          piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho97.symm
      _ = h0 * o97n' := ho97'
  subst ho97eq
  have ho98eq : o98n = o98n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o98n = o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho98.symm
      _ = h0 * o98n' := ho98'
  subst ho98eq
  have ho99eq : o99n = o99n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o99n = o98n +
          piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho99.symm
      _ = h0 * o99n' := ho99'
  subst ho99eq
  have ho100eq : o100n = o100n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o100n = o99n +
          piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho100.symm
      _ = h0 * o100n' := ho100'
  subst ho100eq
  have ho101eq : o101n = o101n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o101n = o100n +
          piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho101.symm
      _ = h0 * o101n' := ho101'
  subst ho101eq
  have ho102eq : o102n = o102n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o102n = o101n +
          piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho102.symm
      _ = h0 * o102n' := ho102'
  subst ho102eq
  have ho103eq : o103n = o103n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o103n = o102n +
          piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho103.symm
      _ = h0 * o103n' := ho103'
  subst ho103eq
  have ho104eq : o104n = o104n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o104n = o103n +
          piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho104.symm
      _ = h0 * o104n' := ho104'
  subst ho104eq
  have ho105eq : o105n = o105n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o105n = o104n +
          piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho105.symm
      _ = h0 * o105n' := ho105'
  subst ho105eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, hmix107, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder106Plus810_of_order107
#print axioms piLeftUnsolvedOrder107810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder107810_zero_of_power
#print axioms piLeftUnsolvedOrder107810_zero_of_source
#print axioms piFace810_linearRoot_order107Chambers
#print axioms piLeftUnsolvedRightU1ZeroOrder107810_b62Law
#print axioms piLeftUnsolvedRightComplementOrder107810_u1rel

end PiOrder107Source810
section PiOrder108Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`108` mixin: the `h⁰` coefficient of the order-`107` Plus
remainder, equivalently the `h^11` coefficient of the unsolved tail
and the `h^12` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder108810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4398046511104 : R) * t0 * a2 * b1
    - (8796093022208 : R) * t0 * a1 * b2
    - (13194139533312 : R) * t0 * a0 * b3
    + (54975581388800 : R) * v1 * a2 * a0
    + (27487790694400 : R) * v1 * a1 ^ 2
    - (35184372088832 : R) * a2 * a0 * s1
    - (17592186044416 : R) * a1 ^ 2 * s1

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after `h` is removed from the order-`107` Plus
remainder. -/
def piLeftUnsolvedOrder108Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 3 * a0 ^ 2
    + (9895604649984 : R) * h ^ 2 * a1 * a0 * lambda
    + (5497558138880 : R) * h * t0 * a1 * a0
    + (17592186044416 : R) * h * a1 * b1
    + (35184372088832 : R) * h * a0 * b2
    - (12369505812480 : R) * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * t0 * a1 ^ 2 * lambda

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder107Plus810_of_order108
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder108Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder107Plus810, piLeftUnsolvedOrder108810,
    piLeftUnsolvedOrder108Plus810]
  ring

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder107Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder107Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder107Plus810_of_order108]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedTail810_of_order108
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 9 * piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 10 * piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 11 * piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 12 * piLeftUnsolvedOrder108Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order107, piLeftUnsolvedOrder107Plus810_of_order108]
  ring

/-- Order-`108` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder108810_t0u1Zero
    (v1 a2 a1 a0 s1 : R) : R :=
    (54975581388800 : R) * v1 * a2 * a0
    + (27487790694400 : R) * v1 * a1 ^ 2
    - (35184372088832 : R) * a2 * a0 * s1
    - (17592186044416 : R) * a1 ^ 2 * s1

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder108810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder108810_t0u1Zero v1 a2 a1 a0 s1 := by
  simp only [piLeftUnsolvedOrder108810,
    piLeftUnsolvedOrder108810_t0u1Zero, ht0, hu1]
  try ring

/-- Integer `1`-clearing of the LEFT order-`108` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder108810 (t0 v1 a2 a1 a0 b3 b2 b1 : R) : R :=
    - (5497558138880 : R) * t0 ^ 2 * a2 * a0
    - (2748779069440 : R) * t0 ^ 2 * a1 ^ 2
    - (4398046511104 : R) * t0 * a2 * b1
    - (8796093022208 : R) * t0 * a1 * b2
    - (13194139533312 : R) * t0 * a0 * b3
    + (10995116277760 : R) * v1 * a2 * a0
    + (5497558138880 : R) * v1 * a1 ^ 2

/-- Integer `1`-clearing of the RIGHT/`u1 = 0` order-`108`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder108810 (v1 a2 a1 a0 b62 : R) : R :=
    (10995116277760 : R) * v1 * a2 * a0
    + (5497558138880 : R) * v1 * a1 ^ 2

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedRightU1ZeroOrder108810_v1Zero
    (v1 a2 a1 a0 b62 : R) (hv1 : v1 = 0) :
    piLeftUnsolvedRightU1ZeroOrder108810 v1 a2 a1 a0 b62 = 0 := by
  simp only [piLeftUnsolvedRightU1ZeroOrder108810, hv1]
  try ring

/-- Cofactor of `16 b62 - 5 v1²` in the cleared RIGHT/`u1 = 0`
order-`108` mixin. -/
def piLeftUnsolvedRightU1ZeroOrder108B62Cofactor810
    (v1 a2 a1 a0 b62 : R) : R :=
    0

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `16 b62 = 5 v1²` specializes the RIGHT/`u1 = 0`
order-`108` mixin. -/
theorem piLeftUnsolvedRightU1ZeroOrder108810_b62Law
    (v1 a2 a1 a0 b62 : R) :
    (16 : R) * piLeftUnsolvedRightU1ZeroOrder108810 v1 a2 a1 a0 b62 =
      ((16 : R) * b62 - (5 : R) * v1 ^ 2) *
          piLeftUnsolvedRightU1ZeroOrder108B62Cofactor810
            v1 a2 a1 a0 b62 +
        (175921860444160 : R) * v1 * a2 * a0
        + (87960930222080 : R) * v1 * a1 ^ 2 := by
  simp only [piLeftUnsolvedRightU1ZeroOrder108810,
    piLeftUnsolvedRightU1ZeroOrder108B62Cofactor810]
  ring

/-- Frozen order-`108` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder108810
    (v1 a2 a1 a0 u1 : R) : R :=
    (10995116277760 : R) * v1 * a2 * a0
    + (5497558138880 : R) * v1 * a1 ^ 2

set_option maxHeartbeats 400000000 in
theorem piLeftUnsolvedRightComplementOrder108810_v1Zero
    (v1 a2 a1 a0 u1 : R) (hv1 : v1 = 0) :
    piLeftUnsolvedRightComplementOrder108810 v1 a2 a1 a0 u1 = 0 := by
  simp only [piLeftUnsolvedRightComplementOrder108810, hv1]
  try ring

/-- Cofactor of `2 u1² + v1³` in the cleared complement mixin. -/
def piLeftUnsolvedRightComplementOrder108U1Cofactor810
    (v1 a2 a1 a0 u1 : R) : R :=
    0

set_option maxHeartbeats 400000000 in
/-- Fifteenth-face extra `2 u1² + v1³ = 0` specializes the complement
order-`108` mixin. -/
theorem piLeftUnsolvedRightComplementOrder108810_u1rel
    (v1 a2 a1 a0 u1 : R) :
    (2 : R) * piLeftUnsolvedRightComplementOrder108810 v1 a2 a1 a0 u1 =
      ((2 : R) * u1 ^ 2 + v1 ^ 3) *
          piLeftUnsolvedRightComplementOrder108U1Cofactor810
            v1 a2 a1 a0 u1 +
        (21990232555520 : R) * v1 * a2 * a0
        + (10995116277760 : R) * v1 * a1 ^ 2 := by
  simp only [piLeftUnsolvedRightComplementOrder108810,
    piLeftUnsolvedRightComplementOrder108U1Cofactor810]
  ring

end PiOrder108Frozen810

section PiOrder108Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 1600000000 in
theorem map_piLeftUnsolvedOrder108810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder108810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder108810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder108810

end PiOrder108Map810

section PiOrder108Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder108810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder108810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder108810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder108810_eval

end PiOrder108Eval810
section PiOrder108Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1600000000 in
/-- Remaining power vanishing after the unsolved order-`107` residual is
peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the
shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder108810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) = h * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o105n ∧
        o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o106n ∧
        o106n +
            piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o107n ∧
        o107n.eval a +
            piLeftUnsolvedOrder108810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, hmix⟩ :=
    piLeftUnsolvedOrder107810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o106n +
          piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder107810_eval]
    exact hmix
  obtain ⟨o107n, ho107⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o106n +
        piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
      a hdegree hroot hsum0
  have h96 : h ^ 96 ≠ 0 := pow_ne_zero 96 hh
  have hquot :
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) +
        h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 16 := by
    apply mul_left_cancel₀ h96
    rw [← localClearedSixteenthDefect810_left_unsolved_factored]
    rw [hpower]
    ring
  have hcancel :
      o96n +
          piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
            b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 15 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
              b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
              w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho]
        ring
      _ = Polynomial.C eta * h ^ 16 := hquot
      _ = h * (Polynomial.C eta * h ^ 15) := by ring
  have hplus14 :
      o97n +
          piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 14 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho97]
        ring
      _ = o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedTail810_of_order97]
        ring
      _ = Polynomial.C eta * h ^ 15 := hcancel
      _ = h * (Polynomial.C eta * h ^ 14) := by ring
  have hplus13 :
      o98n +
          piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 13 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho98]
        ring
      _ = o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder97Plus810_of_order98]
        ring
      _ = Polynomial.C eta * h ^ 14 := hplus14
      _ = h * (Polynomial.C eta * h ^ 13) := by ring
  have hplus12 :
      o99n +
          piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 12 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho99]
        ring
      _ = o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder98Plus810_of_order99]
        ring
      _ = Polynomial.C eta * h ^ 13 := hplus13
      _ = h * (Polynomial.C eta * h ^ 12) := by ring
  have hplus11 :
      o100n +
          piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 11 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho100]
        ring
      _ = o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder99Plus810_of_order100]
        ring
      _ = Polynomial.C eta * h ^ 12 := hplus12
      _ = h * (Polynomial.C eta * h ^ 11) := by ring
  have hplus10 :
      o101n +
          piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 10 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho101]
        ring
      _ = o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder100Plus810_of_order101]
        ring
      _ = Polynomial.C eta * h ^ 11 := hplus11
      _ = h * (Polynomial.C eta * h ^ 10) := by ring
  have hplus9 :
      o102n +
          piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 9 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho102]
        ring
      _ = o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder101Plus810_of_order102]
        ring
      _ = Polynomial.C eta * h ^ 10 := hplus10
      _ = h * (Polynomial.C eta * h ^ 9) := by ring
  have hplus8 :
      o103n +
          piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 8 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho103]
        ring
      _ = o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder102Plus810_of_order103]
        ring
      _ = Polynomial.C eta * h ^ 9 := hplus9
      _ = h * (Polynomial.C eta * h ^ 8) := by ring
  have hplus7 :
      o104n +
          piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 7 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o104n +
            piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho104]
        ring
      _ = o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder103Plus810_of_order104]
        ring
      _ = Polynomial.C eta * h ^ 8 := hplus8
      _ = h * (Polynomial.C eta * h ^ 7) := by ring
  have hplus6 :
      o105n +
          piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 6 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o105n +
            piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho105]
        ring
      _ = o104n +
            piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder104Plus810_of_order105]
        ring
      _ = Polynomial.C eta * h ^ 7 := hplus7
      _ = h * (Polynomial.C eta * h ^ 6) := by ring
  have hplus5 :
      o106n +
          piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 5 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o106n +
            piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho106]
        ring
      _ = o105n +
            piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder105Plus810_of_order106]
        ring
      _ = Polynomial.C eta * h ^ 6 := hplus6
      _ = h * (Polynomial.C eta * h ^ 5) := by ring
  have hplus4 :
      o107n +
          piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 4 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o107n +
            piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o106n +
            piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho107]
        ring
      _ = o106n +
            piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder106Plus810_of_order107]
        ring
      _ = Polynomial.C eta * h ^ 5 := hplus5
      _ = h * (Polynomial.C eta * h ^ 4) := by ring
  have htail :
      (piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder107Plus810_of_order108]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus4
  rw [← piLeftUnsolvedOrder108810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`108` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder108810_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (t0 v1 u1 s1 w1 b62 : k[X])
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (ht0 : p.coeff 7 = h0 ^ 6 * t0)
    (hv1 : p.coeff 6 = h0 ^ 4 * v1)
    (hu1 : p.coeff 5 = h0 ^ 2 * u1)
    (hs1 : q.coeff 8 = h0 ^ 6 * s1)
    (hw1 : q.coeff 7 = h0 ^ 4 * w1)
    (hb62 : q.coeff 6 = h0 ^ 2 * b62) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62 (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o105n ∧
        o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o106n ∧
        o106n +
            piLeftUnsolvedOrder107810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o107n ∧
        o107n.eval a +
            piLeftUnsolvedOrder108810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 := by
  obtain ⟨eta, heta⟩ :=
    sourcePiResidual810_eq_C_of_source p q H h0 j lambda hp hq hh0 hH
      hp8 hq10 hN hD
  have hNpeel :
      5 * (h0 ^ 6 * t0) * h0 ^ 2 - 4 * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    simpa only [ht0, hH] using hN
  have hpi :
      sourcePiResidual810
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * t0))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * v1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * u1))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 9))
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * s1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * w1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * b62))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))
          (RatFunc.C lambda) =
        algebraMap k (RatFunc k) eta := by
    simpa only [ht0, hv1, hu1, hs1, hw1, hb62] using heta
  have hpower :=
    piSourcePowerRelation810_of_residual_eq_C h0 (h0 ^ 6 * t0)
      (h0 ^ 4 * v1) (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 9) (h0 ^ 6 * s1)
      (h0 ^ 4 * w1) (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda eta hh0 hNpeel hpi
  exact piLeftUnsolvedOrder108810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`108` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order108Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n : k[X]),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
            (q.coeff 1) (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o105n ∧
        o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o106n ∧
        o106n +
            piLeftUnsolvedOrder107810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o107n ∧
        o107n.eval a +
            piLeftUnsolvedOrder108810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : k[X]),
              (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                    (5 : k[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : k[X]) * w1 - (160 : k[X]) * u1 -
                    (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : k) * lambda * t0.eval a = 0 ∧
                (4 : k) * tau1.eval a +
                    (9 : k) * lambda * (t0.eval a) ^ 2 +
                  (144 : k) * lambda * v1.eval a = 0) ∧
            (∃ g1 : k[X],
              (2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
                    (35 : k[X]) * t0 ^ 4 -
                    (240 : k[X]) * t0 ^ 2 * v1 +
                    (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : k) * g1.eval a +
                    (3 : k) * lambda *
                      ((7 : k) * (t0.eval a) ^ 3 -
                        (48 : k) * t0.eval a * v1.eval a -
                        (384 : k) * u1.eval a) = 0) ∧
            (∃ k1 : k[X],
              (81920 : k[X]) * (p.coeff 4) * t0 +
                    (131072 : k[X]) * (q.coeff 5) -
                    (98304 : k[X]) * b62 * t0 +
                    (2912 : k[X]) * t0 ^ 5 -
                    (20480 : k[X]) * t0 ^ 3 * v1 +
                    (46080 : k[X]) * t0 ^ 2 * u1 +
                    (30720 : k[X]) * t0 * v1 ^ 2 -
                    (40960 : k[X]) * u1 * v1 =
                  h0 * k1)) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            (40 : k) * (p.coeff 4).eval a - (32 : k) * b62.eval a +
              (5 : k) * (v1.eval a) ^ 2 = 0 ∧
            (16 : k) * (q.coeff 5).eval a =
              (5 : k) * u1.eval a * v1.eval a ∧
            ((u1.eval a = 0 ∧ o96n.eval a = 0 ∧
                (16 : k) * b62.eval a * v1.eval a =
                  (5 : k) * (v1.eval a) ^ 3) ∨
              ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a =
                  0 ∧
                (2 : k) * (u1.eval a) ^ 2 + (v1.eval a) ^ 3 =
                  0)))) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, hmix107, hsplit⟩ :=
    piFace810_linearRoot_order107Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n', o102n', o103n', o104n', o105n', o106n', o107n, ho', ho97', ho98', ho99', ho100', ho101', ho102', ho103', ho104', ho105', ho106', ho107, hmix108⟩ :=
    piLeftUnsolvedOrder108810_zero_of_source p q H h0 j lambda a t0 v1
      u1 s1 w1 b62 hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot ht0 ha6
      ha5 hb8 hb7 hb62
  have ho96eq : o96n = o96n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o96n = piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
          (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) (Polynomial.C lambda) := ho96.symm
      _ = h0 * o96n' := ho'
  subst ho96eq
  have ho97eq : o97n = o97n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o97n = o96n +
          piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho97.symm
      _ = h0 * o97n' := ho97'
  subst ho97eq
  have ho98eq : o98n = o98n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o98n = o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho98.symm
      _ = h0 * o98n' := ho98'
  subst ho98eq
  have ho99eq : o99n = o99n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o99n = o98n +
          piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho99.symm
      _ = h0 * o99n' := ho99'
  subst ho99eq
  have ho100eq : o100n = o100n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o100n = o99n +
          piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho100.symm
      _ = h0 * o100n' := ho100'
  subst ho100eq
  have ho101eq : o101n = o101n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o101n = o100n +
          piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho101.symm
      _ = h0 * o101n' := ho101'
  subst ho101eq
  have ho102eq : o102n = o102n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o102n = o101n +
          piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho102.symm
      _ = h0 * o102n' := ho102'
  subst ho102eq
  have ho103eq : o103n = o103n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o103n = o102n +
          piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho103.symm
      _ = h0 * o103n' := ho103'
  subst ho103eq
  have ho104eq : o104n = o104n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o104n = o103n +
          piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho104.symm
      _ = h0 * o104n' := ho104'
  subst ho104eq
  have ho105eq : o105n = o105n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o105n = o104n +
          piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho105.symm
      _ = h0 * o105n' := ho105'
  subst ho105eq
  have ho106eq : o106n = o106n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o106n = o105n +
          piLeftUnsolvedOrder106810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho106.symm
      _ = h0 * o106n' := ho106'
  subst ho106eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, hmix108, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder107Plus810_of_order108
#print axioms piLeftUnsolvedOrder108810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder108810_zero_of_power
#print axioms piLeftUnsolvedOrder108810_zero_of_source
#print axioms piFace810_linearRoot_order108Chambers
#print axioms piLeftUnsolvedRightU1ZeroOrder108810_b62Law
#print axioms piLeftUnsolvedRightComplementOrder108810_u1rel

end PiOrder108Source810
section PiOrder109Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`109` mixin: the `h⁰` coefficient of the order-`108` Plus
remainder, equivalently the `h^12` coefficient of the unsolved tail
and the `h^13` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder109810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (12369505812480 : R) * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * t0 * a1 ^ 2 * lambda

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after `h` is removed from the order-`108` Plus
remainder. -/
def piLeftUnsolvedOrder109Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 2 * a0 ^ 2
    + (9895604649984 : R) * h * a1 * a0 * lambda
    + (5497558138880 : R) * t0 * a1 * a0
    + (17592186044416 : R) * a1 * b1
    + (35184372088832 : R) * a0 * b2

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder108Plus810_of_order109
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder108Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder108Plus810, piLeftUnsolvedOrder109810,
    piLeftUnsolvedOrder109Plus810]
  ring

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder108Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder108Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder108Plus810_of_order109]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedTail810_of_order109
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 9 * piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 10 * piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 11 * piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 12 * piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 13 * piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order108, piLeftUnsolvedOrder108Plus810_of_order109]
  ring

/-- Order-`109` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder109810_t0u1Zero
    (v1 : R) : R :=
    0

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder109810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder109810_t0u1Zero v1 := by
  simp only [piLeftUnsolvedOrder109810,
    piLeftUnsolvedOrder109810_t0u1Zero, ht0, hu1]
  try ring

/-- Integer `1`-clearing of the LEFT order-`109` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder109810 (t0 a2 a1 a0 lambda : R) : R :=
    - (12369505812480 : R) * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * t0 * a1 ^ 2 * lambda

/-- Integer `1`-clearing of the RIGHT/`u1 = 0` order-`109`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder109810 (v1 b62 : R) : R :=
    0

/-- Frozen order-`109` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder109810
    (v1 u1 : R) : R :=
    0

end PiOrder109Frozen810

section PiOrder109Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 1600000000 in
theorem map_piLeftUnsolvedOrder109810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder109810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder109810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder109810

end PiOrder109Map810

section PiOrder109Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder109810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder109810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder109810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder109810_eval

end PiOrder109Eval810
section PiOrder109Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1600000000 in
/-- Remaining power vanishing after the unsolved order-`108` residual is
peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the
shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder109810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) = h * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o105n ∧
        o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o106n ∧
        o106n +
            piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o107n ∧
        o107n +
            piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o108n ∧
        o108n.eval a +
            piLeftUnsolvedOrder109810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, hmix⟩ :=
    piLeftUnsolvedOrder108810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o107n +
          piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder108810_eval]
    exact hmix
  obtain ⟨o108n, ho108⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o107n +
        piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
      a hdegree hroot hsum0
  have h96 : h ^ 96 ≠ 0 := pow_ne_zero 96 hh
  have hquot :
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) +
        h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 16 := by
    apply mul_left_cancel₀ h96
    rw [← localClearedSixteenthDefect810_left_unsolved_factored]
    rw [hpower]
    ring
  have hcancel :
      o96n +
          piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
            b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 15 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
              b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
              w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho]
        ring
      _ = Polynomial.C eta * h ^ 16 := hquot
      _ = h * (Polynomial.C eta * h ^ 15) := by ring
  have hplus14 :
      o97n +
          piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 14 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho97]
        ring
      _ = o96n +
            piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedTail810_of_order97]
        ring
      _ = Polynomial.C eta * h ^ 15 := hcancel
      _ = h * (Polynomial.C eta * h ^ 14) := by ring
  have hplus13 :
      o98n +
          piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 13 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho98]
        ring
      _ = o97n +
            piLeftUnsolvedOrder97Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder97Plus810_of_order98]
        ring
      _ = Polynomial.C eta * h ^ 14 := hplus14
      _ = h * (Polynomial.C eta * h ^ 13) := by ring
  have hplus12 :
      o99n +
          piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 12 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho99]
        ring
      _ = o98n +
            piLeftUnsolvedOrder98Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder98Plus810_of_order99]
        ring
      _ = Polynomial.C eta * h ^ 13 := hplus13
      _ = h * (Polynomial.C eta * h ^ 12) := by ring
  have hplus11 :
      o100n +
          piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 11 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho100]
        ring
      _ = o99n +
            piLeftUnsolvedOrder99Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder99Plus810_of_order100]
        ring
      _ = Polynomial.C eta * h ^ 12 := hplus12
      _ = h * (Polynomial.C eta * h ^ 11) := by ring
  have hplus10 :
      o101n +
          piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 10 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho101]
        ring
      _ = o100n +
            piLeftUnsolvedOrder100Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder100Plus810_of_order101]
        ring
      _ = Polynomial.C eta * h ^ 11 := hplus11
      _ = h * (Polynomial.C eta * h ^ 10) := by ring
  have hplus9 :
      o102n +
          piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 9 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho102]
        ring
      _ = o101n +
            piLeftUnsolvedOrder101Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder101Plus810_of_order102]
        ring
      _ = Polynomial.C eta * h ^ 10 := hplus10
      _ = h * (Polynomial.C eta * h ^ 9) := by ring
  have hplus8 :
      o103n +
          piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 8 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho103]
        ring
      _ = o102n +
            piLeftUnsolvedOrder102Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder102Plus810_of_order103]
        ring
      _ = Polynomial.C eta * h ^ 9 := hplus9
      _ = h * (Polynomial.C eta * h ^ 8) := by ring
  have hplus7 :
      o104n +
          piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 7 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o104n +
            piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho104]
        ring
      _ = o103n +
            piLeftUnsolvedOrder103Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder103Plus810_of_order104]
        ring
      _ = Polynomial.C eta * h ^ 8 := hplus8
      _ = h * (Polynomial.C eta * h ^ 7) := by ring
  have hplus6 :
      o105n +
          piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 6 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o105n +
            piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho105]
        ring
      _ = o104n +
            piLeftUnsolvedOrder104Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder104Plus810_of_order105]
        ring
      _ = Polynomial.C eta * h ^ 7 := hplus7
      _ = h * (Polynomial.C eta * h ^ 6) := by ring
  have hplus5 :
      o106n +
          piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 5 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o106n +
            piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho106]
        ring
      _ = o105n +
            piLeftUnsolvedOrder105Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder105Plus810_of_order106]
        ring
      _ = Polynomial.C eta * h ^ 6 := hplus6
      _ = h * (Polynomial.C eta * h ^ 5) := by ring
  have hplus4 :
      o107n +
          piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 4 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o107n +
            piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o106n +
            piLeftUnsolvedOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho107]
        ring
      _ = o106n +
            piLeftUnsolvedOrder106Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder106Plus810_of_order107]
        ring
      _ = Polynomial.C eta * h ^ 5 := hplus5
      _ = h * (Polynomial.C eta * h ^ 4) := by ring
  have hplus3 :
      o108n +
          piLeftUnsolvedOrder108Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 3 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o108n +
            piLeftUnsolvedOrder108Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o107n +
            piLeftUnsolvedOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder108Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho108]
        ring
      _ = o107n +
            piLeftUnsolvedOrder107Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder107Plus810_of_order108]
        ring
      _ = Polynomial.C eta * h ^ 4 := hplus4
      _ = h * (Polynomial.C eta * h ^ 3) := by ring
  have htail :
      (piLeftUnsolvedOrder108Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder108Plus810_of_order109]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus3
  rw [← piLeftUnsolvedOrder109810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`109` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder109810_zero_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (t0 v1 u1 s1 w1 b62 : k[X])
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (ht0 : p.coeff 7 = h0 ^ 6 * t0)
    (hv1 : p.coeff 6 = h0 ^ 4 * v1)
    (hu1 : p.coeff 5 = h0 ^ 2 * u1)
    (hs1 : q.coeff 8 = h0 ^ 6 * s1)
    (hw1 : q.coeff 7 = h0 ^ 4 * w1)
    (hb62 : q.coeff 6 = h0 ^ 2 * b62) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62 (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o105n ∧
        o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o106n ∧
        o106n +
            piLeftUnsolvedOrder107810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o107n ∧
        o107n +
            piLeftUnsolvedOrder108810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o108n ∧
        o108n.eval a +
            piLeftUnsolvedOrder109810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 := by
  obtain ⟨eta, heta⟩ :=
    sourcePiResidual810_eq_C_of_source p q H h0 j lambda hp hq hh0 hH
      hp8 hq10 hN hD
  have hNpeel :
      5 * (h0 ^ 6 * t0) * h0 ^ 2 - 4 * q.coeff 9 =
        Polynomial.C lambda * h0 ^ 9 := by
    simpa only [ht0, hH] using hN
  have hpi :
      sourcePiResidual810
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * t0))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * v1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * u1))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 9))
          (algebraMap k[X] (RatFunc k) (h0 ^ 6 * s1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 4 * w1))
          (algebraMap k[X] (RatFunc k) (h0 ^ 2 * b62))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))
          (RatFunc.C lambda) =
        algebraMap k (RatFunc k) eta := by
    simpa only [ht0, hv1, hu1, hs1, hw1, hb62] using heta
  have hpower :=
    piSourcePowerRelation810_of_residual_eq_C h0 (h0 ^ 6 * t0)
      (h0 ^ 4 * v1) (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 9) (h0 ^ 6 * s1)
      (h0 ^ 4 * w1) (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda eta hh0 hNpeel hpi
  exact piLeftUnsolvedOrder109810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`109` chambers.  Witnesses stay unsolved.  The
fifteenth-face extras are carried from the parent.  This is not a
closure. -/
theorem piFace810_linearRoot_order109Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n : k[X]),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
            (q.coeff 1) (Polynomial.C lambda) = h0 * o96n ∧
        o96n +
            piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o97n ∧
        o97n +
            piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o98n ∧
        o98n +
            piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o99n ∧
        o99n +
            piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o100n ∧
        o100n +
            piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o101n ∧
        o101n +
            piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o102n ∧
        o102n +
            piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o103n ∧
        o103n +
            piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o104n ∧
        o104n +
            piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o105n ∧
        o105n +
            piLeftUnsolvedOrder106810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o106n ∧
        o106n +
            piLeftUnsolvedOrder107810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o107n ∧
        o107n +
            piLeftUnsolvedOrder108810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o108n ∧
        o108n.eval a +
            piLeftUnsolvedOrder109810 (t0.eval a) (v1.eval a)
              (u1.eval a) ((p.coeff 4).eval a) ((p.coeff 3).eval a)
              ((p.coeff 2).eval a) ((p.coeff 1).eval a)
              ((p.coeff 0).eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) ((q.coeff 5).eval a) ((q.coeff 4).eval a)
              ((q.coeff 3).eval a) ((q.coeff 2).eval a)
              ((q.coeff 1).eval a) lambda = 0 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : k[X]),
              (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                    (5 : k[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : k[X]) * w1 - (160 : k[X]) * u1 -
                    (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : k) * lambda * t0.eval a = 0 ∧
                (4 : k) * tau1.eval a +
                    (9 : k) * lambda * (t0.eval a) ^ 2 +
                  (144 : k) * lambda * v1.eval a = 0) ∧
            (∃ g1 : k[X],
              (2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
                    (35 : k[X]) * t0 ^ 4 -
                    (240 : k[X]) * t0 ^ 2 * v1 +
                    (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : k) * g1.eval a +
                    (3 : k) * lambda *
                      ((7 : k) * (t0.eval a) ^ 3 -
                        (48 : k) * t0.eval a * v1.eval a -
                        (384 : k) * u1.eval a) = 0) ∧
            (∃ k1 : k[X],
              (81920 : k[X]) * (p.coeff 4) * t0 +
                    (131072 : k[X]) * (q.coeff 5) -
                    (98304 : k[X]) * b62 * t0 +
                    (2912 : k[X]) * t0 ^ 5 -
                    (20480 : k[X]) * t0 ^ 3 * v1 +
                    (46080 : k[X]) * t0 ^ 2 * u1 +
                    (30720 : k[X]) * t0 * v1 ^ 2 -
                    (40960 : k[X]) * u1 * v1 =
                  h0 * k1)) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            (40 : k) * (p.coeff 4).eval a - (32 : k) * b62.eval a +
              (5 : k) * (v1.eval a) ^ 2 = 0 ∧
            (16 : k) * (q.coeff 5).eval a =
              (5 : k) * u1.eval a * v1.eval a ∧
            ((u1.eval a = 0 ∧ o96n.eval a = 0 ∧
                (16 : k) * b62.eval a * v1.eval a =
                  (5 : k) * (v1.eval a) ^ 3) ∨
              ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a =
                  0 ∧
                (2 : k) * (u1.eval a) ^ 2 + (v1.eval a) ^ 3 =
                  0)))) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, hmix108, hsplit⟩ :=
    piFace810_linearRoot_order108Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n', o102n', o103n', o104n', o105n', o106n', o107n', o108n, ho', ho97', ho98', ho99', ho100', ho101', ho102', ho103', ho104', ho105', ho106', ho107', ho108, hmix109⟩ :=
    piLeftUnsolvedOrder109810_zero_of_source p q H h0 j lambda a t0 v1
      u1 s1 w1 b62 hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot ht0 ha6
      ha5 hb8 hb7 hb62
  have ho96eq : o96n = o96n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o96n = piLeftUnsolvedHead810 t0 v1 u1 (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
          (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) (Polynomial.C lambda) := ho96.symm
      _ = h0 * o96n' := ho'
  subst ho96eq
  have ho97eq : o97n = o97n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o97n = o96n +
          piLeftUnsolvedOrder97810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho97.symm
      _ = h0 * o97n' := ho97'
  subst ho97eq
  have ho98eq : o98n = o98n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o98n = o97n +
          piLeftUnsolvedOrder98810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho98.symm
      _ = h0 * o98n' := ho98'
  subst ho98eq
  have ho99eq : o99n = o99n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o99n = o98n +
          piLeftUnsolvedOrder99810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho99.symm
      _ = h0 * o99n' := ho99'
  subst ho99eq
  have ho100eq : o100n = o100n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o100n = o99n +
          piLeftUnsolvedOrder100810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho100.symm
      _ = h0 * o100n' := ho100'
  subst ho100eq
  have ho101eq : o101n = o101n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o101n = o100n +
          piLeftUnsolvedOrder101810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho101.symm
      _ = h0 * o101n' := ho101'
  subst ho101eq
  have ho102eq : o102n = o102n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o102n = o101n +
          piLeftUnsolvedOrder102810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho102.symm
      _ = h0 * o102n' := ho102'
  subst ho102eq
  have ho103eq : o103n = o103n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o103n = o102n +
          piLeftUnsolvedOrder103810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho103.symm
      _ = h0 * o103n' := ho103'
  subst ho103eq
  have ho104eq : o104n = o104n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o104n = o103n +
          piLeftUnsolvedOrder104810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho104.symm
      _ = h0 * o104n' := ho104'
  subst ho104eq
  have ho105eq : o105n = o105n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o105n = o104n +
          piLeftUnsolvedOrder105810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho105.symm
      _ = h0 * o105n' := ho105'
  subst ho105eq
  have ho106eq : o106n = o106n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o106n = o105n +
          piLeftUnsolvedOrder106810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho106.symm
      _ = h0 * o106n' := ho106'
  subst ho106eq
  have ho107eq : o107n = o107n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o107n = o106n +
          piLeftUnsolvedOrder107810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho107.symm
      _ = h0 * o107n' := ho107'
  subst ho107eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, hmix109, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder108Plus810_of_order109
#print axioms piLeftUnsolvedOrder109810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder109810_zero_of_power
#print axioms piLeftUnsolvedOrder109810_zero_of_source
#print axioms piFace810_linearRoot_order109Chambers

end PiOrder109Source810

end Max11DegreeRoutes
