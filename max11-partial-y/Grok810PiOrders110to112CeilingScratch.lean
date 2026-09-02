import Grok810PiOrders105to109Scratch

/-! # Orders `110`–`112` and the ceiling of the `(8,10)` degree-one `π` tower

`Grok810PiOrders105to109Scratch` leaves three live chambers after the
unsolved order-`109` coefficient is extracted:

* LEFT: `o108n(a) + Order109(a) = 0` with the frozen mixin and unsolved
  witnesses `m1, τ1, g1, k1`;
* RIGHT/`u1 = 0`: the fifteenth-face extra `16 b62 v1 = 5 v1³` mixed
  with the next coefficient;
* RIGHT complement: the extra `2 u1² + v1³ = 0` on `5 v1² = 8 b62`.

This file continues the unsolved tail through orders `110`, `111`, and
the CEILING order `112`.  Each order `k ∈ {110, 111}` is the `h⁰`
coefficient of the previous Plus remainder, equivalently the
`h^(k-97)` coefficient of the unsolved tail and the `h^(k-96)`
coefficient of the factored residual after the order-`96` head.  The
four scalar load solves are not inserted as polynomial identities.
Witnesses `m1, τ1, g1, k1` stay unsolved.

Order `112` is the last frozen head: the order-`111` Plus remainder is
independent of `h`, and the order-`112` Plus factor is the zero
polynomial.  The weight-`112` source power relation
`A₀ = C(2⁴⁴ η) · h¹¹²` then identifies the remaining factor
`o111n + Order112` with `C(η)`.  Cancelling the source clearing powers
shows that this remaining factor *is* a polynomial (a scalar multiple
of the depressed `π` residual).  A polynomial cannot have derivative
`C(j)/h₀` with `j ≠ 0`; that holomorphic ceiling is recorded after the
pattern of `Grok610PoleCeilingLemmaScratch` /
`Grok610DegreeZeroOrder75CeilingScratch`.

The last three mixins involve only `t0, a0, a1, b1, b2, λ`.  They do
not mention `m1, τ1, g1, k1`, so those LEFT witnesses are not pinned
by exhaustion.  RIGHT/`u1 = 0` and the complement likewise keep their
fifteenth-face extras; the new mixins constrain `(a0, a1, b1, b2)`
and do not force a chamber-level False.

**No chamber is closed.**  The joint packet
`piFace810_linearRoot_order112Chambers` records the exhausted
divisibilities, the holomorphic remainder, and the same three live
chambers.  There is no unused compact-numerator order after `112`.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 1600000000
set_option linter.unusedVariables false

section PiOrder110Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`110` mixin: the `h⁰` coefficient of the order-`109` Plus
remainder, equivalently the `h^13` coefficient of the unsolved tail
and the `h^14` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder110810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5497558138880 : R) * t0 * a1 * a0
    + (17592186044416 : R) * a1 * b1
    + (35184372088832 : R) * a0 * b2

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after `h` is removed from the order-`109` Plus remainder. -/
def piLeftUnsolvedOrder110Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h * a0 ^ 2
    + (9895604649984 : R) * a1 * a0 * lambda

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder109Plus810_of_order110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder109Plus810, piLeftUnsolvedOrder110810,
    piLeftUnsolvedOrder110Plus810]
  ring

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder109Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder109Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder109Plus810_of_order110]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedTail810_of_order110
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
        h ^ 13 * piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 14 * piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order109, piLeftUnsolvedOrder109Plus810_of_order110]
  ring

/-- Order-`110` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder110810_t0u1Zero
    (a1 a0 b2 b1 : R) : R :=
    (17592186044416 : R) * a1 * b1
    + (35184372088832 : R) * a0 * b2

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder110810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder110810_t0u1Zero a1 a0 b2 b1 := by
  simp only [piLeftUnsolvedOrder110810,
    piLeftUnsolvedOrder110810_t0u1Zero, ht0, hu1]
  try ring

/-- Integer `1`-clearing of the LEFT order-`110` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder110810 (t0 a1 a0 b2 b1 : R) : R :=
    (5497558138880 : R) * t0 * a1 * a0
    + (17592186044416 : R) * a1 * b1
    + (35184372088832 : R) * a0 * b2

/-- Integer `1`-clearing of the RIGHT/`u1 = 0` order-`110`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder110810 (a1 a0 b2 b1 : R) : R :=
    (17592186044416 : R) * a1 * b1
    + (35184372088832 : R) * a0 * b2

/-- Frozen order-`110` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder110810
    (a1 a0 b2 b1 : R) : R :=
    (17592186044416 : R) * a1 * b1
    + (35184372088832 : R) * a0 * b2

end PiOrder110Frozen810

section PiOrder110Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 1600000000 in
theorem map_piLeftUnsolvedOrder110810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder110810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder110810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder110810

end PiOrder110Map810

section PiOrder110Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder110810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder110810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder110810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder110810_eval

end PiOrder110Eval810
section PiOrder110Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1600000000 in
/-- Remaining power vanishing after the unsolved order-`109` residual is peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder110810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n o109n : k[X]),
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
        o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o109n ∧
        o109n.eval a +
            piLeftUnsolvedOrder110810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, hmix⟩ :=
    piLeftUnsolvedOrder109810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o108n +
          piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder109810_eval]
    exact hmix
  obtain ⟨o109n, ho109⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o108n +
        piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
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
  have hplus2 :
      o109n +
          piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 2 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o109n +
            piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho109]
        ring
      _ = o108n +
            piLeftUnsolvedOrder108Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder108Plus810_of_order109]
        ring
      _ = Polynomial.C eta * h ^ 3 := hplus3
      _ = h * (Polynomial.C eta * h ^ 2) := by ring
  have htail :
      (piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder109Plus810_of_order110]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus2
  rw [← piLeftUnsolvedOrder110810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`110` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder110810_zero_of_source
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
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n o109n : k[X]),
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
        o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o109n ∧
        o109n.eval a +
            piLeftUnsolvedOrder110810 (t0.eval a) (v1.eval a)
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
  exact piLeftUnsolvedOrder110810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`110` chambers.  Witnesses stay unsolved.  The fifteenth-face extras are carried from the parent.  This is not a closure. -/
theorem piFace810_linearRoot_order110Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n o109n : k[X]),
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
        o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o109n ∧
        o109n.eval a +
            piLeftUnsolvedOrder110810 (t0.eval a) (v1.eval a)
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
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, hmix109, hsplit⟩ :=
    piFace810_linearRoot_order109Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n', o102n', o103n', o104n', o105n', o106n', o107n', o108n', o109n, ho', ho97', ho98', ho99', ho100', ho101', ho102', ho103', ho104', ho105', ho106', ho107', ho108', ho109, hmix110⟩ :=
    piLeftUnsolvedOrder110810_zero_of_source p q H h0 j lambda a t0 v1
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
  have ho108eq : o108n = o108n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o108n = o107n +
          piLeftUnsolvedOrder108810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho108.symm
      _ = h0 * o108n' := ho108'
  subst ho108eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, hmix110, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder109Plus810_of_order110
#print axioms piLeftUnsolvedOrder110810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder110810_zero_of_power
#print axioms piLeftUnsolvedOrder110810_zero_of_source
#print axioms piFace810_linearRoot_order110Chambers

end PiOrder110Source810
section PiOrder111Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`111` mixin: the `h⁰` coefficient of the order-`110` Plus
remainder, equivalently the `h^14` coefficient of the unsolved tail
and the `h^15` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder111810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (9895604649984 : R) * a1 * a0 * lambda

set_option maxHeartbeats 1600000000 in
/-- Remaining factor after `h` is removed from the order-`110` Plus remainder. -/
def piLeftUnsolvedOrder111Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * a0 ^ 2

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder110Plus810_of_order111
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder111Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder110Plus810, piLeftUnsolvedOrder111810,
    piLeftUnsolvedOrder111Plus810]
  ring

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder110Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder110Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder110Plus810_of_order111]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedTail810_of_order111
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
        h ^ 13 * piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 14 * piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 15 * piLeftUnsolvedOrder111Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order110, piLeftUnsolvedOrder110Plus810_of_order111]
  ring

/-- Order-`111` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder111810_t0u1Zero
    (a1 a0 lambda : R) : R :=
    (9895604649984 : R) * a1 * a0 * lambda

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder111810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder111810_t0u1Zero a1 a0 lambda := by
  simp only [piLeftUnsolvedOrder111810,
    piLeftUnsolvedOrder111810_t0u1Zero, ht0, hu1]
  try ring

/-- Integer `1`-clearing of the LEFT order-`111` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder111810 (a1 a0 lambda : R) : R :=
    (9895604649984 : R) * a1 * a0 * lambda

/-- Integer `1`-clearing of the RIGHT/`u1 = 0` order-`111`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder111810 (a1 a0 lambda : R) : R :=
    (9895604649984 : R) * a1 * a0 * lambda

/-- Frozen order-`111` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder111810
    (a1 a0 lambda : R) : R :=
    (9895604649984 : R) * a1 * a0 * lambda

end PiOrder111Frozen810

section PiOrder111Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 1600000000 in
theorem map_piLeftUnsolvedOrder111810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder111810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder111810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder111810

end PiOrder111Map810

section PiOrder111Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder111810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder111810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder111810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder111810_eval

end PiOrder111Eval810
section PiOrder111Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1600000000 in
/-- Remaining power vanishing after the unsolved order-`110` residual is peeled.  Witnesses stay unsolved.  The `h0`-divisibilities are the shape the ceiling lemma consumes. -/
theorem piLeftUnsolvedOrder111810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n o109n o110n : k[X]),
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
        o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o109n ∧
        o109n +
            piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o110n ∧
        o110n.eval a +
            piLeftUnsolvedOrder111810 (t0.eval a) (v1.eval a)
              (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a)
              (a1.eval a) (a0.eval a) (s1.eval a) (w1.eval a)
              (b62.eval a) (b5.eval a) (b4.eval a) (b3.eval a)
              (b2.eval a) (b1.eval a) lambda = 0 := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, hmix⟩ :=
    piLeftUnsolvedOrder110810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o109n +
          piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder110810_eval]
    exact hmix
  obtain ⟨o110n, ho110⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o109n +
        piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
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
  have hplus2 :
      o109n +
          piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 2 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o109n +
            piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho109]
        ring
      _ = o108n +
            piLeftUnsolvedOrder108Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder108Plus810_of_order109]
        ring
      _ = Polynomial.C eta * h ^ 3 := hplus3
      _ = h * (Polynomial.C eta * h ^ 2) := by ring
  have hplus1 :
      o110n +
          piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 1 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o110n +
            piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o109n +
            piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho110]
        ring
      _ = o109n +
            piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder109Plus810_of_order110]
        ring
      _ = Polynomial.C eta * h ^ 2 := hplus2
      _ = h * (Polynomial.C eta * h ^ 1) := by ring
  have htail :
      (piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
        (piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a := by
    rw [piLeftUnsolvedOrder110Plus810_of_order111]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hroot,
      zero_mul, add_zero]
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, o110n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, ho110, ?_⟩
  have hev := congrArg (Polynomial.eval a) hplus1
  rw [← piLeftUnsolvedOrder111810_eval, ← htail]
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`111` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder111810_zero_of_source
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
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n o109n o110n : k[X]),
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
        o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o109n ∧
        o109n +
            piLeftUnsolvedOrder110810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o110n ∧
        o110n.eval a +
            piLeftUnsolvedOrder111810 (t0.eval a) (v1.eval a)
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
  exact piLeftUnsolvedOrder111810_zero_of_power h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda (17592186044416 * eta) a hh0 hdegree hroot hpower

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`111` chambers.  Witnesses stay unsolved.  The fifteenth-face extras are carried from the parent.  This is not a closure. -/
theorem piFace810_linearRoot_order111Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n o109n o110n : k[X]),
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
        o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o109n ∧
        o109n +
            piLeftUnsolvedOrder110810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o110n ∧
        o110n.eval a +
            piLeftUnsolvedOrder111810 (t0.eval a) (v1.eval a)
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
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, hmix110, hsplit⟩ :=
    piFace810_linearRoot_order110Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n', o102n', o103n', o104n', o105n', o106n', o107n', o108n', o109n', o110n, ho', ho97', ho98', ho99', ho100', ho101', ho102', ho103', ho104', ho105', ho106', ho107', ho108', ho109', ho110, hmix111⟩ :=
    piLeftUnsolvedOrder111810_zero_of_source p q H h0 j lambda a t0 v1
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
  have ho108eq : o108n = o108n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o108n = o107n +
          piLeftUnsolvedOrder108810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho108.symm
      _ = h0 * o108n' := ho108'
  subst ho108eq
  have ho109eq : o109n = o109n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o109n = o108n +
          piLeftUnsolvedOrder109810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho109.symm
      _ = h0 * o109n' := ho109'
  subst ho109eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, o110n,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, ho110, hmix111, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder110Plus810_of_order111
#print axioms piLeftUnsolvedOrder111810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder111810_zero_of_power
#print axioms piLeftUnsolvedOrder111810_zero_of_source
#print axioms piFace810_linearRoot_order111Chambers

end PiOrder111Source810
section PiOrder112Frozen810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Frozen order-`112` mixin: the `h⁰` coefficient of the order-`111` Plus
remainder, equivalently the `h^15` coefficient of the unsolved tail
and the `h^16` coefficient of the factored residual after the
order-`96` head. -/
def piLeftUnsolvedOrder112810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * a0 ^ 2

set_option maxHeartbeats 1600000000 in
/-- Identically zero: the unsolved tail has `h`-degree `15`, so order `112` is the last frozen head. -/
def piLeftUnsolvedOrder112Plus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder111Plus810_of_order112
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder111Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedOrder112Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [piLeftUnsolvedOrder111Plus810, piLeftUnsolvedOrder112810,
    piLeftUnsolvedOrder112Plus810]
  ring

set_option maxHeartbeats 800000000 in
theorem piLeftUnsolvedOrder111Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder111Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedOrder111Plus810_of_order112]
  simp only [zero_mul, add_zero]

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedTail810_of_order112
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
        h ^ 13 * piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 14 * piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 15 * piLeftUnsolvedOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 16 * piLeftUnsolvedOrder112Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  rw [piLeftUnsolvedTail810_of_order111, piLeftUnsolvedOrder111Plus810_of_order112]
  ring

/-- Order-`112` mixin on `t0 = u1 = 0`. -/
def piLeftUnsolvedOrder112810_t0u1Zero
    (a0 : R) : R :=
    - (21990232555520 : R) * a0 ^ 2

set_option maxHeartbeats 1600000000 in
theorem piLeftUnsolvedOrder112810_of_t0u1Zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) (ht0 : t0 = 0) (hu1 : u1 = 0) :
    piLeftUnsolvedOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      piLeftUnsolvedOrder112810_t0u1Zero a0 := by
  simp only [piLeftUnsolvedOrder112810,
    piLeftUnsolvedOrder112810_t0u1Zero, ht0, hu1]
  try ring

/-- Integer `1`-clearing of the LEFT order-`112` mixin after
the four scalar relations.  Witnesses `m1, τ1, g1, k1` are not
inserted. -/
def piLeftUnsolvedLeftOrder112810 (a0 : R) : R :=
    - (21990232555520 : R) * a0 ^ 2

/-- Integer `1`-clearing of the RIGHT/`u1 = 0` order-`112`
mixin after the four scalar relations. -/
def piLeftUnsolvedRightU1ZeroOrder112810 (a0 : R) : R :=
    - (21990232555520 : R) * a0 ^ 2

/-- Frozen order-`112` mixin on the RIGHT complement scalar locus. -/
def piLeftUnsolvedRightComplementOrder112810
    (a0 : R) : R :=
    - (21990232555520 : R) * a0 ^ 2

end PiOrder112Frozen810

section PiOrder112Map810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 1600000000 in
theorem map_piLeftUnsolvedOrder112810 (phi : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (piLeftUnsolvedOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      piLeftUnsolvedOrder112810 (phi t0) (phi v1) (phi u1) (phi a4)
        (phi a3) (phi a2) (phi a1) (phi a0) (phi s1) (phi w1)
        (phi b62) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [piLeftUnsolvedOrder112810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

#print axioms map_piLeftUnsolvedOrder112810

end PiOrder112Map810

section PiOrder112Eval810

variable {k : Type*} [CommRing k]

theorem piLeftUnsolvedOrder112810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (piLeftUnsolvedOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      piLeftUnsolvedOrder112810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_piLeftUnsolvedOrder112810 (Polynomial.evalRingHom a) t0 v1 u1 a4
      a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms piLeftUnsolvedOrder112810_eval

end PiOrder112Eval810
section PiOrder112Source810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1600000000 in
/-- Holomorphic remainder after the unsolved order-`111` residual is peeled.  The remaining power is `h⁰`, so `o111n + Order112` equals `C(η)` as polynomials.  Witnesses stay unsolved. -/
theorem piLeftUnsolvedOrder112810_zero_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n o109n o110n o111n : k[X]),
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
        o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o109n ∧
        o109n +
            piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o110n ∧
        o110n +
            piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          h * o111n ∧
        o111n +
            piLeftUnsolvedOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          Polynomial.C eta := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, o110n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, ho110, hmix⟩ :=
    piLeftUnsolvedOrder111810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0 s1
      w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  have hsum0 :
      (o110n +
          piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
    rw [Polynomial.eval_add, piLeftUnsolvedOrder111810_eval]
    exact hmix
  obtain ⟨o111n, ho111⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h
      (o110n +
        piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
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
  have hplus2 :
      o109n +
          piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 2 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o109n +
            piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho109]
        ring
      _ = o108n +
            piLeftUnsolvedOrder108Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder108Plus810_of_order109]
        ring
      _ = Polynomial.C eta * h ^ 3 := hplus3
      _ = h * (Polynomial.C eta * h ^ 2) := by ring
  have hplus1 :
      o110n +
          piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 1 := by
    apply mul_left_cancel₀ hh
    calc
      h * (o110n +
            piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o109n +
            piLeftUnsolvedOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho110]
        ring
      _ = o109n +
            piLeftUnsolvedOrder109Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder109Plus810_of_order110]
        ring
      _ = Polynomial.C eta * h ^ 2 := hplus2
      _ = h * (Polynomial.C eta * h ^ 1) := by ring
  have hplus0 :
      o111n +
          piLeftUnsolvedOrder111Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta := by
    apply mul_left_cancel₀ hh
    calc
      h * (o111n +
            piLeftUnsolvedOrder111Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
          o110n +
            piLeftUnsolvedOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) +
            h * piLeftUnsolvedOrder111Plus810 h t0 v1 u1 a4 a3 a2 a1
              a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [ho111]
        ring
      _ = o110n +
            piLeftUnsolvedOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0
              s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
        rw [piLeftUnsolvedOrder110Plus810_of_order111]
        ring
      _ = Polynomial.C eta * h ^ 1 := hplus1
      _ = h * Polynomial.C eta := by ring
  have hhol :
      o111n +
          piLeftUnsolvedOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta := by
    have hplus := hplus0
    rw [piLeftUnsolvedOrder111Plus810_of_order112] at hplus
    simpa [piLeftUnsolvedOrder112Plus810, mul_zero, add_zero] using hplus
  refine ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, o110n, o111n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, ho110, ho111, hhol⟩

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`112` peel from a literal `(8,10)` source. -/
theorem piLeftUnsolvedOrder112810_zero_of_source
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
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n o109n o110n o111n : k[X]) (eta : k),
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
        o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o109n ∧
        o109n +
            piLeftUnsolvedOrder110810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o110n ∧
        o110n +
            piLeftUnsolvedOrder111810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o111n ∧
        o111n +
            piLeftUnsolvedOrder112810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C (17592186044416 * eta) := by
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
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, o110n, o111n, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, ho110, ho111, hhol⟩ :=
    piLeftUnsolvedOrder112810_zero_of_power h0 t0 v1 u1
      (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
      b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
      lambda (17592186044416 * eta) a hh0 hdegree hroot hpower
  exact ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, o110n, o111n, eta, ho, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, ho110, ho111, hhol⟩

set_option maxHeartbeats 1600000000 in
/-- Source-facing order-`112` chambers after the last frozen head.  The remaining factor is `C(2⁴⁴ η)`.  Witnesses `m1, τ1, g1, k1` stay unsolved and are not pinned by orders `110`–`112`.  This is not a closure. -/
theorem piFace810_linearRoot_order112Chambers
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n o107n o108n o109n o110n o111n : k[X]) (eta : k),
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
        o108n +
            piLeftUnsolvedOrder109810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o109n ∧
        o109n +
            piLeftUnsolvedOrder110810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o110n ∧
        o110n +
            piLeftUnsolvedOrder111810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          h0 * o111n ∧
        o111n +
            piLeftUnsolvedOrder112810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C (17592186044416 * eta) ∧
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
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, o110n, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, ho110, hmix111, hsplit⟩ :=
    piFace810_linearRoot_order111Chambers p q H h0 j lambda a hp hq
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
  obtain ⟨o96n', o97n', o98n', o99n', o100n', o101n', o102n', o103n', o104n', o105n', o106n', o107n', o108n', o109n', o110n', o111n, eta, ho', ho97', ho98', ho99', ho100', ho101', ho102', ho103', ho104', ho105', ho106', ho107', ho108', ho109', ho110', ho111, hhol⟩ :=
    piLeftUnsolvedOrder112810_zero_of_source p q H h0 j lambda a t0 v1
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
  have ho108eq : o108n = o108n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o108n = o107n +
          piLeftUnsolvedOrder108810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho108.symm
      _ = h0 * o108n' := ho108'
  subst ho108eq
  have ho109eq : o109n = o109n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o109n = o108n +
          piLeftUnsolvedOrder109810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho109.symm
      _ = h0 * o109n' := ho109'
  subst ho109eq
  have ho110eq : o110n = o110n' := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * o110n = o109n +
          piLeftUnsolvedOrder110810 t0 v1 u1 (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1 b62
              (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) := ho110.symm
      _ = h0 * o110n' := ho110'
  subst ho110eq
  refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n, o105n, o106n, o107n, o108n, o109n, o110n, o111n, eta,
    ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, ho96, ho97, ho98, ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107, ho108, ho109, ho110, ho111, hhol, ?_⟩
  exact hsplit

#print axioms piLeftUnsolvedOrder111Plus810_of_order112
#print axioms piLeftUnsolvedOrder112810_of_t0u1Zero
#print axioms piLeftUnsolvedOrder112810_zero_of_power
#print axioms piLeftUnsolvedOrder112810_zero_of_source
#print axioms piFace810_linearRoot_order112Chambers

end PiOrder112Source810

section PiPoleCeiling810

variable {k : Type*} [Field k] [CharZero k]

/-- Cancel `n` polynomial powers from a source clearing
`algebraMap (h0^n * Q) = hRF^n * rho`. -/
theorem algebraMap_cancel_pow_of_piClearing810
    (h0 Q : k[X]) (rho : RatFunc k) (n : ℕ) (hh0 : h0 ≠ 0)
    (hquot :
      algebraMap k[X] (RatFunc k) (h0 ^ n * Q) =
        (algebraMap k[X] (RatFunc k) h0) ^ n * rho) :
    algebraMap k[X] (RatFunc k) Q = rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero n hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ n * Q) =
        hRF ^ n * algebraMap k[X] (RatFunc k) Q := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ n * algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) (h0 ^ n * Q) := hmapPow.symm
    _ = hRF ^ n * rho := hquot

/-- A rational function that is the image of a polynomial cannot have
derivative `C j / h0` with `j ≠ 0`: evaluating `h0 * (remaining)' = C j`
at the simple root forces `j = 0`.  Adapted from
`localLinearPoleZero_C_eq_zero_of_deriv_eq_simplePole610`. -/
theorem piCeiling_C_eq_zero_of_deriv_eq_simplePole810
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 = rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 := by
  have hhRF : algebraMap k[X] (RatFunc k) h0 ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh0
  have hderivA :
      algebraMap k[X] (RatFunc k) (derivative A0) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hderiv, ← hclear, GCD369RatFuncDerivative]
  have hpoly : h0 * derivative A0 = Polynomial.C j := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    rw [map_mul, hderivA, mul_div_cancel₀ _ hhRF]
    simp only [RatFunc.algebraMap_C]
  have heval := congrArg (fun p : k[X] ↦ p.eval a) hpoly
  have heval' : (0 : k) = j := by
    simpa [hroot, Polynomial.eval_mul, Polynomial.eval_C] using heval
  exact heval'.symm

/-- Cancel-and-expose: if `h0^n` divides the cleared numerator, the
remaining factor *is* `rho`, so the simple-pole equation forces `j = 0`. -/
theorem piCeiling_of_pow_dvd_simplePole_eval810
    (a j : k) (h0 A0 Q : k[X]) (rho : RatFunc k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0) (hA : A0 = h0 ^ n * Q)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 :=
  piCeiling_C_eq_zero_of_deriv_eq_simplePole810 a j h0 Q rho hh0 hroot
    (algebraMap_cancel_pow_of_piClearing810 h0 Q rho n hh0
      (by simpa [hA] using hclear))
    hderiv

/-- Same holomorphic remainder, with `j ≠ 0`, is False. -/
theorem piCeiling_of_pow_dvd_simplePole_ne_zero810
    (a j : k) (h0 A0 Q : k[X]) (rho : RatFunc k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0) (hA : A0 = h0 ^ n * Q)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False :=
  hj (piCeiling_of_pow_dvd_simplePole_eval810 a j h0 A0 Q rho n hh0
    hroot hA hclear hderiv)

/-- Weight-`112` source clearing: `A0 = C(2⁴⁴ η) · h0^112`.  Cancelling
those powers exposes a polynomial remaining factor.  If that remaining
factor *were* a rational function with derivative `C j / h0` and
`j ≠ 0`, this would be False.  The depressed `π` residual itself has
derivative `0` on a literal source, so this lemma is the holomorphic
ceiling interface and does not by itself close `piFace810_linearRoot`. -/
theorem localClearedSixteenthDefect810_pow_112_dvd_contradicts_simplePole
    (h0 a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (lambda eta j a : k) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hroot : h0.eval a = 0)
    (hA :
      localClearedSixteenthDefect810 h0 a7 a6 a5 a4 a3 a2 a1 a0 b8 b7
          b6 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C (17592186044416 * eta) * h0 ^ 112)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedSixteenthDefect810 h0 a7 a6 a5 a4 a3 a2 a1 a0
            b8 b7 b6 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ 112 * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  let Q : k[X] := Polynomial.C (17592186044416 * eta)
  have hA' :
      localClearedSixteenthDefect810 h0 a7 a6 a5 a4 a3 a2 a1 a0 b8 b7
          b6 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 112 * Q := by
    simp only [Q, hA]
    ring
  exact piCeiling_of_pow_dvd_simplePole_ne_zero810 a j h0
    (localClearedSixteenthDefect810 h0 a7 a6 a5 a4 a3 a2 a1 a0 b8 b7
      b6 b5 b4 b3 b2 b1 (Polynomial.C lambda))
    Q rho 112 hh0 hroot hA' hclear hderiv hj

/-- After order `112` the remaining jet factor *is* the power-relation
scalar `C(η)`.  Combined with the source clearing this remaining factor
is a polynomial, hence cannot have derivative `C j / h0` with `j ≠ 0`. -/
theorem piLeftUnsolvedOrder112810_remaining_eq_C_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta a : k) (hh : h ≠ 0) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    ∃ (o96n o97n o98n o99n o100n o101n o102n o103n o104n o105n o106n
        o107n o108n o109n o110n o111n : k[X]),
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) = h * o96n ∧
        o111n +
            piLeftUnsolvedOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
              b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
          Polynomial.C eta := by
  obtain ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n,
      o105n, o106n, o107n, o108n, o109n, o110n, o111n, ho, ho97, ho98,
      ho99, ho100, ho101, ho102, ho103, ho104, ho105, ho106, ho107,
      ho108, ho109, ho110, ho111, hhol⟩ :=
    piLeftUnsolvedOrder112810_zero_of_power h t0 v1 u1 a4 a3 a2 a1 a0
      s1 w1 b62 b5 b4 b3 b2 b1 lambda eta a hh hdegree hroot hpower
  exact ⟨o96n, o97n, o98n, o99n, o100n, o101n, o102n, o103n, o104n,
    o105n, o106n, o107n, o108n, o109n, o110n, o111n, ho, hhol⟩

#print axioms algebraMap_cancel_pow_of_piClearing810
#print axioms piCeiling_C_eq_zero_of_deriv_eq_simplePole810
#print axioms piCeiling_of_pow_dvd_simplePole_eval810
#print axioms piCeiling_of_pow_dvd_simplePole_ne_zero810
#print axioms localClearedSixteenthDefect810_pow_112_dvd_contradicts_simplePole
#print axioms piLeftUnsolvedOrder112810_remaining_eq_C_of_power

end PiPoleCeiling810

end Max11DegreeRoutes
