import Grok810PiLinearRootFalseScratch

/-! # Forced `η = 0` on the `(8,10)` degree-one `π` linear-root source

`Grok810PiLinearRootFalseScratch` lands
`piFace810_linearRoot_false_of_eta_tie` and
`piFace810_linearRoot_false_of_packet_tie` *conditionally* on a
universal `η = c·j`.  Its header records the three facts this file
starts from:

* the source wrapper supplies remaining′ = `0`, not `C(j)/h0`;
* `h0^{112} ∣ C(2⁴⁴ η)` forces `η = 0`;
* CAS produced no live-source universal `η/j`.

The new route takes `η = 0` as forced on a literal source at a linear
root and tries to derive False *without* any `η = c·j` tie, from the
degree-`0` Keller row `a0' b1 - a1 b0' = C(j)` with `j ≠ 0`, the
normalized leading core, and the linear-root hypothesis.

CAS `derive_810_pi_eta_zero.py` (job `810-pi-eta-zero`) records:

* formal remaining `Order112 = 0` kills the holomorphic coordinate
  `a0`;
* after `a0 = 0`, `Order111` vanishes and `Order110 = 2⁴⁴ a1 b1`, so
  the next formal mixin kills the product `a1 b1`; the `a1 = 0` branch
  of Jac0 is then `j = 0`;
* the unsolved head *survives* `a0 = 0` (it still involves
  `t0, v1, u1, a4, s1, w1, b62, b5`);
* the *live* polynomial identity is `o111n = N a0²`, hence
  `o111n(a) = N a0(a)²`.  This does **not** kill `a0(a)`.

So `η = 0` is consistent with a live source.  The surviving source
datum is `p.coeff 0`, compensated by the holomorphic remainder
`o111n = 21990232555520 (p.coeff 0)²`.  Jac0 remains
`a0' b1 - a1 b0' = C(j)`.

**CLOSED:** `piFace810_linearRoot_false_of_a0_a1` — vanishing of the
lowest two `Y`-coefficients of `p` forces `j = 0`.  This is the
nonvanishing that a *formal* `a0 = a1 = 0` degeneration would
contradict.

**CLOSED:** `piFace810_linearRoot_a0sq_of_forced_eta_zero` — a forced
`η = 0` rewrites the remaining identity as `o111n = N a0²`.

**CLOSED:** `piFace810_linearRoot_a0_eval_zero_of_eta_zero_of_remainder_root`
— `η = 0` *and* `o111n(a) = 0` kill `a0(a)`, and Jac0 reduces to
`h0'(a) a0n(a) b1(a) - a1(a) b0'(a) = j`.

**NOT A CLOSURE of `piFace810_linearRoot`.**  Gap:
`o111n.eval a = 0` (the formal identification of the remaining
constant with `Order112`) is not supplied by the source wrapper.
Without it, `η = 0` does not kill `a0(a)`.  Even with it, the reduced
Jac0 survives unless the first Taylor of `a0` *and* `a1(a)` also
vanish.  No `ρ` simple pole is imported.

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

/-! ## Linear derivative at a simple root -/

section LinearDerivative810Pi

variable {k : Type*} [Field k]

/-- A degree-one polynomial has nonzero derivative at every point. -/
theorem linearPolynomial_derivative_eval_ne_zero810Pi
    (h0 : k[X]) (a : k) (hdegree : h0.natDegree = 1) :
    h0.derivative.eval a ≠ 0 := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hder : h0.derivative = C c := by
    rw [← hlinear]
    simp [derivative_add, derivative_mul, derivative_X, derivative_C,
      mul_one, zero_mul]
  rw [hder, eval_C]
  exact hc

/-- Vanishing at a simple root is exactly one Taylor step with zero
constant term. -/
theorem linearPolynomial_eq_mul_of_eval_eq_zero810Pi
    (h0 f : k[X]) (a : k) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hf : f.eval a = 0) :
    ∃ fn : k[X], f = h0 * fn :=
  linearPolynomial_dvd_of_eval_eq_zero_810 h0 f a hdegree hroot hf

/-- At a simple root, `(h0 · fn)'(a) = h0'(a) · fn(a)`. -/
theorem linearPolynomial_mul_derivative_eval810Pi
    (h0 fn : k[X]) (a : k) (hroot : h0.eval a = 0) :
    (h0 * fn).derivative.eval a = h0.derivative.eval a * fn.eval a := by
  rw [derivative_mul, eval_add, eval_mul, eval_mul, hroot, zero_mul,
    add_zero]

end LinearDerivative810Pi

/-! ## Jac0 with vanishing lowest `Y`-coefficients -/

section JacobianRow0Degenerate810Pi

variable {k : Type*} [Field k] [CharZero k]

/-- If `p` has no `Y⁰` term, Jac0 reduces to `-p₁ q₀' = C j`. -/
theorem sourceJacobianRow0_of_coeff0_zero_810
    {p q : k[X][X]} {j : k}
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ha0 : p.coeff 0 = 0) :
    - p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  have hrow := sourceJacobianRow0_810 hD
  simpa [ha0, derivative_zero, zero_mul, neg_mul] using hrow

/-- If `p` has no `Y⁰` and no `Y¹` term, the Keller constant vanishes. -/
theorem sourceJacobianRow0_eq_zero_of_coeff0_coeff1_zero_810
    {p q : k[X][X]} {j : k}
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ha0 : p.coeff 0 = 0) (ha1 : p.coeff 1 = 0) :
    j = 0 := by
  have hrow := sourceJacobianRow0_of_coeff0_zero_810 hD ha0
  simp only [ha1, zero_mul, neg_zero] at hrow
  have := congrArg (fun r : k[X] ↦ r.coeff 0) hrow.symm
  simpa [coeff_C_zero] using this

/-- **CLOSED** as a source fact: vanishing of `p₀` and `p₁` contradicts
`j ≠ 0`.  This is the nonvanishing a formal `η = 0` degeneration that
killed both lowest `Y`-coefficients would hit. -/
theorem piFace810_linearRoot_false_of_a0_a1
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
    (ha0 : p.coeff 0 = 0) (ha1 : p.coeff 1 = 0) : False :=
  hj (sourceJacobianRow0_eq_zero_of_coeff0_coeff1_zero_810 hD ha0 ha1)

/-- Root form: if `p₀(a) = 0` then Jac0 is the first Taylor of `p₀`
against `q₁(a)`, minus `p₁(a) q₀'(a)`. -/
theorem sourceJacobianRow0_eval_of_coeff0_root_810
    {p q : k[X][X]} {h0 : k[X]} {j a : k}
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hh0degree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (ha0 : (p.coeff 0).eval a = 0) :
    ∃ a0n : k[X],
      p.coeff 0 = h0 * a0n ∧
        h0.derivative.eval a * a0n.eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j := by
  obtain ⟨a0n, ha0eq⟩ :=
    linearPolynomial_eq_mul_of_eval_eq_zero810Pi h0 (p.coeff 0) a
      hh0degree hroot ha0
  refine ⟨a0n, ha0eq, ?_⟩
  have hrow := sourceJacobianRow0_eval_810 (a := a) hD
  have hder :=
    linearPolynomial_mul_derivative_eval810Pi h0 a0n a hroot
  rw [ha0eq, hder] at hrow
  exact hrow

/-- If `p₀(a) = p₁(a) = 0` and the first Taylor of `p₀` also vanishes
at the root, Jac0 forces `j = 0`. -/
theorem sourceJacobianRow0_eval_eq_zero_of_a0_taylor_a1_810
    {p q : k[X][X]} {h0 : k[X]} {j a : k} {a0n : k[X]}
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hh0degree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (ha0eq : p.coeff 0 = h0 * a0n)
    (ha0n : a0n.eval a = 0) (ha1 : (p.coeff 1).eval a = 0) :
    j = 0 := by
  have hrow := sourceJacobianRow0_eval_810 (a := a) hD
  have hder :=
    linearPolynomial_mul_derivative_eval810Pi h0 a0n a hroot
  rw [ha0eq, hder, ha0n, ha1] at hrow
  ring_nf at hrow
  exact hrow.symm

end JacobianRow0Degenerate810Pi

/-! ## Forced `η = 0` rewrites the holomorphic remainder -/

section PiEtaZeroRemaining810

variable {k : Type*} [Field k] [CharZero k]

/-- The remaining identity at `η = 0` is `o111n = N a0²`. -/
theorem piRemaining810_eq_a0sq_of_eta_zero
    (o111n a0 : k[X])
    (hrest :
      o111n - (21990232555520 : k[X]) * a0 ^ 2 =
        Polynomial.C (17592186044416 * (0 : k))) :
    o111n = (21990232555520 : k[X]) * a0 ^ 2 := by
  simpa [mul_zero, C_0, sub_eq_zero] using hrest

/-- Evaluating that identity at the linear root. -/
theorem piRemaining810_eval_eq_a0sq_of_eta_zero
    (o111n a0 : k[X]) (a : k)
    (hsq : o111n = (21990232555520 : k[X]) * a0 ^ 2) :
    o111n.eval a = (21990232555520 : k) * (a0.eval a) ^ 2 := by
  simpa [eval_mul, eval_pow] using congrArg (fun r : k[X] ↦ r.eval a) hsq

/-- `η = 0` and `o111n(a) = 0` kill `a0(a)`.  This is the extra root
vanishing the source wrapper does not supply. -/
theorem piA0_eval_eq_zero_of_eta_zero_of_remainder_root
    (o111n a0 : k[X]) (a : k)
    (hsq : o111n = (21990232555520 : k[X]) * a0 ^ 2)
    (hrootRem : o111n.eval a = 0) :
    a0.eval a = 0 := by
  have heval := piRemaining810_eval_eq_a0sq_of_eta_zero o111n a0 a hsq
  rw [hrootRem] at heval
  have hN : (21990232555520 : k) ≠ 0 := piOrder112Integer810_ne_zero
  have hsq0 : (a0.eval a) ^ 2 = 0 :=
    (mul_eq_zero.mp heval.symm).resolve_left hN
  exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hsq0

end PiEtaZeroRemaining810

/-! ## Source-facing packet with forced `η = 0` -/

section PiEtaZeroPacket810

variable {k : Type*} [Field k] [CharZero k]

/-- **CLOSED** as glue: a forced `η = 0` on the cancel-expose remaining
identity is `o111n = N a0²`, and Jac0 is the last Keller row.  This
does not kill `a0`. -/
theorem piFace810_linearRoot_a0sq_of_forced_eta_zero
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hzero : ∀ eta : k,
      localClearedSixteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C (17592186044416 * eta) * h0 ^ 112 →
      eta = 0) :
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o111n : k[X]),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        localClearedSixteenthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 4 * v1)
            (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (h0 ^ 6 * s1) (h0 ^ 4 * w1)
            (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) = 0 ∧
        o111n = (21990232555520 : k[X]) * (p.coeff 0) ^ 2 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        o111n.eval a =
          (21990232555520 : k) * ((p.coeff 0).eval a) ^ 2 := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o111n, eta, ht0, hv0,
      hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, hA, _hhol, hrest⟩ :=
    piFace810_linearRoot_remaining_eq_C p q H h0 j lambda a hp hq hh0
      hh0degree hH hp8 hq10 hN hD hroot
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
  have hAraw :
      localClearedSixteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C (17592186044416 * eta) * h0 ^ 112 := by
    simpa only [ht0, ha6, ha5, hb8, hb7, hb62] using hA
  have heta0 : eta = 0 := hzero eta hAraw
  subst heta0
  have hA0 : localClearedSixteenthDefect810 h0 (h0 ^ 6 * t0)
      (h0 ^ 4 * v1) (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3) (p.coeff 2)
      (p.coeff 1) (p.coeff 0) (h0 ^ 6 * s1) (h0 ^ 4 * w1)
      (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) (q.coeff 3)
      (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) = 0 := by
    simpa [mul_zero, C_0, zero_mul] using hA
  have hsq := piRemaining810_eq_a0sq_of_eta_zero o111n (p.coeff 0) hrest
  have heval :=
    piRemaining810_eval_eq_a0sq_of_eta_zero o111n (p.coeff 0) a hsq
  have hjac := sourceJacobianRow0_810 hD
  exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o111n, ht0, hv0, hu0,
    hs0, hw0, hv1, hs1, hu1, hw1, hb62, hA0, hsq, hjac, heval⟩

/-- **CLOSED** as glue: forced `η = 0` together with the missing root
vanishing `o111n(a) = 0` kills `a0(a)` and reduces Jac0 to the first
Taylor of `p₀`. -/
theorem piFace810_linearRoot_a0_eval_zero_of_eta_zero_of_remainder_root
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (hzero : ∀ eta : k,
      localClearedSixteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C (17592186044416 * eta) * h0 ^ 112 →
      eta = 0)
    (hrootRem : ∀ o111n : k[X],
      o111n = (21990232555520 : k[X]) * (p.coeff 0) ^ 2 →
        o111n.eval a = 0) :
    ∃ a0n : k[X],
      p.coeff 0 = h0 * a0n ∧ (p.coeff 0).eval a = 0 ∧
        h0.derivative.eval a * a0n.eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j := by
  obtain ⟨_t0, _v0, _u0, _s0, _w0, _v1, _s1, _u1, _w1, _b62, o111n,
      _ht0, _hv0, _hu0, _hs0, _hw0, _hv1, _hs1, _hu1, _hw1, _hb62, _hA0,
      hsq, _hjac, _heval⟩ :=
    piFace810_linearRoot_a0sq_of_forced_eta_zero p q H h0 j lambda a hp
      hq hh0 hh0degree hH hp8 hq10 hN hD hroot hzero
  have ha0 : (p.coeff 0).eval a = 0 :=
    piA0_eval_eq_zero_of_eta_zero_of_remainder_root o111n (p.coeff 0) a
      hsq (hrootRem o111n hsq)
  obtain ⟨a0n, ha0eq, hjac⟩ :=
    sourceJacobianRow0_eval_of_coeff0_root_810 hD hh0degree hroot ha0
  exact ⟨a0n, ha0eq, ha0, hjac⟩

/-- Conditional False: forced `η = 0`, the missing `o111n(a) = 0`, and
vanishing of the first Taylor of `p₀` together with `p₁(a)`, contradict
`j ≠ 0`.  The last two root vanishings are the exact remaining gap
after killing `a0(a)`. -/
theorem piFace810_linearRoot_false_of_eta_zero_of_remainder_root_taylor
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
    (hzero : ∀ eta : k,
      localClearedSixteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C (17592186044416 * eta) * h0 ^ 112 →
      eta = 0)
    (hrootRem : ∀ o111n : k[X],
      o111n = (21990232555520 : k[X]) * (p.coeff 0) ^ 2 →
        o111n.eval a = 0)
    (htaylor : ∀ a0n : k[X], p.coeff 0 = h0 * a0n →
      a0n.eval a = 0 ∧ (p.coeff 1).eval a = 0) : False := by
  obtain ⟨a0n, ha0eq, _ha0, _hjac⟩ :=
    piFace810_linearRoot_a0_eval_zero_of_eta_zero_of_remainder_root
      p q H h0 j lambda a hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
      hzero hrootRem
  obtain ⟨ha0n, ha1⟩ := htaylor a0n ha0eq
  exact hj (sourceJacobianRow0_eval_eq_zero_of_a0_taylor_a1_810 hD
    hh0degree hroot ha0eq ha0n ha1)

end PiEtaZeroPacket810

#print axioms linearPolynomial_derivative_eval_ne_zero810Pi
#print axioms linearPolynomial_eq_mul_of_eval_eq_zero810Pi
#print axioms linearPolynomial_mul_derivative_eval810Pi
#print axioms sourceJacobianRow0_of_coeff0_zero_810
#print axioms sourceJacobianRow0_eq_zero_of_coeff0_coeff1_zero_810
#print axioms piFace810_linearRoot_false_of_a0_a1
#print axioms sourceJacobianRow0_eval_of_coeff0_root_810
#print axioms sourceJacobianRow0_eval_eq_zero_of_a0_taylor_a1_810
#print axioms piRemaining810_eq_a0sq_of_eta_zero
#print axioms piRemaining810_eval_eq_a0sq_of_eta_zero
#print axioms piA0_eval_eq_zero_of_eta_zero_of_remainder_root
#print axioms piFace810_linearRoot_a0sq_of_forced_eta_zero
#print axioms piFace810_linearRoot_a0_eval_zero_of_eta_zero_of_remainder_root
#print axioms piFace810_linearRoot_false_of_eta_zero_of_remainder_root_taylor

end Max11DegreeRoutes
