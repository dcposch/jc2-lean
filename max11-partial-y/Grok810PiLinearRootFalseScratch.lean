import Grok810PiChamberClosureScratch

/-! # Composition of the `(8,10)` degree-one `π` linear-root packet

`Grok810PiChamberClosureScratch` supplies, on a literal source at a
linear root,

* `piFace810_linearRoot_cancelExposePacket`:
  `localClearedSixteenthDefect810 = C(2⁴⁴ η) · h0^{112}`;
* `piFace810_linearRoot_false_of_scaledPi_simplePole`: that
  `h^{112}` identity plus remaining′ = `C(j)/h0` is False;
* `sourcePiResidual810_eq_C_of_source`: the depressed `π` residual is
  a ground-field constant, so remaining′ = `0`.

CAS `derive_810_pi_eta_j_tie.py` (job `810-pi-eta-j-tie`) records the
formal `h^{112}` coefficient after the six unsolved valuations:

* `Order112 = -21990232555520 a0²`;
* `Order112 / 2⁴⁴ = -5/4 a0²`;
* `Order112Plus = 0`;
* the degree-`0` Keller row is `a0' b1 - a1 b0' = C(j)`.

The holomorphic remainder is the polynomial identity
`o111n + Order112 = C(2⁴⁴ η)`.  Linear-power divisibility of a
*constant* polynomial `C(E)` by `h0^{112}` forces `E = 0`.  A universal
nonzero scalar `c` with `η = c·j`, together with `η = 0`, yields False.

FLAG: cancel-expose composition of the `(8,10)` `π` linear-root
chambers (uniqueness of `η`, Jac0, remaining, CAS `-5/4`, False from
`η = c·j` and `η = 0`).

**CLOSED:** `piFace810_linearRoot_false_of_eta_tie` — if the source `η`
equals `c·j` for a source-independent `c ≠ 0` and `η = 0`, then
`j ≠ 0` is impossible.

**NOT A CLOSURE of `piFace810_linearRoot`.**  The committed source
wrapper gives remaining′ = `0`, not `C(j)/h0`.  CAS does not produce a
live-source universal `η/j`.  `h0^{112} ∣ C(η)` is equivalent to
`η = 0` and is not an independent degree bound on the numerator
`C(2⁴⁴ η)·h0^{112}`.  No `ρ` simple pole is imported.

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

/-! ## CAS scales of the weight-`112` remaining factor -/

/-- Integer clearing of `2⁴⁴ h^{112} π`. -/
def piSourceClearingScale810 : ℕ := 17592186044416

/-- Integer coefficient of the frozen order-`112` mixin `-N a0²`. -/
def piOrder112Integer810 : ℕ := 21990232555520

theorem piSourceClearingScale810_eq :
    piSourceClearingScale810 = 2 ^ 44 := by decide

theorem piOrder112Integer810_eq :
    piOrder112Integer810 = 21990232555520 := rfl

theorem piSourceClearingScale810_ne_zero {k : Type*}
    [Field k] [CharZero k] :
    (piSourceClearingScale810 : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

theorem piOrder112Integer810_ne_zero {k : Type*}
    [Field k] [CharZero k] :
    (piOrder112Integer810 : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

/-- CAS: `21990232555520 / 17592186044416 = 5/4`. -/
theorem piOrder112Integer810_div_scale {k : Type*}
    [Field k] [CharZero k] :
    (piOrder112Integer810 : k) / piSourceClearingScale810 = 5 / 4 := by
  unfold piOrder112Integer810 piSourceClearingScale810
  field_simp
  norm_num

/-- Frozen order-`112` mixin, independent of the other holomorphic
coordinates. -/
theorem piLeftUnsolvedOrder112810_eq_neg_a0sq
    {R : Type*} [CommRing R]
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    piLeftUnsolvedOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      - (21990232555520 : R) * a0 ^ 2 :=
  rfl

/-! ## Copied linear-power ceiling (no degree-zero import) -/

section PolynomialCeiling810Pi

variable {k : Type*} [Field k]

theorem polynomial_eq_zero_of_natDegree_lt_of_linear_pow_dvd810Pi
    (p h0 : k[X]) (M : ℕ) (hdegree : h0.natDegree = 1)
    (hdeg : p.natDegree < M) (hdvd : h0 ^ M ∣ p) : p = 0 := by
  have hpow : (h0 ^ M).natDegree = M := by
    rw [natDegree_pow, hdegree, mul_one]
  exact eq_zero_of_dvd_of_natDegree_lt hdvd (hdeg.trans_eq hpow.symm)

/-- A constant polynomial divisible by a positive power of a linear
scale is the zero constant. -/
theorem C_eq_zero_of_linear_pow_dvd810Pi
    (h0 : k[X]) (E : k) (M : ℕ) (hM : 0 < M)
    (hdegree : h0.natDegree = 1) (hdvd : h0 ^ M ∣ C E) : E = 0 := by
  have hdeg : (C E).natDegree < M := (natDegree_C E).trans_lt hM
  have hzero :=
    polynomial_eq_zero_of_natDegree_lt_of_linear_pow_dvd810Pi
      (C E) h0 M hdegree hdeg hdvd
  have hE : E = 0 := by
    have := congrArg (fun p : k[X] ↦ p.coeff 0) hzero
    simpa [coeff_C_zero] using this
  exact hE

end PolynomialCeiling810Pi

/-! ## Degree-`0` Jacobian row, copied from the seventeenth packet -/

section JacobianRow0810Pi

variable {k : Type*} [Field k] [CharZero k]

/-- The last Keller coefficient: `p₀' q₁ - p₁ q₀' = C j`. -/
theorem sourceJacobianRow0_810
    {p q : k[X][X]} {j : k}
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    (p.coeff 0).derivative * q.coeff 1 -
      p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  have hcoeff := congrArg (fun r : k[X][X] ↦ r.coeff 0) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 0 :
      Finset (ℕ × ℕ)) =
      ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num at hcoeff
  linear_combination hcoeff

theorem sourceJacobianRow0_eval_810
    {p q : k[X][X]} {j a : k}
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j := by
  have hrow := sourceJacobianRow0_810 hD
  have heval := congrArg (fun r : k[X] ↦ r.eval a) hrow
  simpa only [eval_sub, eval_mul, eval_C] using heval

end JacobianRow0810Pi

/-! ## Uniqueness of the source `π` scalar -/

section PiEtaUnique810

variable {k : Type*} [Field k] [CharZero k]

theorem sourcePiEta810_unique_of_C_pow
    (h0 : k[X]) (eta1 eta2 : k) (hh0 : h0 ≠ 0)
    (h :
      Polynomial.C (17592186044416 * eta1) * h0 ^ 112 =
        Polynomial.C (17592186044416 * eta2) * h0 ^ 112) :
    eta1 = eta2 := by
  have hpow : h0 ^ 112 ≠ 0 := pow_ne_zero 112 hh0
  have hC :
      Polynomial.C (17592186044416 * eta1) =
        Polynomial.C (17592186044416 * eta2) :=
    mul_right_cancel₀ hpow h
  have hmul : (17592186044416 : k) * eta1 =
      (17592186044416 : k) * eta2 := by
    have := congrArg (fun p : k[X] ↦ p.coeff 0) hC
    simpa [coeff_C_zero] using this
  exact mul_left_cancel₀ (by norm_num) hmul

/-- Linear-power divisibility of the remaining constant forces that
constant to vanish.  This is the honest content of “`h0^{112}` divides
a degree-bounded object”.  It does *not* follow from
`A0 = C(E)·h0^{112}` alone. -/
theorem piEta810_eq_zero_of_C_pow_dvd
    (h0 : k[X]) (eta : k) (hdegree : h0.natDegree = 1)
    (hdvd : h0 ^ 112 ∣ Polynomial.C (17592186044416 * eta)) :
    eta = 0 := by
  have hE :=
    C_eq_zero_of_linear_pow_dvd810Pi h0 (17592186044416 * eta) 112
      (by decide) hdegree hdvd
  exact mul_left_cancel₀ (by norm_num)
    (hE.trans (mul_zero (17592186044416 : k)).symm)

end PiEtaUnique810

/-! ## Holomorphic remainder on a literal source -/

section PiRemaining810

variable {k : Type*} [Field k] [CharZero k]

/-- Cancel-expose plus the order-`112` remainder: `o111n - N a0²` is
the source scalar `C(2⁴⁴ η)`. -/
theorem piFace810_linearRoot_remaining_eq_C
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
    ∃ (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 o111n : k[X]) (eta : k),
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        localClearedSixteenthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 4 * v1)
            (h0 ^ 2 * u1) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (h0 ^ 6 * s1) (h0 ^ 4 * w1)
            (h0 ^ 2 * b62) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C (17592186044416 * eta) * h0 ^ 112 ∧
        o111n +
            piLeftUnsolvedOrder112810 t0 v1 u1 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
              b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C (17592186044416 * eta) ∧
        o111n - (21990232555520 : k[X]) * (p.coeff 0) ^ 2 =
          Polynomial.C (17592186044416 * eta) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, _t0n, _a1n, _a0n,
      _b2n, _b1n, eta, ht0, hv0, hu0, hs0, hw0, hv1, hs1, hu1, hw1,
      hb62, _ht0T, _ha1T, _ha0T, _hb2T, _hb1T, hA⟩ :=
    piFace810_linearRoot_cancelExposePacket p q H h0 j lambda a hp hq
      hh0 hh0degree hH hp8 hq10 hN hD hroot
  obtain ⟨_o96n, _o97n, _o98n, _o99n, _o100n, _o101n, _o102n, _o103n,
      _o104n, _o105n, _o106n, _o107n, _o108n, _o109n, _o110n, o111n,
      _ho, hhol⟩ :=
    piLeftUnsolvedOrder112810_remaining_eq_C_of_power h0 t0 v1 u1
      (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
      b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
      lambda (17592186044416 * eta) a hh0 hh0degree hroot hA
  have hrest :
      o111n - (21990232555520 : k[X]) * (p.coeff 0) ^ 2 =
        Polynomial.C (17592186044416 * eta) := by
    have hO := piLeftUnsolvedOrder112810_eq_neg_a0sq t0 v1 u1
      (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
      b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
      (Polynomial.C lambda)
    rw [hO] at hhol
    simpa [sub_eq_add_neg] using hhol
  exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, o111n, eta, ht0, hv0,
    hu0, hs0, hw0, hv1, hs1, hu1, hw1, hb62, hA, hhol, hrest⟩

end PiRemaining810

/-! ## False from a universal nonzero `η = c·j` together with `η = 0` -/

section PiLinearRootTie810

variable {k : Type*} [Field k] [CharZero k]

/-- **CLOSED** as a glue: source `η = c·j` with `c ≠ 0` and `η = 0`
contradict `j ≠ 0`.  The two extra hypotheses are the exact remaining
gap of `piFace810_linearRoot`. -/
theorem piFace810_linearRoot_false_of_eta_tie
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
    (c : k) (hc : c ≠ 0)
    (htie_zero :
      ∃ eta : k,
        localClearedSixteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C (17592186044416 * eta) * h0 ^ 112 ∧
          eta = c * j ∧ eta = 0) : False := by
  obtain ⟨eta, _hA, htie, hzero⟩ := htie_zero
  have hj0 : j = 0 :=
    (mul_eq_zero.mp (htie.symm.trans hzero)).resolve_left hc
  exact hj hj0

/-- The cancel-expose packet produces a source `η`.  A universal
nonzero `c` with that `η` equal to `c·j`, together with `η = 0`, is
False. -/
theorem piFace810_linearRoot_false_of_packet_tie
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
    (c : k) (hc : c ≠ 0)
    (htie : ∀ eta : k,
      localClearedSixteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C (17592186044416 * eta) * h0 ^ 112 →
      eta = c * j)
    (hzero : ∀ eta : k,
      localClearedSixteenthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C (17592186044416 * eta) * h0 ^ 112 →
      eta = 0) : False := by
  obtain ⟨eta, hA, _hclear⟩ :=
    piFace810_linearRoot_cancelExpose_of_source p q H h0 j lambda a hp
      hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  exact piFace810_linearRoot_false_of_eta_tie p q H h0 j lambda a hp hq
    hh0 hh0degree hH hp8 hq10 hN hD hroot hj c hc
    ⟨eta, hA, htie eta hA, hzero eta hA⟩

end PiLinearRootTie810

#print axioms piSourceClearingScale810_eq
#print axioms piOrder112Integer810_div_scale
#print axioms piLeftUnsolvedOrder112810_eq_neg_a0sq
#print axioms polynomial_eq_zero_of_natDegree_lt_of_linear_pow_dvd810Pi
#print axioms C_eq_zero_of_linear_pow_dvd810Pi
#print axioms sourceJacobianRow0_810
#print axioms sourceJacobianRow0_eval_810
#print axioms sourcePiEta810_unique_of_C_pow
#print axioms piEta810_eq_zero_of_C_pow_dvd
#print axioms piFace810_linearRoot_remaining_eq_C
#print axioms piFace810_linearRoot_false_of_eta_tie
#print axioms piFace810_linearRoot_false_of_packet_tie

end Max11DegreeRoutes
