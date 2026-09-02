import Sol68ScaleTwoAlignedNonsquareAfterLowerOneDoubleZeroScratch

/-! # Coprimality packet at the terminal double-zero load wall -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section TerminalLoadWallAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Rootwise nonvanishing is the exact coprimality input needed to cancel a
factor modulo a simple quadratic. -/
theorem quadratic_dvd_mul_iff_of_rootwise_ne_68
    (H u f : k[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hu : ∀ a : k, H.eval a = 0 → u.eval a ≠ 0) :
    H ∣ f * u ↔ H ∣ f := by
  constructor
  · intro hfu
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    obtain ⟨v, hv⟩ := hfu
    have hev := congrArg (fun P : k[X] => P.eval a) hv
    simp only [eval_mul, ha, zero_mul] at hev
    exact (mul_eq_zero.mp hev).resolve_right (hu a ha)
  · intro hf
    exact dvd_mul_of_dvd_left hf u

/-- The terminal `I4` equation identifies the next divisibility of `b₅`
and `w₂` because both `Φ₁` and `d₄` are units modulo `H`. -/
theorem terminalLoadWall_b_dvd_iff_w_68
    (H b phi w d : k[X])
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hphi : ∀ a : k, H.eval a = 0 → phi.eval a ≠ 0)
    (hd : ∀ a : k, H.eval a = 0 → d.eval a ≠ 0)
    (hI4 : b * phi + (6 : k[X]) * w * d = 0) :
    H ∣ b ↔ H ∣ w := by
  constructor
  · intro hb
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    have hbroot : b.eval a = 0 := by
      obtain ⟨bq, hbq⟩ := hb
      have hev := congrArg (fun P : k[X] => P.eval a) hbq
      simpa [ha] using hev
    have hev := congrArg (fun P : k[X] => P.eval a) hI4
    simp only [eval_add, eval_mul, eval_C, eval_zero, hbroot, zero_mul,
      zero_add] at hev
    have h6w0 := (mul_eq_zero.mp hev).resolve_right (hd a ha)
    have h6w : (6 : k) * w.eval a = 0 := by
      simpa only [eval_ofNat] using h6w0
    exact (mul_eq_zero.mp h6w).resolve_left (by norm_num)
  · intro hw
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    have hwroot : w.eval a = 0 := by
      obtain ⟨wq, hwq⟩ := hw
      have hev := congrArg (fun P : k[X] => P.eval a) hwq
      simpa [ha] using hev
    have hev := congrArg (fun P : k[X] => P.eval a) hI4
    simp only [eval_add, eval_mul, eval_C, eval_zero, hwroot, zero_mul,
      mul_zero, add_zero] at hev
    exact (mul_eq_zero.mp hev).resolve_right (hphi a ha)

/-- The nonhomogeneous load wall says both terminal factors are units modulo
the core and gives an exact second-order congruence, not a contradiction. -/
theorem terminalLoadWall_coprimality_packet_68
    (H b w eDot d kap : k[X]) (j : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hj : j ≠ 0)
    (hrow : H ^ 2 * b * w * eDot - d * kap = C j)
    (hroot : ∀ a : k, H.eval a = 0 → d.eval a * kap.eval a = -j) :
    H ^ 2 ∣ d * kap + C j ∧
      (∀ a : k, H.eval a = 0 → d.eval a ≠ 0 ∧ kap.eval a ≠ 0) ∧
      (∀ f : k[X], (H ∣ f * d ↔ H ∣ f) ∧
        (H ∣ f * kap ↔ H ∣ f)) := by
  have hne : ∀ a : k, H.eval a = 0 →
      d.eval a ≠ 0 ∧ kap.eval a ≠ 0 := by
    intro a ha
    have hp : d.eval a * kap.eval a ≠ 0 := by
      rw [hroot a ha]
      exact neg_ne_zero.mpr hj
    exact ⟨fun hd0 => hp (by rw [hd0, zero_mul]),
      fun hk0 => hp (by rw [hk0, mul_zero])⟩
  refine ⟨?_, hne, ?_⟩
  · refine ⟨b * w * eDot, ?_⟩
    linear_combination -hrow
  · intro f
    exact ⟨quadratic_dvd_mul_iff_of_rootwise_ne_68 H d f hdeg hsimple
        (fun a ha => (hne a ha).1),
      quadratic_dvd_mul_iff_of_rootwise_ne_68 H kap f hdeg hsimple
        (fun a ha => (hne a ha).2)⟩

end TerminalLoadWallAlgebra68

section TerminalLoadWallSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing coprimality refinement of the pure double-zero load wall.
The mixed `r=0` and `Φ₁=0` allocations are retained verbatim. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneLoadWallPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t b1 d1 phi1 k1 b2 d2 w2 : k[X]),
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r = H * d1 ∧
      b1 = H * b2 ∧ d1 = H * d2 ∧
      (∀ a : k, H.eval a = 0 →
        r.eval a = 0 ∨ phi1.eval a = 0 ∨
          (b2.eval a = 0 ∧ b2.derivative.eval a = 0 ∧
           d2.eval a = 0 ∧ d2.derivative.eval a = 0 ∧
           k1.eval a ≠ 0)) ∧
      ((∀ a : k, H.eval a = 0 →
          r.eval a ≠ 0 ∧ phi1.eval a ≠ 0) →
        ∃ b5 d4 : k[X],
          b2 = H ^ 5 * b5 ∧ d2 = H ^ 4 * d4 ∧
          H ^ 7 ∣ cubicBNumerator68 (p.coeff 3) t r ∧
          H ^ 6 ∣ cubicDNumerator68 H (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r ∧
          b5 * phi1 + (6 : k[X]) * w2 * d4 = 0 ∧
          (let A0 := cubicANumerator68 t r
           let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           H ^ 2 * b5 * w2 * eDot - d4 * k1 = C j) ∧
          H ^ 2 ∣ d4 * k1 + C j ∧
          (H ∣ b5 ↔ H ∣ w2) ∧
          (∀ f : k[X], (H ∣ f * d4 ↔ H ∣ f) ∧
            (H ∣ f * k1 ↔ H ∣ f)) ∧
          ∀ a : k, H.eval a = 0 →
            d4.eval a ≠ 0 ∧ k1.eval a ≠ 0 ∧
            d4.eval a * k1.eval a = -j) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
      _hg, _hgr, _ht, _hX, _hY, hb1, hd1, _hw1, _hphi, hb2, hd2, _hw2,
      _hI4, _hrow, hroots, hpure⟩ :=
    S.terminalAfterLowerOneDoubleZeroPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  refine ⟨r, t, b1, d1, phi1, k1, b2, d2, w2,
    hb1, hd1, hb2, hd2, hroots, ?_⟩
  intro hall
  obtain ⟨b5, d4, hb5, hd4, hI4final, hrowFinal, hrootFinal⟩ := hpure hall
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hrowFinal' : H ^ 2 * b5 * w2 * eDot - d4 * k1 = C j := by
    simpa only [A0, C0, E0, eDot] using hrowFinal
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hcop := terminalLoadWall_coprimality_packet_68
    H b5 w2 eDot d4 k1 j hdeg hsimple hj hrowFinal' hrootFinal
  have hiff := terminalLoadWall_b_dvd_iff_w_68 H b5 phi1 w2 d4
    hdeg hsimple (fun a ha => (hall a ha).2)
      (fun a ha => (hcop.2.1 a ha).1) hI4final
  have hB7 : H ^ 7 ∣ cubicBNumerator68 (p.coeff 3) t r := by
    refine ⟨b5, ?_⟩
    rw [hb1, hb2, hb5]
    ring
  have hD6 : H ^ 6 ∣ cubicDNumerator68 H (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r := by
    refine ⟨d4, ?_⟩
    rw [hd1, hd2, hd4]
    ring
  refine ⟨b5, d4, hb5, hd4, hB7, hD6, hI4final, hrowFinal,
    hcop.1, hiff, hcop.2.2, ?_⟩
  intro a ha
  exact ⟨(hcop.2.1 a ha).1, (hcop.2.1 a ha).2, hrootFinal a ha⟩

end TerminalLoadWallSource68

end Max11DegreeRoutes
