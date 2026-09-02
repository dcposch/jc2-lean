import Sol68ScaleTwoAlignedNonsquareAfterLowerOneScratch

/-! # Components after the aligned-nonsquare lower-row descent -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section TerminalAfterLowerOneFaces68

variable {k : Type*} [Field k] [CharZero k]

/-- The first unused coefficient of the descended `I4` row on the
`b₂=d₂=0` component. -/
theorem terminalAfterLowerOne_I4_derivative_face_68
    (H b phi w d : k[X]) (a : k)
    (ha : H.eval a = 0) (hb : b.eval a = 0) (hd : d.eval a = 0)
    (hI4 : b * phi + (6 : k[X]) * H * w * d = 0) :
    b.derivative.eval a * phi.eval a = 0 := by
  have hder := congrArg (fun f : k[X] => f.derivative) hI4
  have heval := congrArg (fun f : k[X] => f.eval a) hder
  simp only [derivative_add, derivative_mul, derivative_C, derivative_zero,
    eval_add, eval_mul, eval_C, eval_zero] at heval
  rw [ha, hb, hd] at heval
  simpa using heval

/-- The first unused coefficient of the descended last row on the
`b₂=d₂=0` component.  The Jacobian load still starts four orders later. -/
theorem terminalAfterLowerOne_lastRow_derivative_face_68
    (H b w eDot d kap : k[X]) (j a : k)
    (ha : H.eval a = 0) (hb : b.eval a = 0) (hd : d.eval a = 0)
    (hrow : H * b * w * eDot - d * kap = C j * H ^ 4) :
    d.derivative.eval a * kap.eval a = 0 := by
  have hder := congrArg (fun f : k[X] => f.derivative) hrow
  have heval := congrArg (fun f : k[X] => f.eval a) hder
  simp only [derivative_sub, derivative_mul, derivative_pow, derivative_C,
    derivative_zero, eval_sub, eval_add, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero] at heval
  have hz : -(d.derivative.eval a * kap.eval a) = 0 := by
    simpa [ha, hb, hd] using heval
  exact neg_eq_zero.mp hz

/-- Away from `r=0`, the canonical value of `k₁` identifies its zero
component with `Φ₁=0`.  On the complementary component the first unused
`I4` and last-row coefficients force double zeros of both second quotients. -/
theorem terminalAfterLowerOne_components_collapse_68
    (r A b phi d kap hprime bprime dprime : k)
    (hr : r ≠ 0) (hhprime : hprime ≠ 0)
    (hA : A = -(1 / 12 : k) * r ^ 2)
    (hk : kap = hprime * (-(1 / 6 : k) * A * phi))
    (hI4 : b * phi = 0) (hrow : d * kap = 0)
    (hI4next : b = 0 → d = 0 → bprime * phi = 0)
    (hrownext : b = 0 → d = 0 → dprime * kap = 0) :
    phi = 0 ∨
      (b = 0 ∧ bprime = 0 ∧ d = 0 ∧ dprime = 0 ∧ kap ≠ 0) := by
  rcases eq_or_ne phi 0 with hphi | hphi
  · exact Or.inl hphi
  · right
    have hAne : A ≠ 0 := by
      rw [hA]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)
    have hkne : kap ≠ 0 := by
      rw [hk]
      exact mul_ne_zero hhprime
        (mul_ne_zero (mul_ne_zero (by norm_num) hAne) hphi)
    have hb : b = 0 := (mul_eq_zero.mp hI4).resolve_right hphi
    have hd : d = 0 := (mul_eq_zero.mp hrow).resolve_right hkne
    exact ⟨hb, (mul_eq_zero.mp (hI4next hb hd)).resolve_right hphi,
      hd, (mul_eq_zero.mp (hrownext hb hd)).resolve_right hkne, hkne⟩

end TerminalAfterLowerOneFaces68

section TerminalAfterLowerOneComponentsSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing three-component refinement of the exact four-component
packet.  The four raw components are retained explicitly.  Away from `r=0`,
the two `k₁=0` components coincide with `Φ₁=0`; the sole complementary
component has double zeros of `b₂` and `d₂`. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneComponentsPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (g r t X Yd b1 d1 w1 phi1 k1 b2 d2 w2 : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r = H * d1 ∧
      cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma = H * w1 ∧
      cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r S.gamma S.epsilon = H * phi1 ∧
      b1 = H * b2 ∧ d1 = H * d2 ∧ w1 = H * w2 ∧
      (27 : k[X]) * p.coeff 2 - r ^ 2 * X =
        H * (C (243 / 4 : k) * w2 + C (27 / 2 : k) * r * b2 + X ^ 2 -
          C (243 / 4 : k) * C (2 / 3 * S.gamma : k)) ∧
      b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4) ∧
      ∀ a : k, H.eval a = 0 →
        Yd.eval a = 6 * r.eval a * X.eval a ∧
        27 * (p.coeff 2).eval a = (r.eval a) ^ 2 * X.eval a ∧
        (((b2.eval a = 0 ∧ d2.eval a = 0) ∨
          (b2.eval a = 0 ∧ k1.eval a = 0) ∨
          (phi1.eval a = 0 ∧ d2.eval a = 0) ∨
          (phi1.eval a = 0 ∧ k1.eval a = 0)) ∧
        (r.eval a = 0 ∨ phi1.eval a = 0 ∨
          (b2.eval a = 0 ∧ b2.derivative.eval a = 0 ∧
           d2.eval a = 0 ∧ d2.derivative.eval a = 0 ∧
           k1.eval a ≠ 0))) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, _kOld, b2, d2, w2,
      hg, hgr, ht, hX, hY, hb1, hd1, hw1, hphi, hb2, hd2, hw2,
      hp2desc, hI4next, _hrowOld, hrootsOld⟩ :=
    S.terminalAfterLowerOneSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  obtain ⟨g0, r0, t0, X0, Yd0, b10, d10, w10, phi10, k1,
      hg0, hgr0, ht0, hX0, hY0, hb10, hd10, hw10, hphi10,
      hkdef0, hrow0, _hbranches0⟩ :=
    S.terminalKOneNextSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hgg : g0 = g := by
    apply mul_left_cancel₀ hH
    rw [← hg0, ← hg]
  have hrr : r0 = r := by
    apply mul_left_cancel₀ hH
    rw [← hgr0, ← hgr, hgg]
  have htt : t0 = t := by
    apply mul_left_cancel₀ hH
    rw [← ht0, ← ht]
  have hXX : X0 = X := by
    apply mul_left_cancel₀ hH
    rw [← hX0, ← hX, htt, hrr]
  have hYY : Yd0 = Yd := by
    apply mul_left_cancel₀ hH
    rw [← hY0, ← hY, hrr]
  have hbb : b10 = b1 := by
    apply mul_left_cancel₀ hH
    rw [← hb10, ← hb1, htt, hrr]
  have hdd : d10 = d1 := by
    apply mul_left_cancel₀ hH
    rw [← hd10, ← hd1, htt, hrr]
  have hww : w10 = w1 := by
    apply mul_left_cancel₀ hH
    rw [← hw10, ← hw1, htt, hrr]
  have hpp : phi10 = phi1 := by
    apply mul_left_cancel₀ hH
    rw [← hphi10, ← hphi, htt, hrr]
  have hkdef :
      let A0 := cubicANumerator68 t r
      let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
      let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r
      let c0 := terminalCShiftNumerator68 H A0 S.alpha
      let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
        S.epsilon S.eta
      let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
        S.alpha S.gamma S.epsilon S.eta
      k1 = terminalKDotNext68 H E0 V0 c0 R1 := by
    simpa only [htt, hrr, hbb, hdd, hww, hpp] using hkdef0
  have hrow :
      let A0 := cubicANumerator68 t r
      let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
      let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r
      let eDot := terminalEDerivativeNumerator68 H E0
      b1 * w1 * eDot - d1 * k1 = C j * H ^ 5 := by
    simpa only [htt, hrr, hbb, hdd, hww] using hrow0
  have hrowNext :
      let A0 := cubicANumerator68 t r
      let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
      let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r
      let eDot := terminalEDerivativeNumerator68 H E0
      H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4 := by
    dsimp only at hrow ⊢
    rw [hb2, hw2, hd2] at hrow
    apply mul_left_cancel₀ hH
    linear_combination hrow
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let c0 := terminalCShiftNumerator68 H A0 S.alpha
  let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
    S.epsilon S.eta
  let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
    S.alpha S.gamma S.epsilon S.eta
  let eDot := terminalEDerivativeNumerator68 H E0
  have hkcanonical : k1 = terminalKDotNext68 H E0 V0 c0 R1 := by
    simpa only [A0, C0, E0, c0, V0, R1] using hkdef
  have hW : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1]
    simp only [cubicWNumerator68]
  have hPhi : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H * phi1 := by
    dsimp only [A0, C0, E0, terminalScaledPhi68]
    rw [← hphi, ← hb1]
    simp only [cubicPhiNumerator68]
  refine ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
    hg, hgr, ht, hX, hY, hb1, hd1, hw1, hphi, hb2, hd2, hw2,
    hp2desc, hI4next, hrowNext, ?_⟩
  intro a ha
  have hcoords := terminalScaled_root_coordinates_68 H A0 b1 C0 E0 w1
    phi1 S.gamma S.epsilon a hW hPhi ha
  have hAeval : A0.eval a = -(1 / 12 : k) * (r.eval a) ^ 2 := by
    dsimp only [A0, cubicANumerator68]
    simp only [eval_sub, eval_mul, eval_pow, eval_C]
    have hta := congrArg (fun f : k[X] => f.eval a) hX
    simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, ha,
      zero_mul] at hta
    linear_combination (1 / 3 : k) * hta
  have hkroot : k1.eval a = H.derivative.eval a *
      (-(1 / 6 : k) * A0.eval a * phi1.eval a) := by
    have hw1root : w1.eval a = 0 := by
      have h := congrArg (fun f : k[X] => f.eval a) hw2
      simpa [ha] using h
    rw [hkcanonical]
    have hk0 := terminalKDotNext_eval_root_68 H A0 b1 C0 d1 E0 w1
      phi1 S.alpha S.gamma S.epsilon S.eta a ha hcoords.1 hcoords.2
    dsimp only [c0, V0, R1] at hk0
    rw [hcoords.1, hw1root] at hk0
    convert hk0 using 1 <;> ring
  have hsimple : H.derivative.eval a ≠ 0 :=
    nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hI4root : b2.eval a * phi1.eval a = 0 := by
    have h := congrArg (fun f : k[X] => f.eval a) hI4next
    simpa [ha] using h
  have hrowRoot : d2.eval a * k1.eval a = 0 := by
    have h := congrArg (fun f : k[X] => f.eval a) hrowNext
    simp only [eval_sub, eval_mul, eval_pow, eval_C, ha, zero_mul,
      mul_zero, zero_pow] at h
    have hz : -(d2.eval a * k1.eval a) = 0 := by simpa using h
    exact neg_eq_zero.mp hz
  have hI4der := terminalAfterLowerOne_I4_derivative_face_68
    H b2 phi1 w2 d2 a ha
  have hrowDer := terminalAfterLowerOne_lastRow_derivative_face_68
    H b2 w2 eDot d2 k1 j a ha
  have hcoordsOld := hrootsOld a ha
  refine ⟨hcoordsOld.1, hcoordsOld.2.1, ?_, ?_⟩
  · rcases mul_eq_zero.mp hI4root with hb | hphi <;>
      rcases mul_eq_zero.mp hrowRoot with hd | hk
    · exact Or.inl ⟨hb, hd⟩
    · exact Or.inr (Or.inl ⟨hb, hk⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hphi, hd⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hphi, hk⟩))
  · rcases eq_or_ne (r.eval a) 0 with hr0 | hrne
    · exact Or.inl hr0
    · right
      exact terminalAfterLowerOne_components_collapse_68
        (r.eval a) (A0.eval a) (b2.eval a) (phi1.eval a)
        (d2.eval a) (k1.eval a) (H.derivative.eval a)
        (b2.derivative.eval a) (d2.derivative.eval a)
        hrne hsimple hAeval hkroot hI4root hrowRoot
        (fun hb hd => hI4der hb hd hI4next)
        (fun hb hd => hrowDer hb hd hrowNext)

end TerminalAfterLowerOneComponentsSource68

end Max11DegreeRoutes
