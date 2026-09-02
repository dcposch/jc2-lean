import Sol68ScaleTwoAlignedNonsquareSourceFixedMixedAssemblyScratch
import Fable68ScaleTwoAlignedNonsquareMixedNextScratch

/-! # Same-witness fourth-row mixed reduction -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 24000000

section FixedMixedFourth68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- Exact finite fourth-row packet on the fixed mixed roots. -/
def terminalFixedMixedFourth68
    (H r phi1 B D w eDot k1 : k[X]) (j : k) : Prop :=
  ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
    r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
    r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
    B.eval a = 0 ∧ k1.eval a = 0 ∧ D.eval a = 0 ∧
    B.derivative.eval a = 0 ∧ D.derivative.eval a = 0 ∧
    B.eval b * phi1.derivative.eval b +
      6 * H.derivative.eval b * w.eval b * D.eval b = 0 ∧
    H.derivative.eval b * B.eval b * w.eval b * eDot.eval b -
      (D.derivative.eval b * k1.eval b +
        D.eval b * k1.derivative.eval b) = 0 ∧
    (r.eval b ^ 2 * B.eval b + 36 * D.eval b) *
      (6 * phi1.derivative.eval b -
        r.eval b ^ 2 * w.eval b * H.derivative.eval b) = 0 ∧
    15552 * eDot.eval b = H.derivative.eval b * r.eval b ^ 6 ∧
    ((k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
        B * w * eDot - D * k2 = C j * H ^ 3) ∨
      (D.eval b = 0 ∧ B.eval b = 0 ∧ ∃ B3 E1 : k[X],
        B = H * B3 ∧ D = H * E1 ∧
        B3 * phi1 + C 6 * H * w * E1 = 0 ∧
        E1 * k1 = H * B3 * w * eDot - C j * H ^ 3) ∨
      (D.eval b = 0 ∧ k1.eval b ≠ 0 ∧ B.eval b ≠ 0 ∧
        phi1.derivative.eval b = 0 ∧ w.eval b = 0 ∧
        D.derivative.eval b = 0 ∧
        ∃ E2 : k[X], D = H ^ 2 * E2 ∧
          B * phi1 + C 6 * H ^ 3 * w * E2 = 0 ∧
          B * w * eDot - H * E2 * k1 = C j * H ^ 3 ∧
          B.eval b * w.derivative.eval b * eDot.eval b =
            H.derivative.eval b * E2.eval b * k1.eval b))

/-- The once-cancelled lower-zero coefficient refines the exact fixed third
packet without changing its roots or quotient witnesses. -/
theorem terminalFixedMixed_fourth_68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (hX : C 3 * t - r ^ 2 = H * X0)
    (hI4 : B * phi1 + C 6 * H * w * D = 0)
    (hrow : H * B * w * terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) - D * k1 = C j * H ^ 4)
    (T : terminalFixedMixedLowerTransport68 H S r t X0 Yd
      B D w phi1 k1)
    (hthird : terminalFixedMixedThird68 H r phi1 B D w
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) k1 j) :
    terminalFixedMixedFourth68 H r phi1 B D w
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) k1 j := by
  obtain ⟨b1, d1, C0, E0, hb1, hd1, hC0, hE0, hCshape, hEshape,
    hlower⟩ := T
  let A0 := cubicANumerator68 t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have heDotEq : eDot = terminalEDerivativeNumerator68 H
      (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r) := by
    dsimp only [eDot]
    rw [hE0]
  have hrow' : H * B * w * eDot - D * k1 = C j * H ^ 4 := by
    rw [heDotEq]
    exact hrow
  obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hBa, hk1a,
    _hfaceIa, _hDk1a, hfaceIb, hfaceRb, _htri3⟩ := hthird
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hEshape2 : E0 = C (1 / 27 : k) * A0 ^ 3 +
      C (3 / 8 : k) * H * phi1 +
      H ^ 2 * (C (3 / 2 : k) * A0 * w -
        C (1 / 2 * S.gamma : k) * A0) -
      C (3 / 4 * S.epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * (H * B)) ^ 2 := by
    rw [← hb1]
    simpa only [A0] using hEshape
  have hfactor := mixedLowerZero_factor_one_68 H A0 b1 C0 d1 E0 B D
    S.alpha S.gamma S.epsilon S.eta hb1 hd1
  have hRone : mixedLowerZeroOne68 H A0 B C0 D E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    have hz : H * mixedLowerZeroOne68 H A0 B C0 D E0
        S.alpha S.gamma S.epsilon S.eta = 0 := by
      rw [← hfactor]
      simpa only [A0] using hlower
    exact (mul_eq_zero.mp hz).resolve_left hH
  have hAroot : ∀ z : k, H.eval z = 0 →
      A0.eval z = -(1 / 12 : k) * r.eval z ^ 2 := by
    intro z hz
    have he := congrArg (fun P : k[X] => P.eval z) hX
    simp only [eval_mul, eval_sub, eval_pow, eval_ofNat, hz, zero_mul] at he
    have hC3 : (C (3 : k)).eval z = 3 := by simp
    rw [hC3] at he
    dsimp only [A0, cubicANumerator68]
    simp only [eval_sub, eval_mul, eval_pow, eval_C]
    linear_combination (1 / 3 : k) * he
  have hRoneDa : (mixedLowerZeroOne68 H A0 B C0 D E0
      S.alpha S.gamma S.epsilon S.eta).derivative.eval a = 0 := by
    rw [hRone, derivative_zero, eval_zero]
  rw [hCshape, hEshape2, mixedLowerZeroOne_derivative_factor_68
    H A0 B D phi1 w S.alpha S.gamma S.epsilon S.eta a ha] at hRoneDa
  have hDa : D.eval a = 0 := by
    have h5 : phi1.eval a * H.derivative.eval a ^ 2 * D.eval a = 0 := by
      linear_combination (-2 / 5 : k) * hRoneDa +
        (1 / 5 : k) * phi1.eval a * H.derivative.eval a ^ 2 *
          A0.eval a * hBa
    rcases mul_eq_zero.mp h5 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hpa
      · exact absurd h' (pow_ne_zero 2 (hsimple a ha))
    · exact h
  have hBda : B.derivative.eval a = 0 := by
    have hder := congrArg (fun P : k[X] => P.derivative.eval a) hI4
    simp only [derivative_add, derivative_mul, derivative_C, derivative_zero,
      eval_add, eval_mul, eval_C, eval_zero, ha, hBa, hDa, zero_mul,
      mul_zero, zero_add, add_zero] at hder
    have hz : B.derivative.eval a * phi1.eval a = 0 := by
      simpa only [eval_ofNat, mul_assoc] using hder
    exact (mul_eq_zero.mp hz).resolve_right hpa
  have hRoneDDa : (mixedLowerZeroOne68 H A0 B C0 D E0
      S.alpha S.gamma S.epsilon S.eta).derivative.derivative.eval a = 0 := by
    rw [hRone, derivative_zero, derivative_zero, eval_zero]
  rw [hCshape, hEshape2, mixedLowerZeroOne_secondDerivative_rRoot_68
    H A0 B D phi1 w S.alpha S.gamma S.epsilon S.eta a ha hBa hDa]
    at hRoneDDa
  have hDda : D.derivative.eval a = 0 := by
    have h3 : phi1.eval a * H.derivative.eval a ^ 2 *
        D.derivative.eval a = 0 := by
      linear_combination (-1 / 3 : k) * hRoneDDa +
        (1 / 3 : k) * phi1.eval a * H.derivative.eval a ^ 2 *
          A0.eval a * hBda
    rcases mul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hpa
      · exact absurd h' (pow_ne_zero 2 (hsimple a ha))
    · exact h
  have hRoneDDb : (mixedLowerZeroOne68 H A0 B C0 D E0
      S.alpha S.gamma S.epsilon S.eta).derivative.derivative.eval b = 0 := by
    rw [hRone, derivative_zero, derivative_zero, eval_zero]
  rw [hCshape, hEshape2, mixedLowerZeroOne_secondDerivative_phiRoot_68
    H A0 B D phi1 w S.alpha S.gamma S.epsilon S.eta b hb hpb]
    at hRoneDDb
  have hXY := (mul_eq_zero.mp hRoneDDb).resolve_left
    (pow_ne_zero 2 (hsimple b hb))
  rw [hAroot b hb] at hXY
  have hfaceB : (r.eval b ^ 2 * B.eval b + 36 * D.eval b) *
      (6 * phi1.derivative.eval b -
        r.eval b ^ 2 * w.eval b * H.derivative.eval b) = 0 := by
    linear_combination (-72 : k) * hXY
  have hE0b : E0.eval b = (1 / 27 : k) * A0.eval b ^ 3 := by
    have he := congrArg (fun P : k[X] => P.eval b) hEshape2
    simpa only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, hb,
      zero_mul, mul_zero, zero_pow, zero_add, add_zero, sub_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using he
  have heDotPin : 15552 * eDot.eval b =
      H.derivative.eval b * r.eval b ^ 6 := by
    have he1 : eDot.eval b =
        -(3 : k) * (H.derivative.eval b * E0.eval b) := by
      dsimp only [eDot, terminalEDerivativeNumerator68]
      simp only [eval_sub, eval_mul, eval_C, hb, zero_mul]
      ring
    rw [he1, hE0b, hAroot b hb]
    ring
  have hDkb : D.eval b * k1.eval b = 0 := by
    have he := congrArg (fun P : k[X] => P.eval b) hrow'
    simp only [eval_sub, eval_mul, eval_pow, eval_C, hb, zero_mul,
      zero_pow] at he
    have hz : -(D.eval b * k1.eval b) = 0 := by simpa using he
    exact neg_eq_zero.mp hz
  have htri4 :
      (k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
        B * w * eDot - D * k2 = C j * H ^ 3) ∨
      (D.eval b = 0 ∧ B.eval b = 0 ∧ ∃ B3 E1 : k[X],
        B = H * B3 ∧ D = H * E1 ∧
        B3 * phi1 + C 6 * H * w * E1 = 0 ∧
        E1 * k1 = H * B3 * w * eDot - C j * H ^ 3) ∨
      (D.eval b = 0 ∧ k1.eval b ≠ 0 ∧ B.eval b ≠ 0 ∧
        phi1.derivative.eval b = 0 ∧ w.eval b = 0 ∧
        D.derivative.eval b = 0 ∧
        ∃ E2 : k[X], D = H ^ 2 * E2 ∧
          B * phi1 + C 6 * H ^ 3 * w * E2 = 0 ∧
          B * w * eDot - H * E2 * k1 = C j * H ^ 3 ∧
          B.eval b * w.derivative.eval b * eDot.eval b =
            H.derivative.eval b * E2.eval b * k1.eval b) := by
    by_cases hkb : k1.eval b = 0
    · left
      obtain ⟨k2, hk2⟩ := dvd_of_two_simple_root_evals_68 H k1 hdeg
        hsimple a b hab ha hb hk1a hkb
      refine ⟨hkb, k2, hk2, ?_⟩
      apply mul_left_cancel₀ hH
      rw [hk2] at hrow'
      linear_combination hrow'
    · have hDb : D.eval b = 0 := (mul_eq_zero.mp hDkb).resolve_right hkb
      by_cases hBb : B.eval b = 0
      · right
        left
        obtain ⟨B3, hB3⟩ := dvd_of_two_simple_root_evals_68 H B hdeg
          hsimple a b hab ha hb hBa hBb
        obtain ⟨E1, hE1⟩ := dvd_of_two_simple_root_evals_68 H D hdeg
          hsimple a b hab ha hb hDa hDb
        refine ⟨hDb, hBb, B3, E1, hB3, hE1, ?_, ?_⟩
        · apply mul_left_cancel₀ hH
          rw [hB3, hE1] at hI4
          linear_combination hI4
        · apply mul_left_cancel₀ hH
          rw [hB3, hE1] at hrow'
          linear_combination -hrow'
      · right
        right
        have hphidb : phi1.derivative.eval b = 0 := by
          have hz : B.eval b * phi1.derivative.eval b = 0 := by
            linear_combination hfaceIb -
              6 * H.derivative.eval b * w.eval b * hDb
          exact (mul_eq_zero.mp hz).resolve_left hBb
        have hwb : w.eval b = 0 := by
          have h6 : r.eval b ^ 4 * B.eval b * H.derivative.eval b *
              w.eval b = 0 := by
            linear_combination (-1 : k) * hfaceB +
              (6 * r.eval b ^ 2 * B.eval b + 216 * D.eval b) * hphidb +
              (-36 : k) * r.eval b ^ 2 * w.eval b *
                H.derivative.eval b * hDb
          rcases mul_eq_zero.mp h6 with h | h
          · rcases mul_eq_zero.mp h with h' | h'
            · rcases mul_eq_zero.mp h' with h'' | h''
              · exact absurd h'' (pow_ne_zero 4 hrb)
              · exact absurd h'' hBb
            · exact absurd h' (hsimple b hb)
          · exact h
        have hDdb : D.derivative.eval b = 0 := by
          have hfaceRbDot : H.derivative.eval b * B.eval b * w.eval b *
                eDot.eval b -
              (D.derivative.eval b * k1.eval b +
                D.eval b * k1.derivative.eval b) = 0 := by
            rw [heDotEq]
            exact hfaceRb
          have hz : D.derivative.eval b * k1.eval b = 0 := by
            linear_combination (-1 : k) * hfaceRbDot +
              H.derivative.eval b * B.eval b * eDot.eval b * hwb +
              (-1 : k) * k1.derivative.eval b * hDb
          exact (mul_eq_zero.mp hz).resolve_right hkb
        obtain ⟨E1, hE1⟩ := dvd_of_two_simple_root_evals_68 H D hdeg
          hsimple a b hab ha hb hDa hDb
        have hEroot : ∀ z : k, H.eval z = 0 →
            D.derivative.eval z = H.derivative.eval z * E1.eval z := by
          intro z hz
          have he := congrArg (fun P : k[X] => P.derivative.eval z) hE1
          simpa only [derivative_mul, eval_add, eval_mul, hz, zero_mul,
            add_zero] using he
        have hE1a : E1.eval a = 0 := by
          have he := hEroot a ha
          rw [hDda] at he
          exact (mul_eq_zero.mp he.symm).resolve_left (hsimple a ha)
        have hE1b : E1.eval b = 0 := by
          have he := hEroot b hb
          rw [hDdb] at he
          exact (mul_eq_zero.mp he.symm).resolve_left (hsimple b hb)
        obtain ⟨E2, hE2⟩ := dvd_of_two_simple_root_evals_68 H E1 hdeg
          hsimple a b hab ha hb hE1a hE1b
        have hDsq : D = H ^ 2 * E2 := by rw [hE1, hE2]; ring
        have hI4red : B * phi1 + C 6 * H ^ 3 * w * E2 = 0 := by
          rw [hDsq] at hI4
          linear_combination hI4
        have hrowRed : B * w * eDot - H * E2 * k1 = C j * H ^ 3 := by
          apply mul_left_cancel₀ hH
          rw [hDsq] at hrow'
          linear_combination hrow'
        have hface3 : B.eval b * w.derivative.eval b * eDot.eval b =
            H.derivative.eval b * E2.eval b * k1.eval b := by
          have he := congrArg (fun P : k[X] => P.derivative.eval b) hrowRed
          simp only [derivative_sub, derivative_mul, derivative_pow,
            derivative_C, eval_sub, eval_add, eval_mul, eval_pow, eval_C,
            eval_ofNat, hb, hwb, zero_mul, mul_zero, zero_add, add_zero,
            sub_zero, zero_sub, zero_pow] at he
          linear_combination he
        exact ⟨hDb, hkb, hBb, hphidb, hwb, hDdb, E2, hDsq,
          hI4red, hrowRed, hface3⟩
  rw [heDotEq] at heDotPin htri4
  exact ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hBa, hk1a, hDa,
    hBda, hDda, hfaceIb, hfaceRb, hfaceB, heDotPin, htri4⟩

def terminalFixedMixedFourthAssemblyResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  H ∣ r ∨
    terminalFixedMixedFourth68 H r phi1 B D w
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) k1 j ∨
    terminalFixedPhiFinalAssembly68 H S r t X0 Yd B D w phi1 k1

/-- Source-facing replacement of the third-row mixed sibling by the fixed
fourth-row packet. -/
theorem NonsquareAlignedSourceCurveData68.fixedMixedFourthAssemblyPacket
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ r t X0 Yd B D w phi1 k1 : k[X],
      terminalFixedMixedLowerTransport68 H S r t X0 Yd B D w phi1 k1 ∧
      terminalFixedMixedFourthAssemblyResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
      _hp4, hX, _hY, hI4, hrow, _hdvd, hLower, hres⟩ :=
    S.fixedMixedAssemblyPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  refine ⟨r, t, X0, Yd, B, D, w, phi1, k1, hLower, ?_⟩
  rcases hres with hr | hthird | hphi
  · exact Or.inl hr
  · exact Or.inr (Or.inl (terminalFixedMixed_fourth_68 H S
      r t X0 Yd B D w phi1 k1 hdeg hj hX hI4 hrow hLower hthird))
  · exact Or.inr (Or.inr hphi)

end FixedMixedFourth68

section NormalizedFixedMixedFourth68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem normalized68ScaleTwo_alignedNonsquare_fixedMixedFourthAssembly
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let _inst : NonsquarePolynomial46 H := ⟨hnsq⟩
    ∃ (j : k) (S : NonsquareAlignedSourceCurveData68 H p q j),
      j ≠ 0 ∧
      ∃ r t X0 Yd B D w phi1 k1 : k[X],
        terminalFixedMixedLowerTransport68 H S r t X0 Yd B D w phi1 k1 ∧
        terminalFixedMixedFourthAssemblyResidual68 H S
          r t X0 Yd B D w phi1 k1 := by
  dsimp only
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  have haligned' : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0 := by
    simpa only [p, q] using haligned
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDsrc : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [p, q, bivariateJacobian, xderiv, GCD369SourceXDeriv]
      using hjac
  obtain ⟨S⟩ := nonsquareAlignedSourceCurveData68 (H := H) p q j
    hp hq hp6' hq8' haligned' hDsrc
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1, hLower, hres⟩ :=
    S.fixedMixedFourthAssemblyPacket (H := H) hHdegree hp hq hp6' hq8'
      haligned' hjac hj
  exact ⟨j, S, hj, r, t, X0, Yd, B, D, w, phi1, k1, hLower, hres⟩

end NormalizedFixedMixedFourth68

end Max11DegreeRoutes
