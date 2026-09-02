import Sol68ScaleTwoAlignedNonsquareSourceFixedAssemblyScratch

/-! # Same-witness third-row refinement of the mixed allocation -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

section FixedMixedThird68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- First strict refinement of the fixed transverse allocation. -/
def terminalFixedMixedThird68
    (H r phi1 B D w eDot k1 : k[X]) (j : k) : Prop :=
  ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
    r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
    r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
    B.eval a = 0 ∧ k1.eval a = 0 ∧
    B.derivative.eval a * phi1.eval a +
      6 * H.derivative.eval a * w.eval a * D.eval a = 0 ∧
    D.eval a * k1.derivative.eval a = 0 ∧
    B.eval b * phi1.derivative.eval b +
      6 * H.derivative.eval b * w.eval b * D.eval b = 0 ∧
    H.derivative.eval b * B.eval b * w.eval b * eDot.eval b -
      (D.derivative.eval b * k1.eval b +
        D.eval b * k1.derivative.eval b) = 0 ∧
    ((k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
        B * w * eDot - D * k2 = C j * H ^ 3) ∨
      (D.eval b = 0 ∧ B.eval b = 0 ∧ ∃ B3 : k[X], B = H * B3 ∧
        B3 * phi1 + C 6 * w * D = 0 ∧
        D * k1 = H ^ 2 * (B3 * w * eDot - C j * H ^ 2)) ∨
      (D.eval b = 0 ∧ k1.eval b ≠ 0 ∧ B.eval b ≠ 0 ∧
        phi1.derivative.eval b = 0 ∧
        H.derivative.eval b * B.eval b * w.eval b * eDot.eval b =
          D.derivative.eval b * k1.eval b))

/-- A local source transport sufficient to delete the false `k1(a) ≠ 0`
branch.  It is stated independently of how the root was selected. -/
def terminalFixedMixedLowerTransport68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  ∃ b1 d1 C0 E0 : k[X],
    b1 = H * B ∧ d1 = H * D ∧
    C0 = cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r ∧
    E0 = cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r ∧
    C0 = C (1 / 3 : k) * (cubicANumerator68 t r) ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k)) ∧
    E0 = C (1 / 27 : k) * (cubicANumerator68 t r) ^ 3 +
      C (3 / 8 : k) * H * phi1 +
      H ^ 2 * (C (3 / 2 : k) * cubicANumerator68 t r * w -
        C (1 / 2 * S.gamma : k) * cubicANumerator68 t r) -
      C (3 / 4 * S.epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * b1) ^ 2 ∧
    terminalLowerZeroCleared68 H (cubicANumerator68 t r) b1 C0 d1 E0
      S.alpha S.gamma S.epsilon S.eta = 0

/-- The lower-zero source transport excludes a simultaneous first-order zero
of `B,D` carrying units `phi1,k1`. -/
theorem terminalFixedMixed_localKill_68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (hI4 : B * phi1 + C 6 * H * w * D = 0)
    (hrow : H * B * w * terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) - D * k1 = C j * H ^ 4)
    (T : terminalFixedMixedLowerTransport68 H S r t X0 Yd
      B D w phi1 k1)
    (a : k) (ha : H.eval a = 0) (hphi : phi1.eval a ≠ 0)
    (hk : k1.eval a ≠ 0) (hB0 : B.eval a = 0)
    (hB1 : B.derivative.eval a = 0) (hD0 : D.eval a = 0)
    (hD1 : D.derivative.eval a = 0) : False := by
  obtain ⟨b1, d1, C0, E0, hb1, hd1, hC0, hE0, hCshape, hEshape,
    hlower⟩ := T
  let A0 := cubicANumerator68 t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hrow' : H * B * w * eDot - D * k1 = C j * H ^ 4 := by
    dsimp only [eDot]
    rw [hE0]
    exact hrow
  have hboot := terminalAfterLowerOne_mixedRoot_bootstrap_68
    H B phi1 w D eDot k1 j a ha hphi hk hB0 hB1 hD0 hD1 hI4 hrow'
  let L : k[X] := X - C a
  have hLH : L ∣ H := by
    dsimp only [L]
    rw [dvd_iff_isRoot]
    exact ha
  obtain ⟨M, hHM⟩ := hLH
  have hMval : M.eval a = H.derivative.eval a := by
    have hder := congrArg (fun P : k[X] => P.derivative.eval a) hHM
    dsimp only [L] at hder
    simp only [derivative_mul, derivative_sub, derivative_X,
      derivative_C, eval_add, eval_mul, eval_sub, eval_one, eval_X,
      eval_C, sub_self, zero_mul, one_mul, add_zero] at hder
    simpa using hder.symm
  have hsimple : H.derivative.eval a ≠ 0 :=
    nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hMne : M.eval a ≠ 0 := by rw [hMval]; exact hsimple
  obtain ⟨BQ, hBQ⟩ := hboot.1
  obtain ⟨DQ, hDQ⟩ := hboot.2
  have hL : L ≠ 0 := by dsimp only [L]; exact X_sub_C_ne_zero a
  have hrowQ : L ^ 2 * M * BQ * w * eDot - DQ * k1 = C j * M ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 4 hL)
    rw [hHM, hBQ, hDQ] at hrow'
    linear_combination hrow'
  have hDprod : DQ.eval a * k1.eval a = -j * (M.eval a) ^ 4 := by
    have he := congrArg (fun P : k[X] => P.eval a) hrowQ
    dsimp only [L] at he
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C,
      eval_X, sub_self, zero_pow, zero_mul] at he
    linear_combination -he
  have hDQne : DQ.eval a ≠ 0 := by
    intro hDz
    rw [hDz, zero_mul] at hDprod
    exact (mul_ne_zero (neg_ne_zero.mpr hj) (pow_ne_zero 4 hMne)) hDprod.symm
  have hbLocal : b1 = L ^ 6 * (M * BQ) := by rw [hb1, hBQ, hHM]; ring
  have hdLocal : d1 = L ^ 5 * (M * DQ) := by rw [hd1, hDQ, hHM]; ring
  have hClocal : C0 = C (1 / 3 : k) * A0 ^ 2 +
      (L * M) ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k)) := by
    rw [← hHM]
    simpa only [A0] using hCshape
  have hElocal : E0 = C (1 / 27 : k) * A0 ^ 3 +
      C (3 / 8 : k) * (L * M) * phi1 +
      (L * M) ^ 2 * (C (3 / 2 : k) * A0 * w -
        C (1 / 2 * S.gamma : k) * A0) -
      C (3 / 4 * S.epsilon : k) * (L * M) ^ 3 +
      C (1 / 9 : k) * ((L * M) * (L ^ 6 * (M * BQ))) ^ 2 := by
    rw [← hHM, ← hbLocal]
    simpa only [A0] using hEshape
  have hlowerLocal : terminalLowerZeroCleared68 (L * M)
      A0 b1 C0 d1 E0 S.alpha S.gamma S.epsilon S.eta = 0 := by
    rw [← hHM]
    simpa only [A0] using hlower
  exact terminalLowerZero_mixedLocal_impossible_68
    M A0 b1 C0 d1 E0 (M * BQ) (M * DQ) phi1 w
    S.alpha S.gamma S.epsilon S.eta a hMne
    (by simp only [eval_mul]; exact mul_ne_zero hMne hDQne) hphi
    (by simpa only [L] using hbLocal)
    (by simpa only [L] using hdLocal)
    (by simpa only [L] using hClocal)
    (by simpa only [L] using hElocal)
    (by simpa only [L] using hlowerLocal)

/-- Exact same-witness refinement of an already selected mixed packet. -/
theorem terminalFixedMixed_third_68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (hdeg : H.natDegree = 2) (hj : j ≠ 0)
    (hI4 : B * phi1 + C 6 * H * w * D = 0)
    (hrow : H * B * w * terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) - D * k1 = C j * H ^ 4)
    (T : terminalFixedMixedLowerTransport68 H S r t X0 Yd
      B D w phi1 k1)
    (hmixed : terminalFixedCoordinateMixed68 H r phi1 B D w
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) k1) :
    terminalFixedMixedThird68 H r phi1 B D w
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) k1 j := by
  let eDot := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb,
    hBa, hfaceIa, hsplitDa, hfaceRa, hfaceIb, hfaceRb, hsplitDb⟩ := hmixed
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hface4a : D.derivative.eval a * k1.eval a +
      D.eval a * k1.derivative.eval a = 0 := by
    linear_combination -hfaceRa +
      H.derivative.eval a * w.eval a * eDot.eval a * hBa
  have hk1a : k1.eval a = 0 := by
    by_contra hkne
    have hDa : D.eval a = 0 := hsplitDa.resolve_right hkne
    have hBda : B.derivative.eval a = 0 := by
      have hz : B.derivative.eval a * phi1.eval a = 0 := by
        linear_combination hfaceIa -
          6 * H.derivative.eval a * w.eval a * hDa
      exact (mul_eq_zero.mp hz).resolve_right hpa
    have hDda : D.derivative.eval a = 0 := by
      have hz : D.derivative.eval a * k1.eval a = 0 := by
        linear_combination hface4a - k1.derivative.eval a * hDa
      exact (mul_eq_zero.mp hz).resolve_right hkne
    exact terminalFixedMixed_localKill_68 H S r t X0 Yd B D w phi1 k1
      hdeg hj hI4 hrow T a ha hpa hkne hBa hBda hDa hDda
  have hDk1a : D.eval a * k1.derivative.eval a = 0 := by
    linear_combination hface4a - D.derivative.eval a * hk1a
  have htri :
      (k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
        B * w * eDot - D * k2 = C j * H ^ 3) ∨
      (D.eval b = 0 ∧ B.eval b = 0 ∧ ∃ B3 : k[X], B = H * B3 ∧
        B3 * phi1 + C 6 * w * D = 0 ∧
        D * k1 = H ^ 2 * (B3 * w * eDot - C j * H ^ 2)) ∨
      (D.eval b = 0 ∧ k1.eval b ≠ 0 ∧ B.eval b ≠ 0 ∧
        phi1.derivative.eval b = 0 ∧
        H.derivative.eval b * B.eval b * w.eval b * eDot.eval b =
          D.derivative.eval b * k1.eval b) := by
    by_cases hkb : k1.eval b = 0
    · left
      obtain ⟨k2, hk2⟩ := dvd_of_two_simple_root_evals_68 H k1 hdeg
        hsimple a b hab ha hb hk1a hkb
      refine ⟨hkb, k2, hk2, ?_⟩
      apply mul_left_cancel₀ hH
      rw [hk2] at hrow
      linear_combination hrow
    · have hDb : D.eval b = 0 := hsplitDb.resolve_right hkb
      by_cases hBb : B.eval b = 0
      · right
        left
        obtain ⟨B3, hB3⟩ := dvd_of_two_simple_root_evals_68 H B hdeg
          hsimple a b hab ha hb hBa hBb
        refine ⟨hDb, hBb, B3, hB3, ?_, ?_⟩
        · apply mul_left_cancel₀ hH
          rw [hB3] at hI4
          linear_combination hI4
        · rw [hB3] at hrow
          linear_combination -hrow
      · right
        right
        have hphidb : phi1.derivative.eval b = 0 := by
          have hz : B.eval b * phi1.derivative.eval b = 0 := by
            linear_combination hfaceIb -
              6 * H.derivative.eval b * w.eval b * hDb
          exact (mul_eq_zero.mp hz).resolve_left hBb
        refine ⟨hDb, hkb, hBb, hphidb, ?_⟩
        linear_combination hfaceRb + k1.derivative.eval b * hDb
  exact ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hBa, hk1a,
    hfaceIa, hDk1a, hfaceIb, hfaceRb, htri⟩

end FixedMixedThird68

end Max11DegreeRoutes
