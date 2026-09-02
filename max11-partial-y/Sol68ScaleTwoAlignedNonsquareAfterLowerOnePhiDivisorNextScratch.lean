import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorScratch

/-! # The next lower-zero coefficient on the global phi divisor -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section PhiDivisorNextAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The first derivative of the once-cancelled lower-zero row still cancels.
The second derivative is the first informative coefficient; it factors into
two exact scalar faces. -/
theorem terminalLowerZeroOne_secondDerivative_eval_root_68
    (H A B D phi w : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) :
    let C0 := C (1 / 3 : k) * A ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
    let E := C (1 / 27 : k) * A ^ 3 +
      H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
        C (1 / 2 * gamma : k) * A) -
      C (3 / 4 * epsilon : k) * H ^ 3 + C (1 / 9 : k) * H ^ 4 * B ^ 2
    (terminalLowerZeroOne68 H A B C0 D E
      alpha gamma epsilon eta).derivative.derivative.eval a =
        (H.derivative.eval a) ^ 3 *
          (A.eval a * B.eval a - 3 * D.eval a) *
          (phi.eval a + 2 * A.eval a * w.eval a) := by
  dsimp only
  simp only [terminalLowerZeroOne68, terminalLowerZeroSOne68,
    terminalLowerZeroUOne68, terminalLowerZeroDDOne68,
    terminalLowerZeroUDOne68, terminalLowerZeroCDot68,
    terminalLowerZeroTDot68, terminalLowerOneTNumerator68,
    terminalEDerivativeNumerator68, terminalVDerivativeNumerator68,
    terminalVNumerator68, derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
    C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  ring

theorem terminalLowerZeroOne_next_split_68
    (H A B D phi w : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hh : H.derivative.eval a ≠ 0)
    (hlower :
      let C0 := C (1 / 3 : k) * A ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
      let E := C (1 / 27 : k) * A ^ 3 +
        H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
          C (1 / 2 * gamma : k) * A) -
        C (3 / 4 * epsilon : k) * H ^ 3 + C (1 / 9 : k) * H ^ 4 * B ^ 2
      terminalLowerZeroOne68 H A B C0 D E
        alpha gamma epsilon eta = 0) :
    A.eval a * B.eval a - 3 * D.eval a = 0 ∨
      phi.eval a + 2 * A.eval a * w.eval a = 0 := by
  dsimp only at hlower
  have hzero : (terminalLowerZeroOne68 H A B
      (C (1 / 3 : k) * A ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))) D
      (C (1 / 27 : k) * A ^ 3 +
        H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
          C (1 / 2 * gamma : k) * A) -
        C (3 / 4 * epsilon : k) * H ^ 3 + C (1 / 9 : k) * H ^ 4 * B ^ 2)
      alpha gamma epsilon eta).derivative.derivative.eval a = 0 := by
    rw [hlower, derivative_zero, derivative_zero, eval_zero]
  rw [terminalLowerZeroOne_secondDerivative_eval_root_68 H A B D phi w
    alpha gamma epsilon eta a ha] at hzero
  rcases mul_eq_zero.mp hzero with hleft | hright
  · left
    exact (mul_eq_zero.mp hleft).resolve_left (pow_ne_zero 3 hh)
  · exact Or.inr hright

end PhiDivisorNextAlgebra68

section PhiDivisorNextSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing form of the first informative lower-zero coefficient on the
global `H | phi₁` family.  Together with
`terminalAfterLowerOnePhiDivisorPacket`, this retains the twice-divided I4 and
terminal rows and adds the exact two-face split at every core root. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorNextPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t X Yd phi1 k1 b2 d2 w2 : k[X]),
      p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4) ∧
      (H ∣ phi1 →
        ∃ phi2 : k[X], phi1 = H * phi2 ∧
          b2 * phi2 + (6 : k[X]) * w2 * d2 = 0 ∧
          (let A0 := cubicANumerator68 t r
           ∀ a : k, H.eval a = 0 →
             A0.eval a * b2.eval a - 3 * d2.eval a = 0 ∨
             phi2.eval a + 2 * A0.eval a * w2.eval a = 0)) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
      hg, hgr, ht, hX, hY, hb1, hd1, hw1, hphi, hb2, hd2, hw2,
      _hp2desc, hI4next, hrowNext, _hroots⟩ :=
    S.terminalAfterLowerOneSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
    ht, hX, hY, hrowNext, ?_⟩
  intro hphiDvd
  obtain ⟨phi2, hphi2⟩ := hphiDvd
  have hI4q : b2 * phi2 + (6 : k[X]) * w2 * d2 = 0 := by
    rw [hphi2] at hI4next
    apply mul_left_cancel₀ hH
    linear_combination hI4next
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  have hW1 : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1]
    simp only [cubicWNumerator68]
  have hW2 : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w2 := by
    rw [hW1, hw2]
    ring
  have hCshape : C0 = C (1 / 3 : k) * A0 ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w2 - C (3 / 2 * S.gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hm := congrArg (algebraMap k[X] (RatFunc k)) hW2
    dsimp only [terminalScaledW68] at hm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hm ⊢
    linear_combination (9 / 4 : RatFunc k) * hm
  have hPhi1 : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H * phi1 := by
    dsimp only [A0, C0, E0, terminalScaledPhi68]
    rw [← hphi, ← hb1]
    simp only [cubicPhiNumerator68]
  have hPhi2 : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H ^ 2 * phi2 := by
    rw [hPhi1, hphi2]
    ring
  have hEshape : E0 = C (1 / 27 : k) * A0 ^ 3 +
      H ^ 2 * (C (3 / 8 : k) * phi2 + C (3 / 2 : k) * A0 * w2 -
        C (1 / 2 * S.gamma : k) * A0) -
      C (3 / 4 * S.epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * H ^ 4 * b2 ^ 2 := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hPhi2' := hPhi2
    rw [hb2] at hPhi2'
    have hPm := congrArg (algebraMap k[X] (RatFunc k)) hPhi2'
    have hCm := congrArg (algebraMap k[X] (RatFunc k)) hCshape
    dsimp only [terminalScaledPhi68] at hPm
    simp only [map_add, map_sub, map_neg, map_mul, map_pow,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one] at hPm hCm ⊢
    linear_combination (3 / 8 : RatFunc k) * hPm +
      (2 / 3 * algebraMap k[X] (RatFunc k) A0) * hCm
  have htransport := S.terminalLowerZeroClearedTransport_source (H := H)
    hp hp6 hg hgr ht hX hY
  obtain ⟨hAred, hBred, hCred, hDred, hEred⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
  have hbred : terminalGReducedB68 r X Yd = b1 := by
    apply mul_left_cancel₀ hH
    rw [← hBred, ← hb1]
  have hdred : terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2) =
      d1 := by
    apply mul_left_cancel₀ hH
    rw [← hDred, ← hd1]
  have hlower : terminalLowerZeroCleared68 H A0 b1 C0 d1 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    simpa only [A0, C0, E0, ← hAred, hbred, ← hCred, hdred, ← hEred]
      using htransport
  have hfactor := terminalLowerZero_factor_one_68 H A0 b1 C0 d1 E0
    b2 d2 S.alpha S.gamma S.epsilon S.eta hb2 hd2
  have hlower1 : terminalLowerZeroOne68 H A0 b2 C0 d2 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    have hz : H * terminalLowerZeroOne68 H A0 b2 C0 d2 E0
        S.alpha S.gamma S.epsilon S.eta = 0 := by rw [← hfactor, hlower]
    exact (mul_eq_zero.mp hz).resolve_left hH
  refine ⟨phi2, hphi2, hI4q, ?_⟩
  dsimp only
  intro a ha
  have hlowshape : terminalLowerZeroOne68 H A0 b2
      (C (1 / 3 : k) * A0 ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w2 - C (3 / 2 * S.gamma : k))) d2
      (C (1 / 27 : k) * A0 ^ 3 +
        H ^ 2 * (C (3 / 8 : k) * phi2 + C (3 / 2 : k) * A0 * w2 -
          C (1 / 2 * S.gamma : k) * A0) -
        C (3 / 4 * S.epsilon : k) * H ^ 3 +
        C (1 / 9 : k) * H ^ 4 * b2 ^ 2)
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    rw [← hCshape, ← hEshape]
    exact hlower1
  exact terminalLowerZeroOne_next_split_68 H A0 b2 d2 phi2 w2
    S.alpha S.gamma S.epsilon S.eta a ha (hsimple a ha) hlowshape

end PhiDivisorNextSource68

end Max11DegreeRoutes
