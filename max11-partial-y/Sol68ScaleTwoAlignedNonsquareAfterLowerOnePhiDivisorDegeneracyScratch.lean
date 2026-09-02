import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorNextScratch

/-! # Degeneracy packet on the global phi divisor -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section PhiDivisorDegeneracyAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalPhiDivisorDegeneracy68
    (A b d w phi e k2 hprime : k) : Prop :=
  ((A * b - 3 * d = 0) ∧ (phi + 2 * A * w = 0) ∧
      (A = 0 ∨ b = 0 ∨ hprime * A ^ 2 * w + 3 * k2 = 0)) ∨
    ((A * b - 3 * d = 0) ∧ b = 0 ∧ d = 0) ∨
    ((phi + 2 * A * w = 0) ∧ w = 0 ∧ phi = 0 ∧
      (d = 0 ∨ k2 = 0))

/-- Divided I4 turns either lower-zero face into a coordinate zero or the
common face.  The divided terminal row then gives the exact residual load on
the common face, and `d*k₂=0` on the zero-`w` face. -/
theorem terminalPhiDivisor_degeneracy_68
    (A b d w phi e k2 hprime : k)
    (hI4 : b * phi + 6 * w * d = 0)
    (hrow : b * w * e - d * k2 = 0)
    (he : e = -(1 / 9 : k) * hprime * A ^ 3)
    (hface : A * b - 3 * d = 0 ∨ phi + 2 * A * w = 0) :
    terminalPhiDivisorDegeneracy68 A b d w phi e k2 hprime := by
  rcases hface with hF | hG
  · have hbG : b * (phi + 2 * A * w) = 0 := by
      linear_combination hI4 + 2 * w * hF
    rcases mul_eq_zero.mp hbG with hb0 | hG
    · have hd0 : d = 0 := by
        have hF0 : A * 0 - 3 * d = 0 := by simpa [hb0] using hF
        linear_combination (-1 / 3 : k) * hF0
      exact Or.inr (Or.inl ⟨hF, hb0, hd0⟩)
    · left
      refine ⟨hF, hG, ?_⟩
      rw [he] at hrow
      have hload : A * b * (hprime * A ^ 2 * w + 3 * k2) = 0 := by
        linear_combination -9 * hrow + 3 * k2 * hF
      rcases mul_eq_zero.mp hload with hAb | hload
      · rcases mul_eq_zero.mp hAb with hA | hb
        · exact Or.inl hA
        · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hload)
  · have hwF : w * (A * b - 3 * d) = 0 := by
      linear_combination (-1 / 2 : k) * hI4 + b / 2 * hG
    rcases mul_eq_zero.mp hwF with hw0 | hF
    · right; right
      have hphi0 : phi = 0 := by rw [hw0, mul_zero, add_zero] at hG; exact hG
      have hdk : d * k2 = 0 := by
        rw [hw0, mul_zero, zero_mul, zero_sub] at hrow
        linear_combination -hrow
      exact ⟨hG, hw0, hphi0, mul_eq_zero.mp hdk⟩
    · left
      refine ⟨hF, hG, ?_⟩
      rw [he] at hrow
      have hload : A * b * (hprime * A ^ 2 * w + 3 * k2) = 0 := by
        linear_combination -9 * hrow + 3 * k2 * hF
      rcases mul_eq_zero.mp hload with hAb | hload
      · rcases mul_eq_zero.mp hAb with hA | hb
        · exact Or.inl hA
        · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hload)

end PhiDivisorDegeneracyAlgebra68

section PhiDivisorDegeneracySource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Full source-facing sharp packet on `H | phi₁`: both invariant rows are
divided, and every simple core root lies in one of the three exact degeneracy
components recorded by `terminalPhiDivisorDegeneracy68`. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorDegeneracyPacket
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
      (H ∣ phi1 →
        ∃ phi2 k2 : k[X],
          phi1 = H * phi2 ∧ k1 = H * k2 ∧
          b2 * phi2 + (6 : k[X]) * w2 * d2 = 0 ∧
          (let A0 := cubicANumerator68 t r
           let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) ∧
          (let A0 := cubicANumerator68 t r
           let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
             (p.coeff 3) t r
           let eDot := terminalEDerivativeNumerator68 H E0
           ∀ a : k, H.eval a = 0 →
             terminalPhiDivisorDegeneracy68
               (A0.eval a) (b2.eval a) (d2.eval a) (w2.eval a)
               (phi2.eval a) (eDot.eval a) (k2.eval a)
               (H.derivative.eval a))) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, hg, hgr, ht, hX, hY, hb1, hd1,
      hw1, hroot, _hdvdW, _hsqW⟩ :=
    S.terminalLowerOneSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  obtain ⟨g0, r0, t0, X0, Yd0, b10, d10, w10, phi1, k1,
      hg0, hgr0, ht0, hX0, hY0, hb10, hd10, hw10, hphi10,
      hkdef0, hrow0, _hselectors0⟩ :=
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
  have hphi : cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) t r S.gamma S.epsilon = H * phi1 := by
    simpa only [htt, hrr] using hphi10
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
    simpa only [htt, hrr, hbb, hdd, hww] using hkdef0
  have hrow :
      let A0 := cubicANumerator68 t r
      let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
      let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r
      let eDot := terminalEDerivativeNumerator68 H E0
      b1 * w1 * eDot - d1 * k1 = C j * H ^ 5 := by
    simpa only [htt, hrr, hbb, hdd, hww] using hrow0
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hdvdB : H ∣ b1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hroot a ha).1)
  have hdvdD : H ∣ d1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hroot a ha).2.1)
  have hdvdW : H ∣ w1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hroot a ha).2.2)
  obtain ⟨b2, hb2⟩ := hdvdB
  obtain ⟨d2, hd2⟩ := hdvdD
  obtain ⟨w2, hw2⟩ := hdvdW
  have hI4source := S.terminalI4_cleared_source_identity (H := H)
    hp hp6 hg hgr ht
  rw [hb1, hd1, hw1, hphi] at hI4source
  have hI4 : b1 * phi1 + (6 : k[X]) * w1 * d1 = 0 := by
    have hfac : H ^ 2 * (b1 * phi1 + (6 : k[X]) * w1 * d1) = 0 := by
      linear_combination hI4source
    exact (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hH)
  have hI4next : b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0 := by
    rw [hb2, hw2, hd2] at hI4
    apply mul_left_cancel₀ hH
    linear_combination hI4
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
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, ?_⟩
  intro hphiDvd
  obtain ⟨phi2, hphi2⟩ := hphiDvd
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let c0 := terminalCShiftNumerator68 H A0 S.alpha
  let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
    S.epsilon S.eta
  let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
    S.alpha S.gamma S.epsilon S.eta
  have hW1 : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1]
    simp only [cubicWNumerator68]
  have hW2 : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w2 := by
    rw [hW1, hw2]
    ring
  have hPhi1 : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H * phi1 := by
    dsimp only [A0, C0, E0, terminalScaledPhi68]
    rw [← hphi, ← hb1]
    simp only [cubicPhiNumerator68]
  have hkcanonical : k1 = terminalKDotNext68 H E0 V0 c0 R1 := by
    simpa only [A0, C0, E0, c0, V0, R1] using hkdef
  have hkroot : ∀ a : k, H.eval a = 0 → k1.eval a = 0 := by
    intro a ha
    have hcoords := terminalScaled_root_coordinates_68 H A0 b1 C0 E0 w1
      phi1 S.gamma S.epsilon a hW1 hPhi1 ha
    have hw1root : w1.eval a = 0 := by
      have h := congrArg (fun f : k[X] => f.eval a) hw2
      simpa [ha] using h
    rw [hkcanonical]
    have hk0 := terminalKDotNext_eval_root_68 H A0 b1 C0 d1 E0 w1
      phi1 S.alpha S.gamma S.epsilon S.eta a ha hcoords.1 hcoords.2
    dsimp only [c0, V0, R1] at hk0
    rw [hcoords.1, hw1root] at hk0
    have hp0 : phi1.eval a = 0 := by
      have he := congrArg (fun P : k[X] => P.eval a) hphi2
      simpa [ha] using he
    rw [hp0] at hk0
    simpa using hk0
  have hkDvd : H ∣ k1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hkroot
  obtain ⟨k2, hk2⟩ := hkDvd
  have hI4q : b2 * phi2 + (6 : k[X]) * w2 * d2 = 0 := by
    rw [hphi2] at hI4next
    apply mul_left_cancel₀ hH
    linear_combination hI4next
  have hrow' : H * b2 * w2 *
      terminalEDerivativeNumerator68 H E0 - d2 * k1 = C j * H ^ 4 := by
    simpa only [A0, C0, E0] using hrowNext
  have hrowq : b2 * w2 * terminalEDerivativeNumerator68 H E0 -
      d2 * k2 = C j * H ^ 3 := by
    rw [hk2] at hrow'
    apply mul_left_cancel₀ hH
    linear_combination hrow'
  have hCshape : C0 = C (1 / 3 : k) * A0 ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w2 - C (3 / 2 * S.gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hm := congrArg (algebraMap k[X] (RatFunc k)) hW2
    dsimp only [terminalScaledW68] at hm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hm ⊢
    linear_combination (9 / 4 : RatFunc k) * hm
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
  refine ⟨phi2, k2, hphi2, hk2, hI4q, hrowq, ?_⟩
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
  have hface := terminalLowerZeroOne_next_split_68 H A0 b2 d2 phi2 w2
    S.alpha S.gamma S.epsilon S.eta a ha (hsimple a ha) hlowshape
  have hI4a := congrArg (fun P : k[X] => P.eval a) hI4q
  have hrowa := congrArg (fun P : k[X] => P.eval a) hrowq
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat,
    eval_zero, ha, zero_pow, mul_zero] at hI4a hrowa
  have hcoords : E0.eval a = (A0.eval a) ^ 3 / 27 := by
    have hm := congrArg (fun P : k[X] => P.eval a) hEshape
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat,
      ha, zero_pow, zero_mul, mul_zero, zero_add, add_zero] at hm
    simpa [div_eq_mul_inv, mul_comm] using hm
  have hrowa0 : b2.eval a * w2.eval a *
      (terminalEDerivativeNumerator68 H E0).eval a -
      d2.eval a * k2.eval a = 0 := by
    simpa using hrowa
  have he := terminalEDerivativeNumerator_eval_root_68 H A0 E0 a ha hcoords
  exact terminalPhiDivisor_degeneracy_68 (A0.eval a) (b2.eval a)
    (d2.eval a) (w2.eval a) (phi2.eval a)
    ((terminalEDerivativeNumerator68 H E0).eval a) (k2.eval a)
    (H.derivative.eval a) hI4a hrowa0 he hface

end PhiDivisorDegeneracySource68

end Max11DegreeRoutes
