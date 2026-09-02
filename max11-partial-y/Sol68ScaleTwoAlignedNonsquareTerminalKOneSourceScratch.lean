import Sol68ScaleTwoAlignedNonsquareTerminalKDotNextScratch

/-! # Source assembly of the first transverse derivative quotient -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

section TerminalKOneRootAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The two old terminal quotients fix the leading even coordinates. -/
theorem terminalScaled_root_coordinates_68
    (H A0 b1 C0 E0 w1 phi1 : k[X]) (gamma epsilon a : k)
    (hW : terminalScaledW68 H A0 C0 gamma = H * w1)
    (hPhi : terminalScaledPhi68 H A0 b1 C0 E0 gamma epsilon = H * phi1)
    (ha : H.eval a = 0) :
    C0.eval a = (A0.eval a) ^ 2 / 3 ∧
      E0.eval a = (A0.eval a) ^ 3 / 27 := by
  have hWa := congrArg (fun f : k[X] => f.eval a) hW
  have hPhia := congrArg (fun f : k[X] => f.eval a) hPhi
  dsimp only [terminalScaledW68, terminalScaledPhi68] at hWa hPhia
  simp only [eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
    eval_ofNat, ha, zero_mul, zero_pow, OfNat.zero_ne_ofNat, add_zero,
    sub_zero] at hWa hPhia
  constructor
  · linear_combination (9 / 4 : k) * hWa
  · linear_combination (3 / 8 : k) * hPhia +
      (3 / 2 : k) * A0.eval a * hWa

/-- Consequently the first differentiated numerator has a fixed root value. -/
theorem terminalEDerivativeNumerator_eval_root_68
    (H A0 E0 : k[X]) (a : k) (ha : H.eval a = 0)
    (hE : E0.eval a = (A0.eval a) ^ 3 / 27) :
    (terminalEDerivativeNumerator68 H E0).eval a =
      -(1 / 9 : k) * H.derivative.eval a * (A0.eval a) ^ 3 := by
  dsimp only [terminalEDerivativeNumerator68]
  simp only [eval_sub, eval_mul, eval_C, eval_ofNat, ha, zero_mul, zero_sub]
  rw [hE]
  ring

theorem terminalFBranch_kOne_sharp_68
    (r b d w eDot k1 hprime A : k) (hr : r ≠ 0)
    (hrow : b * w * eDot - d * k1 = 0)
    (hw : w = (2 / 27 : k) * r * b)
    (hd : d = -(5 / 36 : k) * r ^ 2 * b)
    (he : eDot = -(1 / 9 : k) * hprime * A ^ 3) :
    b = 0 ∨ 135 * r * k1 - 8 * b * hprime * A ^ 3 = 0 := by
  rw [hw, hd, he] at hrow
  have hfac : r * b * (135 * r * k1 - 8 * b * hprime * A ^ 3) = 0 := by
    linear_combination 972 * hrow
  rcases mul_eq_zero.mp hfac with hrb | hface
  · rcases mul_eq_zero.mp hrb with hr0 | hb
    · exact Or.inl (hr hr0).elim
    · exact Or.inl hb
  · exact Or.inr hface

theorem terminalGBranch_kOne_sharp_68
    (r b d w eDot k1 hprime A : k) (hr : r ≠ 0)
    (hrow : b * w * eDot - d * k1 = 0)
    (hw : w = -(2 / 27 : k) * r * b)
    (hd : d = -(1 / 36 : k) * r ^ 2 * b)
    (he : eDot = -(1 / 9 : k) * hprime * A ^ 3) :
    b = 0 ∨ 27 * r * k1 + 8 * b * hprime * A ^ 3 = 0 := by
  rw [hw, hd, he] at hrow
  have hfac : r * b * (27 * r * k1 + 8 * b * hprime * A ^ 3) = 0 := by
    linear_combination 972 * hrow
  rcases mul_eq_zero.mp hfac with hrb | hface
  · rcases mul_eq_zero.mp hrb with hr0 | hb
    · exact Or.inl (hr hr0).elim
    · exact Or.inl hb
  · exact Or.inr hface

end TerminalKOneRootAlgebra68

section TerminalKOneSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Full source packet after cancelling the newly proved factor of `H` from
the terminal last row. -/
theorem NonsquareAlignedSourceCurveData68.terminalKOneSourcePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (g r t X Yd b1 d1 w1 phi1 k1 : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r = H * d1 ∧
      cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma = H * w1 ∧
      cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r S.gamma S.epsilon = H * phi1 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let c0 := terminalCShiftNumerator68 H A0 S.alpha
       let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
         S.epsilon S.eta
       let eDot := terminalEDerivativeNumerator68 H E0
       b1 * w1 * eDot - d1 * k1 = C j * H ^ 5) ∧
      ∀ a : k, H.eval a = 0 →
        r.eval a = 0 ∨
          ((9 * (r.eval a) ^ 2 * X.eval a -
              2 * r.eval a * Yd.eval a + 81 * (p.coeff 2).eval a = 0) ∧
            (b1.eval a = 0 ∨
              135 * r.eval a * k1.eval a -
                8 * b1.eval a * H.derivative.eval a *
                  (cubicANumerator68 t r).eval a ^ 3 = 0)) ∨
          ((3 * (r.eval a) ^ 2 * X.eval a -
              r.eval a * Yd.eval a + 81 * (p.coeff 2).eval a = 0) ∧
            (b1.eval a = 0 ∨
              27 * r.eval a * k1.eval a +
                8 * b1.eval a * H.derivative.eval a *
                  (cubicANumerator68 t r).eval a ^ 3 = 0)) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, hg, hr, ht, hX, hY,
      hb1, hd1, hw1, hphi1, _hI4, hbranches⟩ :=
    S.terminalFactorsSourcePacket (H := H) hdeg hp hq hp6 hq8 haligned hjac
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
  let kDot := terminalTransverseDerivativeNumerator68 H E0 V0 c0
  let k1 := terminalKDotNext68 H E0 V0 c0 R1
  have hW : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1]
    simp only [cubicWNumerator68]
  have hPhi : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H * phi1 := by
    dsimp only [A0, C0, E0, terminalScaledPhi68]
    rw [← hphi1, ← hb1]
    simp only [cubicPhiNumerator68]
  have hkfactor : kDot = H * k1 := by
    exact terminalTransverseDerivative_next_factor_68 H A0 b1 C0 d1 E0
      w1 phi1 S.alpha S.gamma S.epsilon S.eta hW hPhi
  have hclear : H * b1 * w1 * eDot - d1 * kDot = C j * H ^ 6 := by
    exact S.terminalDerivativeClearIdentity (H := H) hp hp6 hg hr ht hb1 hd1 hw1
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hrow5 : b1 * w1 * eDot - d1 * k1 = C j * H ^ 5 := by
    have hcancel : H * (b1 * w1 * eDot - d1 * k1) =
        H * (C j * H ^ 5) := by
      rw [hkfactor] at hclear
      linear_combination hclear
    exact mul_left_cancel₀ hH hcancel
  refine ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, hg, hr, ht, hX, hY,
    hb1, hd1, hw1, hphi1, ?_, ?_⟩
  · simpa only [A0, C0, E0, c0, V0, eDot, k1] using hrow5
  · intro a ha
    have hcoords := terminalScaled_root_coordinates_68 H A0 b1 C0 E0 w1
      phi1 S.gamma S.epsilon a hW hPhi ha
    have heval : eDot.eval a = -(1 / 9 : k) * H.derivative.eval a *
        (A0.eval a) ^ 3 :=
      terminalEDerivativeNumerator_eval_root_68 H A0 E0 a ha hcoords.2
    have hrowa : b1.eval a * w1.eval a * eDot.eval a -
        d1.eval a * k1.eval a = 0 := by
      simpa [ha] using congrArg (fun f : k[X] => f.eval a) hrow5
    rcases hbranches a ha with hr0 | hF | hG
    · exact Or.inl hr0
    ·
      rcases eq_or_ne (r.eval a) 0 with hr0 | hrne
      · exact Or.inl hr0
      · right; left
        refine ⟨hF.1, ?_⟩
        exact terminalFBranch_kOne_sharp_68 (r.eval a) (b1.eval a) (d1.eval a)
          (w1.eval a) (eDot.eval a) (k1.eval a) (H.derivative.eval a)
          (A0.eval a) hrne hrowa hF.2.1 hF.2.2 heval
    ·
      rcases eq_or_ne (r.eval a) 0 with hr0 | hrne
      · exact Or.inl hr0
      · right; right
        refine ⟨hG.1, ?_⟩
        exact terminalGBranch_kOne_sharp_68 (r.eval a) (b1.eval a) (d1.eval a)
          (w1.eval a) (eDot.eval a) (k1.eval a) (H.derivative.eval a)
          (A0.eval a) hrne hrowa hG.2.1 hG.2.2 heval

end TerminalKOneSource68

end Max11DegreeRoutes
