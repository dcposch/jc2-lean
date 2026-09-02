import Sol68ScaleTwoAlignedNonsquareTerminalKOneSourceScratch

/-! # The first exact root value of the transverse derivative quotient -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

section TerminalKOneNextRoot68

variable {k : Type*} [Field k] [CharZero k]

/-- The canonical next quotient has a sparse root value.  All derivatives of
`A₀,C₀,E₀` cancel; only the already extracted `W,Φ` quotients remain. -/
theorem terminalKDotNext_eval_root_68
    (H A0 b1 C0 d1 E0 w1 phi1 : k[X])
    (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0)
    (hC : C0.eval a = (A0.eval a) ^ 2 / 3)
    (hE : E0.eval a = (A0.eval a) ^ 3 / 27) :
    let c0 := terminalCShiftNumerator68 H A0 alpha
    let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0
      alpha gamma epsilon eta
    let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
      alpha gamma epsilon eta
    (terminalKDotNext68 H E0 V0 c0 R1).eval a =
      H.derivative.eval a *
        (-(1 / 6 : k) * A0.eval a * phi1.eval a -
          2 * C0.eval a * w1.eval a) := by
  dsimp only [terminalKDotNext68, terminalCShiftNumerator68,
    terminalVNumerator68, terminalKDotLoadQuotient68]
  simp only [derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, eval_add, eval_sub, eval_neg, eval_mul,
    eval_pow, eval_C, eval_ofNat, zero_mul, zero_add, add_zero, mul_zero,
    ha]
  rw [hC, hE]
  ring

/-- On the first transverse component the new quotient value is incompatible
with the descended last row unless the odd quotient `b` vanishes. -/
theorem terminalFBranch_kOne_deleted_68
    (r b d w phi eDot k1 hprime A : k)
    (hr : r ≠ 0) (hhprime : hprime ≠ 0)
    (hI4 : b * phi + 6 * w * d = 0)
    (hrow : b * w * eDot - d * k1 = 0)
    (hw : w = (2 / 27 : k) * r * b)
    (hd : d = -(5 / 36 : k) * r ^ 2 * b)
    (hA : A = -(1 / 12 : k) * r ^ 2)
    (he : eDot = -(1 / 9 : k) * hprime * A ^ 3)
    (hk : k1 = hprime *
      (-(1 / 6 : k) * A * phi - (2 / 3 : k) * A ^ 2 * w)) :
    b = 0 := by
  by_contra hb
  have hphi : phi = (5 / 81 : k) * r ^ 3 * b := by
    have hfac : b * (phi - (5 / 81 : k) * r ^ 3 * b) = 0 := by
      rw [hw, hd] at hI4
      linear_combination hI4
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hb)
  have hk' : k1 = (1 / 1944 : k) * hprime * r ^ 5 * b := by
    rw [hk, hA, hphi, hw]
    ring
  have hsharp := terminalFBranch_kOne_sharp_68 r b d w eDot k1 hprime A
    hr hrow hw hd he
  rcases hsharp with hb0 | hface
  · exact hb hb0
  · rw [hk', hA] at hface
    have hzero : hprime * r ^ 6 * b = 0 := by
      linear_combination (27 / 2 : k) * hface
    exact (mul_ne_zero hhprime (mul_ne_zero (pow_ne_zero 6 hr) hb))
      (by simpa only [mul_assoc] using hzero)

/-- The second transverse component survives, but its new quotient is now an
explicit monomial. -/
theorem terminalGBranch_kOne_exact_68
    (r b d w phi k1 hprime A : k)
    (hr : r ≠ 0)
    (hI4 : b * phi + 6 * w * d = 0)
    (hw : w = -(2 / 27 : k) * r * b)
    (hd : d = -(1 / 36 : k) * r ^ 2 * b)
    (hA : A = -(1 / 12 : k) * r ^ 2)
    (hk : k1 = hprime *
      (-(1 / 6 : k) * A * phi - (2 / 3 : k) * A ^ 2 * w)) :
    b = 0 ∨ k1 = (1 / 5832 : k) * hprime * r ^ 5 * b := by
  rcases eq_or_ne b 0 with hb | hb
  · exact Or.inl hb
  · right
    have hphi : phi = -(1 / 81 : k) * r ^ 3 * b := by
      have hfac : b * (phi + (1 / 81 : k) * r ^ 3 * b) = 0 := by
        rw [hw, hd] at hI4
        linear_combination hI4
      have hsum := (mul_eq_zero.mp hfac).resolve_left hb
      linear_combination hsum
    rw [hk, hA, hphi, hw]
    ring

/-- Pointwise, `b₁(a)=0` is precisely an extra multiplicity of the original
odd numerator at the simple core root. -/
theorem terminalB_derivative_zero_of_quotient_root_68
    (H B b1 : k[X]) (a : k) (hB : B = H * b1)
    (ha : H.eval a = 0) (hb : b1.eval a = 0) :
    B.derivative.eval a = 0 := by
  rw [hB, derivative_mul, eval_add, eval_mul, eval_mul, ha, hb]
  ring

/-- If the `b₁=0` sibling occurs at both roots, it globalizes to `H² | B`. -/
theorem terminalB_sq_dvd_of_all_quotient_roots_68
    [IsAlgClosed k]
    (H B b1 : k[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hB : B = H * b1)
    (hb : ∀ a : k, H.eval a = 0 → b1.eval a = 0) :
    H ^ 2 ∣ B := by
  have hdvd : H ∣ b1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hb
  obtain ⟨b2, hb2⟩ := hdvd
  refine ⟨b2, ?_⟩
  rw [hB, hb2]
  ring

end TerminalKOneNextRoot68

section TerminalKOneNextSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing assembly of the new quotient value.  The first transverse
component is deleted away from `b₁=0`; the second is reduced to one exact
monomial value of `k₁`. -/
theorem NonsquareAlignedSourceCurveData68.terminalKOneNextSourcePacket
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
       let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
         S.alpha S.gamma S.epsilon S.eta
       k1 = terminalKDotNext68 H E0 V0 c0 R1) ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       b1 * w1 * eDot - d1 * k1 = C j * H ^ 5) ∧
      ∀ a : k, H.eval a = 0 →
        r.eval a = 0 ∨
          ((9 * (r.eval a) ^ 2 * X.eval a -
              2 * r.eval a * Yd.eval a + 81 * (p.coeff 2).eval a = 0) ∧
            b1.eval a = 0) ∨
          ((3 * (r.eval a) ^ 2 * X.eval a -
              r.eval a * Yd.eval a + 81 * (p.coeff 2).eval a = 0) ∧
            (b1.eval a = 0 ∨
              k1.eval a = (1 / 5832 : k) * H.derivative.eval a *
                (r.eval a) ^ 5 * b1.eval a)) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, hg, hr, ht, hX, hY,
      hb1, hd1, hw1, hphi1, hI4, hbranches⟩ :=
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
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  refine ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, hg, hr, ht, hX, hY,
    hb1, hd1, hw1, hphi1, ?_, ?_, ?_⟩
  · rfl
  · simpa only [A0, C0, E0, eDot, k1] using hrow5
  · intro a ha
    have hcoords := terminalScaled_root_coordinates_68 H A0 b1 C0 E0 w1
      phi1 S.gamma S.epsilon a hW hPhi ha
    have hAeval : A0.eval a = -(1 / 12 : k) * (r.eval a) ^ 2 := by
      dsimp only [A0, cubicANumerator68]
      simp only [eval_sub, eval_mul, eval_pow, eval_C]
      have hta := congrArg (fun f : k[X] => f.eval a) hX
      simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, ha,
        zero_mul] at hta
      linear_combination (1 / 3 : k) * hta
    have heval : eDot.eval a = -(1 / 9 : k) * H.derivative.eval a *
        (A0.eval a) ^ 3 :=
      terminalEDerivativeNumerator_eval_root_68 H A0 E0 a ha hcoords.2
    have hkroot : k1.eval a = H.derivative.eval a *
        (-(1 / 6 : k) * A0.eval a * phi1.eval a -
          (2 / 3 : k) * (A0.eval a) ^ 2 * w1.eval a) := by
      have hk0 := terminalKDotNext_eval_root_68 H A0 b1 C0 d1 E0 w1
        phi1 S.alpha S.gamma S.epsilon S.eta a ha hcoords.1 hcoords.2
      dsimp only [c0, V0, R1, k1] at hk0
      rw [hcoords.1] at hk0
      convert hk0 using 1 <;> ring
    have hrowa : b1.eval a * w1.eval a * eDot.eval a -
        d1.eval a * k1.eval a = 0 := by
      simpa [ha] using congrArg (fun f : k[X] => f.eval a) hrow5
    have hI4a : b1.eval a * phi1.eval a +
        6 * w1.eval a * d1.eval a = 0 := by
      simpa using congrArg (fun f : k[X] => f.eval a) hI4
    rcases hbranches a ha with hr0 | hF | hG
    · exact Or.inl hr0
    · rcases eq_or_ne (r.eval a) 0 with hr0 | hrne
      · exact Or.inl hr0
      · right; left
        refine ⟨hF.1, ?_⟩
        exact terminalFBranch_kOne_deleted_68 (r.eval a) (b1.eval a)
          (d1.eval a) (w1.eval a) (phi1.eval a) (eDot.eval a)
          (k1.eval a) (H.derivative.eval a) (A0.eval a) hrne
          (hsimple a ha) hI4a hrowa hF.2.1 hF.2.2 hAeval heval hkroot
    · rcases eq_or_ne (r.eval a) 0 with hr0 | hrne
      · exact Or.inl hr0
      · right; right
        refine ⟨hG.1, ?_⟩
        exact terminalGBranch_kOne_exact_68 (r.eval a) (b1.eval a)
          (d1.eval a) (w1.eval a) (phi1.eval a) (k1.eval a)
          (H.derivative.eval a) (A0.eval a) hrne hI4a hG.2.1 hG.2.2
          hAeval hkroot

end TerminalKOneNextSource68

end Max11DegreeRoutes
