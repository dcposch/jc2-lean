import Sol68ScaleTwoAlignedNonsquareSourceComprehensiveSplitScratch

/-! # Fixed-witness coordinate split for the nonsquare source

The coordinate divisor is reconstructed from the literal `KOneNext` and
`DoubleZero` source quotients.  Only quotients with exported defining
equations are identified, by cancellation in `k[X]`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

section FixedCoordinateSplit68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- The exact transverse allocation on the fixed source quotients. -/
def terminalFixedCoordinateMixed68
    (H r phi1 B D w eDot k1 : k[X]) : Prop :=
  ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
    r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
    r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
    B.eval a = 0 ∧
    B.derivative.eval a * phi1.eval a +
      6 * H.derivative.eval a * w.eval a * D.eval a = 0 ∧
    (D.eval a = 0 ∨ k1.eval a = 0) ∧
    H.derivative.eval a * B.eval a * w.eval a * eDot.eval a -
      (D.derivative.eval a * k1.eval a +
        D.eval a * k1.derivative.eval a) = 0 ∧
    B.eval b * phi1.derivative.eval b +
      6 * H.derivative.eval b * w.eval b * D.eval b = 0 ∧
    H.derivative.eval b * B.eval b * w.eval b * eDot.eval b -
      (D.derivative.eval b * k1.eval b +
        D.eval b * k1.derivative.eval b) = 0 ∧
    (D.eval b = 0 ∨ k1.eval b = 0)

/-- Comprehensive normalized aligned-nonsquare residual on one fixed tuple.
The alternatives are the canonical `r` divisor, the literal two-root mixed
packet, and the complete post-`phi1` fixed geometric split. -/
def terminalFixedCoordinateComprehensiveResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  H ∣ r ∨
    terminalFixedCoordinateMixed68 H r phi1 B D w
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) k1 ∨
    ∃ phi K : k[X],
      terminalPhiDivisorSameWitnessSourceTransport68 H S
        r t X0 Yd B D w phi1 k1 phi K ∧
      terminalPhiDivisorFixedGeometricSplit68 H p r t X0 B D w phi K j

/-- The normalized source constructs one fixed tuple carrying the complete
coordinate split.  In particular the `H ∣ phi1` branch feeds directly into
the fixed-witness geometric theorem; no existential tuple is reselected. -/
theorem NonsquareAlignedSourceCurveData68.fixedCoordinateComprehensivePacket
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ r t X0 Yd B D w phi1 k1 : k[X],
      p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
      C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
      B * phi1 + C 6 * H * w * D = 0 ∧
      H * B * w * terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
      H ∣ r * phi1 ∧
      terminalFixedCoordinateComprehensiveResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  classical
  obtain ⟨g, r, t, X0, Yd, b1, d1, w1, phi1, kOld, B, D, w,
      hg, hgr, hp4, hX, hY, hb1, hd1, hw1, hphi1, hB, hD, hw,
      hI4, hrowOld, hroots, _hpure⟩ :=
    S.terminalAfterLowerOneDoubleZeroPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  obtain ⟨g0, r0, t0, X00, Yd0, b10, d10, w10, phi10, k1,
      hg0, hgr0, hp40, hX0, hY0, hb10, hd10, hw10, hphi10,
      hkdef, hrow5, _hselectors⟩ :=
    S.terminalKOneNextSourcePacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hgg : g0 = g := by
    apply mul_left_cancel₀ hH
    rw [← hg0, ← hg]
  have hrr : r0 = r := by
    apply mul_left_cancel₀ hH
    rw [← hgr0, ← hgr, hgg]
  have htt : t0 = t := by
    apply mul_left_cancel₀ hH
    rw [← hp40, ← hp4]
  have hXX : X00 = X0 := by
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
    rw [← hphi10, ← hphi1, htt, hrr]
  subst g0
  subst r0
  subst t0
  subst X00
  subst Yd0
  subst b10
  subst d10
  subst w10
  subst phi10
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hrow4 : H * B * w * eDot - D * k1 = C j * H ^ 4 := by
    rw [hB, hw, hD] at hrow5
    apply mul_left_cancel₀ hH
    simpa only [A0, C0, E0, eDot] using (by linear_combination hrow5)
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hW1 : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1]
    simp only [cubicWNumerator68]
  have hW2 : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w := by
    rw [hW1, hw]
    ring
  have hCshape : C0 = C (1 / 3 : k) * A0 ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hm := congrArg (algebraMap k[X] (RatFunc k)) hW2
    dsimp only [terminalScaledW68] at hm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hm ⊢
    linear_combination (9 / 4 : RatFunc k) * hm
  have hPhi1 : terminalScaledPhi68 H A0 b1 C0 E0
      S.gamma S.epsilon = H * phi1 := by
    dsimp only [A0, C0, E0, terminalScaledPhi68]
    rw [← hphi1, ← hb1]
    simp only [cubicPhiNumerator68]
  have hEshape : E0 = C (1 / 27 : k) * A0 ^ 3 +
      C (3 / 8 : k) * H * phi1 +
      H ^ 2 * (C (3 / 2 : k) * A0 * w -
        C (1 / 2 * S.gamma : k) * A0) -
      C (3 / 4 * S.epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * b1) ^ 2 := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hPm := congrArg (algebraMap k[X] (RatFunc k)) hPhi1
    have hCm := congrArg (algebraMap k[X] (RatFunc k)) hCshape
    dsimp only [terminalScaledPhi68] at hPm
    simp only [map_add, map_sub, map_neg, map_mul, map_pow,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one] at hPm hCm ⊢
    linear_combination (3 / 8 : RatFunc k) * hPm +
      (2 / 3 * algebraMap k[X] (RatFunc k) A0) * hCm
  have htransport := S.terminalLowerZeroClearedTransport_source (H := H)
    hp hp6 hg hgr hp4 hX hY
  obtain ⟨hAred, hBred, hCred, hDred, hEred⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X0 Yd hX hY
  have hbred : terminalGReducedB68 r X0 Yd = b1 := by
    apply mul_left_cancel₀ hH
    rw [← hBred, ← hb1]
  have hdred : terminalGReducedD68 H r X0 Yd (p.coeff 1) (p.coeff 2) =
      d1 := by
    apply mul_left_cancel₀ hH
    rw [← hDred, ← hd1]
  have hlower : terminalLowerZeroCleared68 H A0 b1 C0 d1 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    simpa only [A0, C0, E0, ← hAred, hbred, ← hCred, hdred, ← hEred]
      using htransport
  have hrootCoordinate : ∀ a : k, H.eval a = 0 →
      (r * phi1).eval a = 0 := by
    intro a ha
    by_contra hrphi
    have hrne : r.eval a ≠ 0 := by
      intro hr0
      exact hrphi (by simp [eval_mul, hr0])
    have hpne : phi1.eval a ≠ 0 := by
      intro hp0
      exact hrphi (by simp [eval_mul, hp0])
    rcases hroots a ha with hr0 | hp0 | hdouble
    · exact False.elim (hrne hr0)
    · exact False.elim (hpne hp0)
    · let L : k[X] := X - C a
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
      have hMne : M.eval a ≠ 0 := by rw [hMval]; exact hsimple a ha
      have hrowOld' : H * B * w * eDot - D * kOld = C j * H ^ 4 := by
        simpa only [A0, C0, E0, eDot] using hrowOld
      have hboot := terminalAfterLowerOne_mixedRoot_bootstrap_68
        H B phi1 w D eDot kOld j a ha hpne hdouble.2.2.2.2
        hdouble.1 hdouble.2.1 hdouble.2.2.1 hdouble.2.2.2.1 hI4 hrowOld'
      obtain ⟨BQ, hBQ⟩ := hboot.1
      obtain ⟨DQ, hDQ⟩ := hboot.2
      have hL : L ≠ 0 := by dsimp only [L]; exact X_sub_C_ne_zero a
      have hrowQ : L ^ 2 * M * BQ * w * eDot - DQ * kOld =
          C j * M ^ 4 := by
        apply mul_left_cancel₀ (pow_ne_zero 4 hL)
        rw [hHM, hBQ, hDQ] at hrowOld'
        linear_combination hrowOld'
      have hDprod : DQ.eval a * kOld.eval a = -j * (M.eval a) ^ 4 := by
        have he := congrArg (fun P : k[X] => P.eval a) hrowQ
        dsimp only [L] at he
        simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C,
          eval_X, sub_self, zero_pow, zero_mul] at he
        linear_combination -he
      have hDQne : DQ.eval a ≠ 0 := by
        intro hDz
        rw [hDz, zero_mul] at hDprod
        exact (mul_ne_zero (neg_ne_zero.mpr hj) (pow_ne_zero 4 hMne))
          hDprod.symm
      have hbLocal : b1 = L ^ 6 * (M * BQ) := by
        rw [hB, hBQ, hHM]
        ring
      have hdLocal : d1 = L ^ 5 * (M * DQ) := by
        rw [hD, hDQ, hHM]
        ring
      have hClocal : C0 = C (1 / 3 : k) * A0 ^ 2 +
          (L * M) ^ 2 *
            (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k)) := by
        rw [← hHM]
        exact hCshape
      have hElocal : E0 = C (1 / 27 : k) * A0 ^ 3 +
          C (3 / 8 : k) * (L * M) * phi1 +
          (L * M) ^ 2 * (C (3 / 2 : k) * A0 * w -
            C (1 / 2 * S.gamma : k) * A0) -
          C (3 / 4 * S.epsilon : k) * (L * M) ^ 3 +
          C (1 / 9 : k) * ((L * M) * (L ^ 6 * (M * BQ))) ^ 2 := by
        rw [← hHM, ← hbLocal]
        exact hEshape
      have hlowerLocal : terminalLowerZeroCleared68 (L * M)
          A0 b1 C0 d1 E0 S.alpha S.gamma S.epsilon S.eta = 0 := by
        rw [← hHM]
        exact hlower
      exact False.elim (terminalLowerZero_mixedLocal_impossible_68
        M A0 b1 C0 d1 E0 (M * BQ) (M * DQ) phi1 w
        S.alpha S.gamma S.epsilon S.eta a hMne
        (by simp only [eval_mul]; exact mul_ne_zero hMne hDQne) hpne
        (by simpa only [L] using hbLocal)
        (by simpa only [L] using hdLocal)
        (by simpa only [L] using hClocal)
        (by simpa only [L] using hElocal)
        (by simpa only [L] using hlowerLocal))
  have hdvd : H ∣ r * phi1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hrootCoordinate
  have hsplit := simpleQuadratic_dvd_product_coordinate_split_68
    H r phi1 hdeg hsimple hdvd
  refine ⟨r, t, X0, Yd, B, D, w, phi1, k1, hp4, hX, hY, hI4,
    (by simpa only [E0, eDot] using hrow4), hdvd, ?_⟩
  rcases hsplit with hr | hphi | hmixed
  · exact Or.inl hr
  · right
    right
    obtain ⟨phi, hphiEq⟩ := hphi
    have hkroot : ∀ a : k, H.eval a = 0 → k1.eval a = 0 := by
      intro a ha
      have hcoords := terminalScaled_root_coordinates_68 H A0 b1 C0 E0 w1
        phi1 S.gamma S.epsilon a hW1 hPhi1 ha
      have hwroot : w1.eval a = 0 := by
        have he := congrArg (fun P : k[X] => P.eval a) hw
        simpa [ha] using he
      have hphiroot : phi1.eval a = 0 := by
        have he := congrArg (fun P : k[X] => P.eval a) hphiEq
        simpa [ha] using he
      rw [hkdef]
      have hk0 := terminalKDotNext_eval_root_68 H A0 b1 C0 d1 E0 w1
        phi1 S.alpha S.gamma S.epsilon S.eta a ha hcoords.1 hcoords.2
      dsimp only at hk0 ⊢
      rw [hcoords.1, hwroot, hphiroot] at hk0
      simpa using hk0
    obtain ⟨K, hkEq⟩ : ∃ K, k1 = H * K :=
      dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hkroot
    have hI4q : B * phi + C 6 * w * D = 0 := by
      rw [hphiEq] at hI4
      have hz : H * (B * phi + C 6 * w * D) = 0 := by
        calc
          H * (B * phi + C 6 * w * D) =
              B * (H * phi) + C 6 * H * w * D := by ring
          _ = 0 := hI4
      exact (mul_eq_zero.mp hz).resolve_left hH
    have hrowq : B * w * eDot - D * K = C j * H ^ 3 := by
      rw [hkEq] at hrow4
      apply mul_left_cancel₀ hH
      linear_combination hrow4
    have hPhi2 : terminalScaledPhi68 H A0 (H * B) C0 E0
        S.gamma S.epsilon = H ^ 2 * phi := by
      rw [← hB, hPhi1, hphiEq]
      ring
    have hlowerBD : terminalLowerZeroCleared68 H A0 (H * B) C0
        (H * D) E0 S.alpha S.gamma S.epsilon S.eta = 0 := by
      rw [← hB, ← hD]
      exact hlower
    have T : terminalPhiDivisorSameWitnessSourceTransport68 H S
        r t X0 Yd B D w phi1 k1 phi K :=
      ⟨hp4, hX, hY, by simpa only [A0, C0] using hW2,
        by simpa only [A0, C0, E0] using hPhi2, ⟨hphiEq, hkEq⟩,
        hI4q, by simpa only [E0, eDot] using hrowq,
        by simpa only [A0, C0, E0] using hlowerBD⟩
    exact ⟨phi, K, T,
      S.fixedWitnessComprehensiveSplit (H := H) hdeg
        r t X0 Yd B D w phi1 k1 phi K T⟩
  · right
    left
    obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb⟩ := hmixed
    have hrf := terminalAfterLowerOne_rRoot_faces_68
      H B phi1 w D eDot k1 j a ha hpa hI4 hrow4
    have hpf := terminalAfterLowerOne_phiRoot_faces_68
      H B phi1 w D eDot k1 j b hb hpb (hsimple b hb) hI4 hrow4
    exact ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb,
      hrf.1, hrf.2.1, hrf.2.2.1, hrf.2.2.2,
      hpf.1, hpf.2.1, hpf.2.2⟩

end FixedCoordinateSplit68

end Max11DegreeRoutes
