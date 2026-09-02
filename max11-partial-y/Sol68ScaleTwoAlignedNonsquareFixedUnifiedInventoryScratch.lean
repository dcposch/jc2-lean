import Fable68ScaleTwoAlignedNonsquareFixedRDivisorConsumerScratch
import Fable68ScaleTwoAlignedNonsquareFixedPhiEarlyGeometricConsumerScratch
import Sol68ScaleTwoAlignedNonsquareSourceFixedMixedFifthScratch

/-! # Unified fixed-coordinate aligned nonsquare inventory -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 24000000

section FixedUnifiedInventory68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- The fixed-R construction with its already-proved lower-zero transport
exported on the same tuple. -/
theorem NonsquareAlignedSourceCurveData68.fixedRDivisorConsumerPacketWithLower
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
      terminalFixedMixedLowerTransport68 H S r t X0 Yd
        B D w phi1 k1 ∧
      terminalFixedRDivisorConsumerResidual68 H S
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
  have Tlower : terminalFixedMixedLowerTransport68 H S
      r t X0 Yd B D w phi1 k1 := by
    refine ⟨b1, d1, C0, E0, hB, hD, rfl, rfl, ?_, ?_, ?_⟩
    · simpa only [A0] using hCshape
    · simpa only [A0] using hEshape
    · simpa only [A0] using hlower
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
  refine ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, (by simpa only [E0, eDot] using hrow4), hdvd,
    Tlower, ?_⟩
  rcases hsplit with hr | hphiDvd | hmixed
  · obtain ⟨s, hs⟩ := hr
    obtain ⟨ht1c, ht1sc, hp4sc, hy1c, hy1sc⟩ :=
      rDivisor_coordinate_cascade_68 H r t X0 Yd (p.coeff 3) (p.coeff 4)
        s hs hp4 hX hY
    have hnum := rDivisor_numerator_cascade_68 H s
      (C (1 / 3 : k) * (H * s ^ 2 + X0))
      (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd))
      (p.coeff 0) (p.coeff 1) (p.coeff 2)
    let t1w : k[X] := C (1 / 3 : k) * (H * s ^ 2 + X0)
    let y1w : k[X] := C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)
    let A1w : k[X] := t1w - C (5 / 12 : k) * H * s ^ 2
    let c2w : k[X] := C (1 / 3 : k) * A1w ^ 2 + C (9 / 4 : k) * w -
      C (3 / 2 * S.gamma : k)
    let e3w : k[X] := p.coeff 0 - C (1 / 6 : k) * p.coeff 1 * s +
      C (1 / 36 : k) * p.coeff 2 * s ^ 2 -
      C (1 / 216 : k) * H * y1w * s ^ 3 +
      C (1 / 1296 : k) * H ^ 2 * t1w * s ^ 4 -
      C (5 / 46656 : k) * H ^ 3 * s ^ 6
    let psiw : k[X] := rDivisorLowerZeroPhiQuotient68 H A1w B c2w e3w
      S.gamma S.epsilon
    let mw : k[X] := H * B * w * e3w.derivative - C j
    have hAf : cubicANumerator68 t r = H * A1w := by
      dsimp only [A1w, t1w]
      rw [ht1c, hs]
      exact hnum.1
    have hEf : cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r = H ^ 3 * e3w := by
      dsimp only [e3w, y1w, t1w]
      rw [ht1c, hs, hy1c]
      exact hnum.2.2
    have hCshapeLit := hCshape
    dsimp only [A0, C0] at hCshapeLit
    have hCf : cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r =
        H ^ 2 * c2w := by
      rw [hCshapeLit, hAf]
      dsimp only [c2w]
      ring
    have heDot : terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) = H ^ 4 * e3w.derivative := by
      rw [hEf]
      exact rDivisor_derivative_collapse_68 H e3w
    have hphi2 : phi1 = H ^ 2 * psiw := by
      apply mul_left_cancel₀ hH
      rw [← hPhi1]
      dsimp only [A0, C0, E0]
      rw [hB, hAf, hCf, hEf, rDivisorLowerZero_phi_factor_68]
      dsimp only [psiw]
      ring
    have hwd6 : (6 : k[X]) * (w * D) = -(H * B * psiw) := by
      apply mul_left_cancel₀ hH
      linear_combination hI4 - B * hphi2
    have hwd : w * D = -(C (1 / 6 : k)) * (H * B * psiw) := by
      linear_combination C (1 / 6 : k) * hwd6 -
        w * D * rDivisorLowerZeroSixUnit68 (k := k)
    have hlowerB : terminalLowerZeroCleared68 H (cubicANumerator68 t r)
        (H * B) (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
        (H * D)
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)
        S.alpha S.gamma S.epsilon S.eta = 0 := by
      rw [← hB, ← hD]
      exact hlower
    have hbranch : terminalLowerZeroCleared68 H (H * A1w) (H * B)
        (H ^ 2 * c2w) (H * D) (H ^ 3 * e3w)
        S.alpha S.gamma S.epsilon S.eta = 0 := by
      rw [← hAf, ← hCf, ← hEf]
      exact hlowerB
    have hQ0 : rDivisorLowerZeroQuotient68 H A1w B c2w D e3w
        S.alpha S.gamma S.epsilon S.eta = 0 := by
      have hz : H ^ 4 * rDivisorLowerZeroQuotient68 H A1w B c2w D e3w
          S.alpha S.gamma S.epsilon S.eta = 0 := by
        rw [← rDivisorLowerZero_row_factor_68]
        exact hbranch
      exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 4 hH)
    have hrowE : H * B * w * (H ^ 4 * e3w.derivative) - D * k1 =
        C j * H ^ 4 := by
      rw [← heDot]
      exact hrow4
    have hdk : D * k1 = H ^ 4 * mw :=
      rDivisor_row_cofactor_68 H B w D k1 e3w j hrowE
    have hfaces : ∀ a : k, H.eval a = 0 →
        (w * D).eval a = 0 ∧ (D * psiw).eval a = 0 ∧
          D.eval a * k1.eval a = 0 := by
      intro a ha
      have hf := rDivisorLowerZero_root_faces_68 H A1w B c2w D e3w w
        psiw S.alpha S.gamma S.epsilon S.eta rfl rfl hwd hQ0 a ha
        (hsimple a ha)
      refine ⟨hf.1, hf.2, ?_⟩
      have hdka := congrArg (fun P : k[X] => P.eval a) hdk
      simpa [ha] using hdka
    have hdpsi : H ∣ D * psiw :=
      dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
        (fun a ha => (hfaces a ha).2.1)
    have hval : ∀ a : k, H.eval a = 0 →
        mw.eval a = -j ∧ mw.eval a ≠ 0 := by
      intro a ha
      have h1 : mw.eval a = -j :=
        rDivisor_cofactor_eval_68 H B w e3w j a ha
      exact ⟨h1, by rw [h1]; exact neg_ne_zero.mpr hj⟩
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hdeg]
      decide
    obtain ⟨a0, ha0⟩ := IsAlgClosed.exists_root H hdegne
    have ha0' : H.eval a0 = 0 := ha0
    have hne := rDivisor_factors_ne_zero_68 H D k1 mw j hj hH hdk
      a0 ha0' (hval a0 ha0').1
    have hkroot : ∀ a : k, H.eval a = 0 → k1.eval a = 0 := by
      intro a ha
      have hcoords := terminalScaled_root_coordinates_68 H A0 b1 C0 E0 w1
        phi1 S.gamma S.epsilon a hW1 hPhi1 ha
      have hwroot : w1.eval a = 0 := by
        have he := congrArg (fun P : k[X] => P.eval a) hw
        simpa [ha] using he
      have hphiroot : phi1.eval a = 0 := by
        have he := congrArg (fun P : k[X] => P.eval a) hphi2
        simpa [ha] using he
      rw [hkdef]
      have hk0 := terminalKDotNext_eval_root_68 H A0 b1 C0 d1 E0 w1
        phi1 S.alpha S.gamma S.epsilon S.eta a ha hcoords.1 hcoords.2
      dsimp only at hk0 ⊢
      rw [hcoords.1, hwroot, hphiroot] at hk0
      simpa using hk0
    obtain ⟨K, hkEq⟩ : ∃ K, k1 = H * K :=
      dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hkroot
    have hphiEq : phi1 = H * (H * psiw) := by
      rw [hphi2]
      ring
    have hI4q : B * (H * psiw) + C 6 * w * D = 0 := by
      rw [hphi2] at hI4
      have hz : H * (B * (H * psiw) + C 6 * w * D) = 0 := by
        calc
          H * (B * (H * psiw) + C 6 * w * D) =
              B * (H ^ 2 * psiw) + C 6 * H * w * D := by ring
          _ = 0 := hI4
      exact (mul_eq_zero.mp hz).resolve_left hH
    have hrowq : B * w * eDot - D * K = C j * H ^ 3 := by
      rw [hkEq] at hrow4
      apply mul_left_cancel₀ hH
      linear_combination hrow4
    have hPhi2 : terminalScaledPhi68 H A0 (H * B) C0 E0
        S.gamma S.epsilon = H ^ 2 * (H * psiw) := by
      rw [← hB, hPhi1, hphi2]
      ring
    have hlowerBD : terminalLowerZeroCleared68 H A0 (H * B) C0
        (H * D) E0 S.alpha S.gamma S.epsilon S.eta = 0 := by
      rw [← hB, ← hD]
      exact hlower
    have T : terminalPhiDivisorSameWitnessSourceTransport68 H S
        r t X0 Yd B D w phi1 k1 (H * psiw) K :=
      ⟨hp4, hX, hY, by simpa only [A0, C0] using hW2,
        by simpa only [A0, C0, E0] using hPhi2, ⟨hphiEq, hkEq⟩,
        hI4q, by simpa only [E0, eDot] using hrowq,
        by simpa only [A0, C0, E0] using hlowerBD⟩
    have hgeom : terminalPhiDivisorFixedGeometricSplit68 H p
        r t X0 B D w (H * psiw) K j :=
      S.fixedWitnessComprehensiveSplit (H := H) hdeg
        r t X0 Yd B D w phi1 k1 (H * psiw) K T
    have hassembly : terminalFixedPhiFinalAssembly68 H S
        r t X0 Yd B D w phi1 k1 :=
      S.fixedPhiFinalAssembly_of_transport (H := H) hdeg hj
        r t X0 Yd B D w phi1 k1 (H * psiw) K T hgeom
    exact Or.inl ⟨s, t1w, y1w, A1w, c2w, e3w, psiw, mw, K,
      hs, ⟨s, hs⟩, ht1c, ht1sc, hp4sc, hy1c, hy1sc,
      ⟨t1w, ht1c⟩, ⟨t1w, hp4sc⟩, ⟨y1w, hy1c⟩,
      rfl, hAf, rfl, hCf, rfl, hEf, heDot, rfl, hphi2,
      ⟨psiw, hphi2⟩, ⟨H * psiw, hphiEq⟩,
      hwd, ⟨-(C (1 / 6 : k)) * (B * psiw), by rw [hwd]; ring⟩,
      hlowerB, hQ0, hdpsi, hfaces, rfl, hdk, ⟨mw, hdk⟩, hval,
      hne.1, hne.2, hkEq, T, hgeom, hassembly⟩
  · right
    right
    obtain ⟨phi, hphiEq⟩ := hphiDvd
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
    exact S.fixedPhiFinalAssembly_of_transport (H := H) hdeg hj
      r t X0 Yd B D w phi1 k1 phi K T
      (S.fixedWitnessComprehensiveSplit (H := H) hdeg
        r t X0 Yd B D w phi1 k1 phi K T)
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

/-- One same-witness normalized residual: refined R-divisor data with its
early-geometric routing, fifth-row mixed data, or early-geometric phi data. -/
def terminalFixedUnifiedInventory68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  (terminalFixedRDivisorLowerZeroRefined68 H S
      r t X0 Yd B D w phi1 k1 ∧
    terminalFixedPhiEarlyGeometricAssembly68 H S
      r t X0 Yd B D w phi1 k1) ∨
  terminalFixedMixedFifth68 H r phi1 B D w
      (terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)) k1 j ∨
  terminalFixedPhiEarlyGeometricAssembly68 H S
    r t X0 Yd B D w phi1 k1

/-- The repaired source packet feeds all three consumers without changing
any polynomial or root witness. -/
theorem NonsquareAlignedSourceCurveData68.fixedUnifiedInventoryPacket
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
      terminalFixedMixedLowerTransport68 H S r t X0 Yd
        B D w phi1 k1 ∧
      terminalFixedUnifiedInventory68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
      hp4, hX, hY, hI4, hrow, hdvd, Tlower, hres⟩ :=
    S.fixedRDivisorConsumerPacketWithLower (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower, ?_⟩
  rcases hres with href | hmixed | hphi
  · left
    refine ⟨href, S.fixedPhiEarlyGeometricAssembly_of_fixedAssembly
      (H := H) hdeg r t X0 Yd B D w phi1 k1 ?_⟩
    exact terminalFixedRDivisorLowerZeroRefined68_phiAssembly H S
      r t X0 Yd B D w phi1 k1 href
  · right
    left
    have hthird := terminalFixedMixed_third_68 H S
      r t X0 Yd B D w phi1 k1 hdeg hj hI4 hrow Tlower hmixed
    have hfourth := terminalFixedMixed_fourth_68 H S
      r t X0 Yd B D w phi1 k1 hdeg hj hX hI4 hrow Tlower hthird
    exact terminalFixedMixed_fifth_68 H hdeg hfourth
  · right
    right
    exact S.fixedPhiEarlyGeometricAssembly_of_fixedAssembly
      (H := H) hdeg r t X0 Yd B D w phi1 k1 hphi

end FixedUnifiedInventory68

section NormalizedFixedUnifiedInventory68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Normalized fixed-coordinate H=2 aligned-nonsquare inventory with the
R-divisor, mixed fifth-row, and early-geometric phi consumers all on one
canonical tuple. -/
theorem normalized68ScaleTwo_alignedNonsquare_fixedUnifiedInventory
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
        p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
        C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
        B * phi1 + C 6 * H * w * D = 0 ∧
        H * B * w * terminalEDerivativeNumerator68 H
            (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
        H ∣ r * phi1 ∧
        terminalFixedMixedLowerTransport68 H S r t X0 Yd
          B D w phi1 k1 ∧
        terminalFixedUnifiedInventory68 H S
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
  refine ⟨j, S, hj, ?_⟩
  exact S.fixedUnifiedInventoryPacket (H := H)
    hHdegree hp hq hp6' hq8' haligned' hjac hj

end NormalizedFixedUnifiedInventory68

end Max11DegreeRoutes
