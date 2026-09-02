import Sol68ScaleTwoAlignedNonsquareAfterLowerOneTwoRootMixedBootstrapScratch

/-! # Local lower-zero closure of the mixed two-root allocation -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section MixedLocalLowerZeroAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalLowerZeroLocalSFive68
    (L H A B D : k[X]) (alpha : k) : k[X] :=
  C (4 / 3 : k) * D + C (4 / 9 : k) * L * A * B +
    C alpha * H * L * B

def terminalLowerZeroLocalUFive68
    (L H A B C0 D : k[X]) (alpha gamma : k) : k[X] :=
  C (4 / 9 : k) * L * B * C0 + C (4 / 9 : k) * A * D -
    C (4 / 27 : k) * L * A ^ 2 * B + C alpha * H * D +
    C (2 / 3 * gamma : k) * H ^ 2 * L * B

def terminalLowerZeroLocalDDFive68
    (L M H D : k[X]) : k[X] :=
  (C 2 * C 5 * M * L.derivative - C 3 * H.derivative) * D +
    C 2 * H * D.derivative

def terminalLowerZeroLocalUDFive68
    (L M H U : k[X]) : k[X] :=
  (C 2 * C 5 * M * L.derivative - C 5 * H.derivative) * U +
    C 2 * H * U.derivative

def terminalLowerZeroLocalFive68
    (L M H A B C0 D E : k[X])
    (alpha gamma epsilon eta : k) : k[X] :=
  let S5 := terminalLowerZeroLocalSFive68 L H A B D alpha
  let T0 := terminalLowerOneTNumerator68 H A (L ^ 6 * B) C0 E
    alpha gamma epsilon
  let U5 := terminalLowerZeroLocalUFive68 L H A B C0 D alpha gamma
  let V0 := terminalVNumerator68 H A (L ^ 6 * B) C0 (L ^ 5 * D) E
    alpha gamma epsilon eta
  U5 * terminalLowerZeroCDot68 H C0 +
    T0 * terminalLowerZeroLocalDDFive68 L M H D +
    C 3 * S5 * terminalEDerivativeNumerator68 H E -
    C 3 * L * B * terminalVDerivativeNumerator68 H V0 -
    C0 * terminalLowerZeroLocalUDFive68 L M H U5 -
    D * terminalLowerZeroTDot68 H T0

/-- Local factorization at one simple core root.  Unlike the global `H`-adic
factorization, the complementary factor `M` is retained explicitly. -/
theorem terminalLowerZero_local_factor_five_68
    (L M H A b C0 d E B D : k[X])
    (alpha gamma epsilon eta : k)
    (hH : H = L * M) (hb : b = L ^ 6 * B) (hd : d = L ^ 5 * D) :
    terminalLowerZeroCleared68 H A b C0 d E alpha gamma epsilon eta =
      L ^ 5 * terminalLowerZeroLocalFive68 L M H A B C0 D E
        alpha gamma epsilon eta := by
  rw [hb, hd]
  have hS : terminalLowerZeroSNumerator68 H A (L ^ 6 * B) (L ^ 5 * D)
      alpha = L ^ 5 * terminalLowerZeroLocalSFive68 L H A B D alpha := by
    simp only [terminalLowerZeroSNumerator68, terminalLowerZeroLocalSFive68]
    ring
  have hU : terminalLowerOneUNumerator68 H A (L ^ 6 * B) C0 (L ^ 5 * D)
      alpha gamma = L ^ 5 *
        terminalLowerZeroLocalUFive68 L H A B C0 D alpha gamma := by
    simp only [terminalLowerOneUNumerator68, terminalLowerZeroLocalUFive68]
    ring
  have hpow5 : (L ^ 5).derivative = C 5 * L ^ 4 * L.derivative := by
    rw [derivative_pow]
    norm_num
  have hHder : H.derivative = L.derivative * M + L * M.derivative := by
    rw [hH, derivative_mul]
  have hDD : terminalLowerOneDTwoDot68 H (L ^ 5 * D) =
      L ^ 5 * terminalLowerZeroLocalDDFive68 L M H D := by
    simp only [terminalLowerOneDTwoDot68, terminalLowerZeroLocalDDFive68,
      derivative_mul, hpow5]
    rw [hHder, hH]
    ring
  have hUD : terminalLowerOneUTwoDot68 H
      (terminalLowerOneUNumerator68 H A (L ^ 6 * B) C0 (L ^ 5 * D)
        alpha gamma) = L ^ 5 * terminalLowerZeroLocalUDFive68 L M H
          (terminalLowerZeroLocalUFive68 L H A B C0 D alpha gamma) := by
    rw [hU]
    simp only [terminalLowerOneUTwoDot68, terminalLowerZeroLocalUDFive68,
      derivative_mul, hpow5]
    rw [hHder, hH]
    ring
  simp only [terminalLowerZeroCleared68, terminalLowerZeroLocalFive68]
  rw [hS, hDD, hUD, hU]
  ring

/-- The first coefficient after the five automatic local factors.  The
complementary core factor contributes exactly the unit square `M(a)^2`. -/
theorem terminalLowerZeroLocalFive_derivative_factor_68
    (M A B D phi w : k[X]) (alpha gamma epsilon eta a : k) :
    let L : k[X] := X - C a
    let H := L * M
    let C0 := C (1 / 3 : k) * A ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
    let E := C (1 / 27 : k) * A ^ 3 + C (3 / 8 : k) * H * phi +
      H ^ 2 * (C (3 / 2 : k) * A * w - C (1 / 2 * gamma : k) * A) -
      C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * (L ^ 6 * B)) ^ 2
    (terminalLowerZeroLocalFive68 L M H A B C0 D E
      alpha gamma epsilon eta).derivative.eval a =
        (3 / 2 : k) * (M.eval a) ^ 2 * D.eval a * phi.eval a := by
  dsimp only
  simp only [terminalLowerZeroLocalFive68,
    terminalLowerZeroLocalUFive68, terminalLowerZeroLocalSFive68,
    terminalLowerZeroLocalDDFive68, terminalLowerZeroLocalUDFive68,
    terminalLowerZeroCDot68, terminalLowerZeroTDot68,
    terminalLowerOneTNumerator68, terminalEDerivativeNumerator68,
    terminalVDerivativeNumerator68, terminalVNumerator68,
    derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_X, derivative_ofNat,
    C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul, eval_pow,
    eval_C, eval_X, eval_one, eval_ofNat, eval_zero, sub_self, zero_mul, mul_zero,
    zero_add, add_zero, zero_pow]
  ring

theorem terminalLowerZero_mixedLocal_impossible_68
    (M A b C0 d E B D phi w : k[X])
    (alpha gamma epsilon eta a : k)
    (hM : M.eval a ≠ 0) (hD : D.eval a ≠ 0)
    (hphi : phi.eval a ≠ 0)
    (hb : b = (X - C a) ^ 6 * B)
    (hd : d = (X - C a) ^ 5 * D)
    (hC : C0 = C (1 / 3 : k) * A ^ 2 +
      ((X - C a) * M) ^ 2 *
        (C (9 / 4 : k) * w - C (3 / 2 * gamma : k)))
    (hE : E = C (1 / 27 : k) * A ^ 3 +
      C (3 / 8 : k) * ((X - C a) * M) * phi +
      ((X - C a) * M) ^ 2 *
        (C (3 / 2 : k) * A * w - C (1 / 2 * gamma : k) * A) -
      C (3 / 4 * epsilon : k) * ((X - C a) * M) ^ 3 +
      C (1 / 9 : k) *
        (((X - C a) * M) * ((X - C a) ^ 6 * B)) ^ 2)
    (hlower : terminalLowerZeroCleared68 ((X - C a) * M)
      A b C0 d E alpha gamma epsilon eta = 0) : False := by
  let L : k[X] := X - C a
  let H := L * M
  have hfactor := terminalLowerZero_local_factor_five_68
    L M H A b C0 d E B D alpha gamma epsilon eta rfl hb hd
  have hL : L ≠ 0 := by
    dsimp only [L]
    exact X_sub_C_ne_zero a
  have hfive : terminalLowerZeroLocalFive68 L M H A B C0 D E
      alpha gamma epsilon eta = 0 := by
    have hz : L ^ 5 * terminalLowerZeroLocalFive68 L M H A B C0 D E
        alpha gamma epsilon eta = 0 := by
      rw [← hfactor]
      simpa only [H, L] using hlower
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 5 hL)
  have hzero : (terminalLowerZeroLocalFive68 L M H A B C0 D E
      alpha gamma epsilon eta).derivative.eval a = 0 := by
    rw [hfive, derivative_zero, eval_zero]
  rw [hC, hE] at hzero
  change (terminalLowerZeroLocalFive68 (X - C a) M ((X - C a) * M)
      A B _ D _ alpha gamma epsilon eta).derivative.eval a = 0 at hzero
  rw [terminalLowerZeroLocalFive_derivative_factor_68
    M A B D phi w alpha gamma epsilon eta a] at hzero
  exact (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hM)) hD)
      hphi) hzero

end MixedLocalLowerZeroAlgebra68

section MixedLocalClosureSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- The local lower-zero coefficient deletes the complementary double-root
component.  Consequently every root of the quadratic core lies on the
coordinate divisor `r*phi₁`, so the entire remaining family is expressed by
the single global divisibility `H ∣ r*phi₁`. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneCoordinateDvdPacket
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
      b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4) ∧
      H ∣ r * phi1 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       ∀ a : k, H.eval a = 0 → phi1.eval a = 0 →
        b2.eval a * phi1.derivative.eval a +
            6 * H.derivative.eval a * w2.eval a * d2.eval a = 0 ∧
          H.derivative.eval a * b2.eval a * w2.eval a * eDot.eval a -
            (d2.derivative.eval a * k1.eval a +
              d2.eval a * k1.derivative.eval a) = 0) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
      hg, hgr, ht, hX, hY, hb1, hd1, hw1, hphi, hb2, hd2, hw2,
      hI4, hrow, hroots, _hpure⟩ :=
    S.terminalAfterLowerOneDoubleZeroPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hrow' : H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4 := by
    simpa only [A0, C0, E0, eDot] using hrow
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
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
  have hPhi : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H * phi1 := by
    dsimp only [A0, C0, E0, terminalScaledPhi68]
    rw [← hphi, ← hb1]
    simp only [cubicPhiNumerator68]
  have hEshape : E0 = C (1 / 27 : k) * A0 ^ 3 +
      C (3 / 8 : k) * H * phi1 +
      H ^ 2 * (C (3 / 2 : k) * A0 * w2 -
        C (1 / 2 * S.gamma : k) * A0) -
      C (3 / 4 * S.epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * b1) ^ 2 := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hPm := congrArg (algebraMap k[X] (RatFunc k)) hPhi
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
    · let L : k[X] := Polynomial.X - C a
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
      have hMne : M.eval a ≠ 0 := by
        rw [hMval]
        exact hsimple a ha
      have hboot := terminalAfterLowerOne_mixedRoot_bootstrap_68
        H b2 phi1 w2 d2 eDot k1 j a ha hpne hdouble.2.2.2.2
        hdouble.1 hdouble.2.1 hdouble.2.2.1 hdouble.2.2.2.1 hI4 hrow'
      obtain ⟨B, hB⟩ := hboot.1
      obtain ⟨D, hD⟩ := hboot.2
      have hL : L ≠ 0 := by
        dsimp only [L]
        exact X_sub_C_ne_zero a
      have hrowQ : L ^ 2 * M * B * w2 * eDot - D * k1 = C j * M ^ 4 := by
        apply mul_left_cancel₀ (pow_ne_zero 4 hL)
        rw [hHM, hB, hD] at hrow'
        linear_combination hrow'
      have hDprod : D.eval a * k1.eval a = -j * (M.eval a) ^ 4 := by
        have he := congrArg (fun P : k[X] => P.eval a) hrowQ
        dsimp only [L] at he
        simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C,
          eval_X, sub_self, zero_pow, zero_mul] at he
        linear_combination -he
      have hDne : D.eval a ≠ 0 := by
        intro hDz
        rw [hDz, zero_mul] at hDprod
        exact (mul_ne_zero (neg_ne_zero.mpr hj) (pow_ne_zero 4 hMne))
          hDprod.symm
      have hbLocal : b1 = L ^ 6 * (M * B) := by
        rw [hb2, hB, hHM]
        ring
      have hdLocal : d1 = L ^ 5 * (M * D) := by
        rw [hd2, hD, hHM]
        ring
      have hClocal : C0 = C (1 / 3 : k) * A0 ^ 2 +
          (L * M) ^ 2 *
            (C (9 / 4 : k) * w2 - C (3 / 2 * S.gamma : k)) := by
        rw [← hHM]
        exact hCshape
      have hElocal : E0 = C (1 / 27 : k) * A0 ^ 3 +
          C (3 / 8 : k) * (L * M) * phi1 +
          (L * M) ^ 2 * (C (3 / 2 : k) * A0 * w2 -
            C (1 / 2 * S.gamma : k) * A0) -
          C (3 / 4 * S.epsilon : k) * (L * M) ^ 3 +
          C (1 / 9 : k) * ((L * M) * (L ^ 6 * (M * B))) ^ 2 := by
        rw [← hHM, ← hbLocal]
        exact hEshape
      have hlowerLocal : terminalLowerZeroCleared68 (L * M)
          A0 b1 C0 d1 E0 S.alpha S.gamma S.epsilon S.eta = 0 := by
        rw [← hHM]
        exact hlower
      exact False.elim (terminalLowerZero_mixedLocal_impossible_68
        M A0 b1 C0 d1 E0 (M * B) (M * D) phi1 w2
        S.alpha S.gamma S.epsilon S.eta a hMne
        (by simp only [eval_mul]; exact mul_ne_zero hMne hDne) hpne
        (by simpa only [L] using hbLocal)
        (by simpa only [L] using hdLocal)
        (by simpa only [L] using hClocal)
        (by simpa only [L] using hElocal)
        (by simpa only [L] using hlowerLocal))
  have hdvd : H ∣ r * phi1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hrootCoordinate
  have hfaces : ∀ a : k, H.eval a = 0 → phi1.eval a = 0 →
      b2.eval a * phi1.derivative.eval a +
          6 * H.derivative.eval a * w2.eval a * d2.eval a = 0 ∧
        H.derivative.eval a * b2.eval a * w2.eval a * eDot.eval a -
          (d2.derivative.eval a * k1.eval a +
            d2.eval a * k1.derivative.eval a) = 0 := by
    intro a ha hpa
    have hf := terminalAfterLowerOne_phiZero_next_faces_68
      H b2 phi1 w2 d2 eDot k1 j a ha hpa (hsimple a ha) hI4 hrow'
    exact ⟨hf.1, hf.2.1⟩
  exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
    ht, hX, hY, hI4, hrow, hdvd, hfaces⟩

end MixedLocalClosureSource68

end Max11DegreeRoutes
