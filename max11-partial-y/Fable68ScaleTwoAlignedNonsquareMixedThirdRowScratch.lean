import Sol68ScaleTwoAlignedNonsquareAfterLowerOneCoordinateSplitScratch

/-! # Third row of the preserved transverse two-root allocation

The coordinate-split packet keeps the genuinely transverse family: a core
root `a` with `r(a)=0`, `Φ₁(a)≠0` and a distinct core root `b` with
`r(b)≠0`, `Φ₁(b)=0`, each carrying the exact `I₄` and terminal
first-derivative faces together with the scalar split `d₂=0 ∨ k₁=0`.

The first genuinely unused row at the `r`-root is the transported lower-zero
one-form: its order-`0` and order-`1` specializations are vacuous there
(`b₁ = H b₂`, `d₁ = H d₂` make every low term automatic), while its local
five-factor derivative coefficient `(3/2) M² D Φ₁` is a unit multiple exactly
when `k₁(a) ≠ 0`.  On that face the two retained scalar rows force the
simultaneous double zeros of `b₂` and `d₂`, the mixed-root bootstrap lifts
them to orders five and four, and the lower-zero row then refutes the face.
Hence the split at the `r`-root collapses outright to `k₁(a) = 0`, and the
terminal derivative face there sharpens to `d₂(a)·k₁'(a) = 0`.

At the complementary `Φ₁`-root the surviving split globalizes exactly, using
the degree-two simple-root transfer only where two actual zero evaluations
justify it: `k₁(b)=0` joins `k₁(a)=0` and divides the terminal row by the
core, `b₂(b)=0` joins `b₂(a)=0` and divides `I₄` by the core, and otherwise
the smallest exact cross-root residual remains: `d₂(b)=0`, `Φ₁'(b)=0` with
units `k₁(b)`, `b₂(b)` and the reduced terminal face
`H'(b) b₂(b) w₂(b) Ė(b) = d₂'(b) k₁(b)`.  No `x`-degree bounds are assumed
and the `H∣r`, `H∣Φ₁` branches are passed through untouched. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section MixedThirdRowAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The two given distinct roots exhaust the roots of a degree-two core. -/
theorem natDegree_two_roots_exhaust_68
    (H : k[X]) (hdeg : H.natDegree = 2) (a b c : k) (hab : a ≠ b)
    (ha : H.eval a = 0) (hb : H.eval b = 0) (hc : H.eval c = 0) :
    c = a ∨ c = b := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hlinA : X - C a ∣ H := by
    rw [dvd_iff_isRoot]
    exact ha
  obtain ⟨H1, hH1⟩ := hlinA
  have hH1b : H1.eval b = 0 := by
    have hev := congrArg (fun P : k[X] => P.eval b) hH1
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hev
    rw [hb] at hev
    exact (mul_eq_zero.mp hev.symm).resolve_left
      (sub_ne_zero.mpr (Ne.symm hab))
  have hlinB : X - C b ∣ H1 := by
    rw [dvd_iff_isRoot]
    exact hH1b
  obtain ⟨H2, hH2⟩ := hlinB
  have hfull : H = (X - C a) * ((X - C b) * H2) := by
    rw [hH1, hH2]
  have hH2ne : H2 ≠ 0 := by
    rintro rfl
    rw [mul_zero, mul_zero] at hfull
    exact hH hfull
  have hH2deg : H2.natDegree = 0 := by
    have hXa : (X - C a : k[X]) ≠ 0 := X_sub_C_ne_zero a
    have hXb : (X - C b : k[X]) ≠ 0 := X_sub_C_ne_zero b
    have hmul : H.natDegree =
        (X - C a : k[X]).natDegree + ((X - C b) * H2).natDegree := by
      rw [hfull]
      exact natDegree_mul hXa (mul_ne_zero hXb hH2ne)
    rw [natDegree_mul hXb hH2ne] at hmul
    simp only [natDegree_X_sub_C] at hmul
    rw [hdeg] at hmul
    omega
  have hH2c : H2.eval c ≠ 0 := by
    intro h0
    apply hH2ne
    have hconst := eq_C_of_natDegree_eq_zero hH2deg
    rw [hconst] at h0
    rw [eval_C] at h0
    rw [hconst, h0, C_0]
  have hev := congrArg (fun P : k[X] => P.eval c) hfull
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hev
  rw [hc] at hev
  rcases mul_eq_zero.mp hev.symm with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inr (sub_eq_zero.mp h')
    · exact absurd h' hH2c

/-- Degree-two simple-root transfer: two actual zero evaluations, one at
each of two distinct core roots, globalize to core divisibility. -/
theorem dvd_of_two_simple_root_evals_68
    (H P : k[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (a b : k) (hab : a ≠ b) (ha : H.eval a = 0) (hb : H.eval b = 0)
    (hPa : P.eval a = 0) (hPb : P.eval b = 0) : H ∣ P := by
  apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
  intro c hc
  rcases natDegree_two_roots_exhaust_68 H hdeg a b c hab ha hb hc with
    rfl | rfl
  · exact hPa
  · exact hPb

end MixedThirdRowAlgebra68

section MixedThirdRowSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Third-row refinement of the preserved transverse two-root allocation.
The lower-zero transport row, specialized at the `r`-root through its local
five-factor coefficient, deletes the `k₁≠0` face there, so the terminal
scalar split collapses to the definite face `k₁(a)=0` with the sharpened
derivative face `d₂(a)·k₁'(a)=0`.  At the complementary `Φ₁`-root the split
globalizes exactly: either `k₁` gains both core roots and the terminal row
divides by the core, or `b₂` gains both core roots and `I₄` divides by the
core, or the exact transverse residual `d₂(b)=0 ∧ Φ₁'(b)=0` remains with
units `k₁(b)`, `b₂(b)`. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneMixedThirdRowPacket
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
      (H ∣ r ∨ H ∣ phi1 ∨
        (let A0 := cubicANumerator68 t r
         let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
         let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
           (p.coeff 3) t r
         let eDot := terminalEDerivativeNumerator68 H E0
         ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
           r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
           r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
           b2.eval a = 0 ∧ k1.eval a = 0 ∧
           b2.derivative.eval a * phi1.eval a +
             6 * H.derivative.eval a * w2.eval a * d2.eval a = 0 ∧
           d2.eval a * k1.derivative.eval a = 0 ∧
           b2.eval b * phi1.derivative.eval b +
             6 * H.derivative.eval b * w2.eval b * d2.eval b = 0 ∧
           H.derivative.eval b * b2.eval b * w2.eval b * eDot.eval b -
             (d2.derivative.eval b * k1.eval b +
               d2.eval b * k1.derivative.eval b) = 0 ∧
           ((k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
               b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) ∨
            (d2.eval b = 0 ∧ b2.eval b = 0 ∧ ∃ b3 : k[X], b2 = H * b3 ∧
               b3 * phi1 + (6 : k[X]) * w2 * d2 = 0 ∧
               d2 * k1 = H ^ 2 * (b3 * w2 * eDot - C j * H ^ 2)) ∨
            (d2.eval b = 0 ∧ k1.eval b ≠ 0 ∧ b2.eval b ≠ 0 ∧
               phi1.derivative.eval b = 0 ∧
               H.derivative.eval b * b2.eval b * w2.eval b * eDot.eval b =
                 d2.derivative.eval b * k1.eval b)))) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
      hg, hgr, ht, hX, hY, hb1n, hd1n, hw1n, hphin, hb1b2, hd1d2, hw1w2,
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
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  -- Exact core shapes of the retained cubic coordinates.
  have hW1 : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1n]
    simp only [cubicWNumerator68]
  have hW2 : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w2 := by
    rw [hW1, hw1w2]
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
    rw [← hphin, ← hb1n]
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
    rw [← hBred, ← hb1n]
  have hdred : terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2) =
      d1 := by
    apply mul_left_cancel₀ hH
    rw [← hDred, ← hd1n]
  have hlower : terminalLowerZeroCleared68 H A0 b1 C0 d1 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    simpa only [A0, C0, E0, ← hAred, hbred, ← hCred, hdred, ← hEred]
      using htransport
  -- The lower-zero row deletes any core root carrying units `Φ₁`, `k₁`
  -- and simultaneous double zeros of `b₂`, `d₂`.
  have hlocalKill : ∀ x : k, H.eval x = 0 → phi1.eval x ≠ 0 →
      k1.eval x ≠ 0 → b2.eval x = 0 → b2.derivative.eval x = 0 →
      d2.eval x = 0 → d2.derivative.eval x = 0 → False := by
    intro x hx hpx hkx hbx hbdx hdx hddx
    have hboot := terminalAfterLowerOne_mixedRoot_bootstrap_68
      H b2 phi1 w2 d2 eDot k1 j x hx hpx hkx hbx hbdx hdx hddx hI4 hrow'
    let L : k[X] := Polynomial.X - C x
    have hLH : L ∣ H := by
      dsimp only [L]
      rw [dvd_iff_isRoot]
      exact hx
    obtain ⟨M, hHM⟩ := hLH
    have hMval : M.eval x = H.derivative.eval x := by
      have hder := congrArg (fun P : k[X] => P.derivative.eval x) hHM
      dsimp only [L] at hder
      simp only [derivative_mul, derivative_sub, derivative_X,
        derivative_C, eval_add, eval_mul, eval_sub, eval_one, eval_X,
        eval_C, sub_self, zero_mul, one_mul, add_zero] at hder
      simpa using hder.symm
    have hMne : M.eval x ≠ 0 := by
      rw [hMval]
      exact hsimple x hx
    obtain ⟨B, hB⟩ := hboot.1
    obtain ⟨D, hD⟩ := hboot.2
    have hL : L ≠ 0 := by
      dsimp only [L]
      exact X_sub_C_ne_zero x
    have hrowQ : L ^ 2 * M * B * w2 * eDot - D * k1 = C j * M ^ 4 := by
      apply mul_left_cancel₀ (pow_ne_zero 4 hL)
      rw [hHM, hB, hD] at hrow'
      linear_combination hrow'
    have hDprod : D.eval x * k1.eval x = -j * (M.eval x) ^ 4 := by
      have he := congrArg (fun P : k[X] => P.eval x) hrowQ
      dsimp only [L] at he
      simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C,
        eval_X, sub_self, zero_pow, zero_mul] at he
      linear_combination -he
    have hDne : D.eval x ≠ 0 := by
      intro hDz
      rw [hDz, zero_mul] at hDprod
      exact (mul_ne_zero (neg_ne_zero.mpr hj) (pow_ne_zero 4 hMne))
        hDprod.symm
    have hbLocal : b1 = L ^ 6 * (M * B) := by
      rw [hb1b2, hB, hHM]
      ring
    have hdLocal : d1 = L ^ 5 * (M * D) := by
      rw [hd1d2, hD, hHM]
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
    exact terminalLowerZero_mixedLocal_impossible_68
      M A0 b1 C0 d1 E0 (M * B) (M * D) phi1 w2
      S.alpha S.gamma S.epsilon S.eta x hMne
      (by simp only [eval_mul]; exact mul_ne_zero hMne hDne) hpx
      (by simpa only [L] using hbLocal)
      (by simpa only [L] using hdLocal)
      (by simpa only [L] using hClocal)
      (by simpa only [L] using hElocal)
      (by simpa only [L] using hlowerLocal)
  -- Every core root lies on the coordinate divisor.
  have hrootCoordinate : ∀ x : k, H.eval x = 0 →
      (r * phi1).eval x = 0 := by
    intro x hx
    by_contra hrphi
    have hrne : r.eval x ≠ 0 := by
      intro hr0
      exact hrphi (by simp [eval_mul, hr0])
    have hpne : phi1.eval x ≠ 0 := by
      intro hp0
      exact hrphi (by simp [eval_mul, hp0])
    rcases hroots x hx with hr0 | hp0 | hdz
    · exact hrne hr0
    · exact hpne hp0
    · exact hlocalKill x hx hpne hdz.2.2.2.2 hdz.1 hdz.2.1 hdz.2.2.1
        hdz.2.2.2.1
  have hdvd : H ∣ r * phi1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      hrootCoordinate
  have hsplitTri := simpleQuadratic_dvd_product_coordinate_split_68
    H r phi1 hdeg hsimple hdvd
  rcases hsplitTri with hcase | hcase | hmix
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inl hcase⟩
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inr (Or.inl hcase)⟩
  · obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb⟩ := hmix
    have hrf := terminalAfterLowerOne_rRoot_faces_68
      H b2 phi1 w2 d2 eDot k1 j a ha hpa hI4 hrow'
    have hpf := terminalAfterLowerOne_phiRoot_faces_68
      H b2 phi1 w2 d2 eDot k1 j b hb hpb (hsimple b hb) hI4 hrow'
    have hb2a : b2.eval a = 0 := hrf.1
    have hface4a : d2.derivative.eval a * k1.eval a +
        d2.eval a * k1.derivative.eval a = 0 := by
      linear_combination -hrf.2.2.2 +
        H.derivative.eval a * w2.eval a * eDot.eval a * hb2a
    -- The lower-zero row collapses the split at the `r`-root.
    have hk1a : k1.eval a = 0 := by
      by_contra hk1ne
      have hd2a : d2.eval a = 0 := hrf.2.2.1.resolve_right hk1ne
      have hb2da : b2.derivative.eval a = 0 := by
        have hz : b2.derivative.eval a * phi1.eval a = 0 := by
          linear_combination hrf.2.1 -
            6 * H.derivative.eval a * w2.eval a * hd2a
        exact (mul_eq_zero.mp hz).resolve_right hpa
      have hd2da : d2.derivative.eval a = 0 := by
        have hz : d2.derivative.eval a * k1.eval a = 0 := by
          linear_combination hface4a - k1.derivative.eval a * hd2a
        exact (mul_eq_zero.mp hz).resolve_right hk1ne
      exact hlocalKill a ha hpa hk1ne hb2a hb2da hd2a hd2da
    have hd2k1da : d2.eval a * k1.derivative.eval a = 0 := by
      linear_combination hface4a - d2.derivative.eval a * hk1a
    -- Exact globalization of the surviving split at the `Φ₁`-root.
    have htrichB :
        (k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
            b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) ∨
        (d2.eval b = 0 ∧ b2.eval b = 0 ∧ ∃ b3 : k[X], b2 = H * b3 ∧
            b3 * phi1 + (6 : k[X]) * w2 * d2 = 0 ∧
            d2 * k1 = H ^ 2 * (b3 * w2 * eDot - C j * H ^ 2)) ∨
        (d2.eval b = 0 ∧ k1.eval b ≠ 0 ∧ b2.eval b ≠ 0 ∧
            phi1.derivative.eval b = 0 ∧
            H.derivative.eval b * b2.eval b * w2.eval b * eDot.eval b =
              d2.derivative.eval b * k1.eval b) := by
      by_cases hk1b : k1.eval b = 0
      · left
        refine ⟨hk1b, ?_⟩
        obtain ⟨k2, hk2⟩ := dvd_of_two_simple_root_evals_68 H k1 hdeg
          hsimple a b hab ha hb hk1a hk1b
        refine ⟨k2, hk2, ?_⟩
        apply mul_left_cancel₀ hH
        rw [hk2] at hrow'
        linear_combination hrow'
      · have hd2b : d2.eval b = 0 := hpf.2.2.resolve_right hk1b
        by_cases hb2b : b2.eval b = 0
        · right
          left
          refine ⟨hd2b, hb2b, ?_⟩
          obtain ⟨b3, hb3⟩ := dvd_of_two_simple_root_evals_68 H b2 hdeg
            hsimple a b hab ha hb hb2a hb2b
          refine ⟨b3, hb3, ?_, ?_⟩
          · apply mul_left_cancel₀ hH
            rw [hb3] at hI4
            linear_combination hI4
          · rw [hb3] at hrow'
            linear_combination -hrow'
        · right
          right
          have hphi1db : phi1.derivative.eval b = 0 := by
            have hz : b2.eval b * phi1.derivative.eval b = 0 := by
              linear_combination hpf.1 -
                6 * H.derivative.eval b * w2.eval b * hd2b
            exact (mul_eq_zero.mp hz).resolve_left hb2b
          refine ⟨hd2b, hk1b, hb2b, hphi1db, ?_⟩
          linear_combination hpf.2.1 + k1.derivative.eval b * hd2b
    exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inr (Or.inr
        ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hb2a, hk1a,
         hrf.2.1, hd2k1da, hpf.1, hpf.2.1, htrichB⟩)⟩

end MixedThirdRowSource68

end Max11DegreeRoutes
