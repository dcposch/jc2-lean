import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateSourceScratch

/-! # Transverse refinement of the conjugate common component

On the common component of the conjugate global split both leaf identities
`phi + 2*A*w = H*G` and `H*b*G = 2*w*(A*b - 3*D)` are exact.  The all-roots
lower-third packet decides how the remaining core root is allocated:

* if `w` also vanishes at the conjugate root, the common leaf collapses into
  the component-III shape: `w` and `phi` divide by the core with the exact
  quotient pin `phi/H = G - 2*A*w₁`, the terminal row kills `D*K` at the
  conjugate root, and one of `D`, `K` divides by the core with the row
  dropping one core power;
* otherwise the deep-root selector either kills `b` or the cubic coefficient
  at the deep root, the transverse face `A*b - 3*D` then divides by the full
  core, and the core cancels from the `G`-row outright: `b*G = 2*w*F₁`;
* the only residual limb is transverse of order two at the deep root: `w`,
  `phi` and `G` all gain a further root there with the exact tie
  `H'*G' = A*w''`, the third divided-I4 jet, the order-two row tie
  `b*w''*e = 2*D'*K'`, the j-loaded third row, and the derivative of the
  transverse face at the conjugate root tied to `G`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RefinedIIIConjugateCommonAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact transverse refinement of the common conjugate component.  The
`G`-face and the cancelled loaded face are retained verbatim; the finite
split records the three possible allocations of the remaining core root. -/
def terminalRefinedIIIConjugateCommonTransverse68
    (H A b D w phi e K : k[X]) (j a c : k) : Prop :=
  ∃ G : k[X],
    phi + 2 * A * w = H * G ∧
    H * b * G - 2 * w * (A * b - 3 * D) = 0 ∧
    ((w.eval c = 0 ∧
      ∃ w1 : k[X],
        w = H * w1 ∧
        phi = H * (G - 2 * A * w1) ∧
        b * (G - 2 * A * w1) + 6 * w1 * D = 0 ∧
        ((D.eval c = 0 ∧
           ∃ D1 : k[X], D = H * D1 ∧
             b * w1 * e - D1 * K = C j * H ^ 2) ∨
         (K.eval c = 0 ∧
           ∃ K1 : k[X], K = H * K1 ∧
             b * w1 * e - D * K1 = C j * H ^ 2))) ∨
     (w.eval c ≠ 0 ∧
      (∃ F1 : k[X],
        A * b - 3 * D = H * F1 ∧ b * G = 2 * w * F1) ∧
      (b.eval a = 0 ∨
        (A.eval a = 0 ∧ G.eval a = 0 ∧ phi.derivative.eval a = 0))) ∨
     (w.eval c ≠ 0 ∧ b.eval a ≠ 0 ∧ A.eval a ≠ 0 ∧
      w.derivative.eval a = 0 ∧ phi.derivative.eval a = 0 ∧
      phi.derivative.derivative.eval a = 0 ∧ G.eval a = 0 ∧
      H.derivative.eval a * G.derivative.eval a =
        A.eval a * w.derivative.derivative.eval a ∧
      b.eval a * phi.derivative.derivative.derivative.eval a +
        18 * w.derivative.derivative.eval a * D.derivative.eval a = 0 ∧
      b.eval a * w.derivative.derivative.eval a * e.eval a =
        2 * D.derivative.eval a * K.derivative.eval a ∧
      3 * b.derivative.eval a * w.derivative.derivative.eval a * e.eval a +
          b.eval a * w.derivative.derivative.derivative.eval a * e.eval a +
          3 * b.eval a * w.derivative.derivative.eval a *
            e.derivative.eval a -
          3 * D.derivative.derivative.eval a * K.derivative.eval a -
          3 * D.derivative.eval a * K.derivative.derivative.eval a =
        6 * j * H.derivative.eval a ^ 3 ∧
      H.derivative.eval c * b.eval c * G.eval c =
        2 * w.eval c *
          (A.derivative.eval c * b.eval c + A.eval c * b.derivative.eval c -
            3 * D.derivative.eval c)))

/-- The common conjugate leaf refines to the exact transverse split.  The
deep root carries the full source packet, the conjugate root carries the
common matching evals, and the lower-third selector at the deep root closes
the transverse sibling `w'(a) ≠ 0` outside the two collapse branches. -/
theorem terminalRefinedIII_conjugateCommon_transverse_68
    (H A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hDa : D.eval a = 0) (hKa : K.eval a = 0)
    (hI4 : b * phi + 6 * w * D = 0)
    (hrow : b * w * e - D * K = C j * H ^ 3)
    (hsplita : b.eval a = 0 ∨
      (phi.derivative.eval a = 0 ∧
        (A.eval a = 0 ∨ w.derivative.eval a = 0)))
    (hFc : A.eval c * b.eval c - 3 * D.eval c = 0)
    (hGc : phi.eval c + 2 * A.eval c * w.eval c = 0) :
    terminalRefinedIIIConjugateCommonTransverse68 H A b D w phi e K j a c := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hGa0 : (phi + 2 * A * w).eval a = 0 := by
    simp [eval_add, eval_mul, hphia, hwa]
  have hGc0 : (phi + 2 * A * w).eval c = 0 := by
    simp only [eval_add, eval_mul, eval_ofNat]
    linear_combination hGc
  obtain ⟨G, hG⟩ := dvd_of_two_simple_root_evals_68
    H (phi + 2 * A * w) hdeg hsimple a c hac ha hc hGa0 hGc0
  have hleaf : H * b * G - 2 * w * (A * b - 3 * D) = 0 := by
    linear_combination hI4 - b * hG
  refine ⟨G, hG, hleaf, ?_⟩
  rcases eq_or_ne (w.eval c) 0 with hwc | hwc
  · -- the conjugate root also lies on `w`: full component-III collapse
    left
    obtain ⟨w1, hw1⟩ := dvd_of_two_simple_root_evals_68
      H w hdeg hsimple a c hac ha hc hwa hwc
    have hphi1 : phi = H * (G - 2 * A * w1) := by
      linear_combination hG - 2 * A * hw1
    have hI4q : b * (G - 2 * A * w1) + 6 * w1 * D = 0 := by
      apply mul_left_cancel₀ hH
      linear_combination hI4 - b * hG + (2 * A * b - 6 * D) * hw1
    have hrowc := congrArg (fun P : k[X] => P.eval c) hrow
    simp only [eval_sub, eval_mul, eval_pow, eval_C, hc, hwc, mul_zero,
      zero_mul, zero_pow, sub_zero, zero_sub] at hrowc
    have hDKc : D.eval c * K.eval c = 0 := by linear_combination -hrowc
    refine ⟨hwc, w1, hw1, hphi1, hI4q, ?_⟩
    rcases mul_eq_zero.mp hDKc with hDc | hKc
    · left
      obtain ⟨D1, hD1⟩ := dvd_of_two_simple_root_evals_68
        H D hdeg hsimple a c hac ha hc hDa hDc
      refine ⟨hDc, D1, hD1, ?_⟩
      apply mul_left_cancel₀ hH
      linear_combination hrow - b * e * hw1 + K * hD1
    · right
      obtain ⟨K1, hK1⟩ := dvd_of_two_simple_root_evals_68
        H K hdeg hsimple a c hac ha hc hKa hKc
      refine ⟨hKc, K1, hK1, ?_⟩
      apply mul_left_cancel₀ hH
      linear_combination hrow - b * e * hw1 + D * hK1
  · -- the conjugate root misses `w`: allocate through the transverse face
    have hFpack : (A * b - 3 * D).eval a = 0 →
        ∃ F1 : k[X], A * b - 3 * D = H * F1 ∧ b * G = 2 * w * F1 := by
      intro hPa
      have hPc : (A * b - 3 * D).eval c = 0 := by
        simp only [eval_sub, eval_mul, eval_ofNat]
        linear_combination hFc
      obtain ⟨F1, hF1⟩ := dvd_of_two_simple_root_evals_68
        H (A * b - 3 * D) hdeg hsimple a c hac ha hc hPa hPc
      refine ⟨F1, hF1, ?_⟩
      apply mul_left_cancel₀ hH
      linear_combination hleaf + 2 * w * hF1
    rcases eq_or_ne (b.eval a) 0 with hba | hba
    · -- `b` dies at the deep root: the transverse face divides globally
      right; left
      have hPa : (A * b - 3 * D).eval a = 0 := by
        simp only [eval_sub, eval_mul, eval_ofNat]
        linear_combination A.eval a * hba - 3 * hDa
      exact ⟨hwc, hFpack hPa, Or.inl hba⟩
    · obtain ⟨hphi'a, hAW⟩ := hsplita.resolve_left hba
      rcases eq_or_ne (A.eval a) 0 with hAa | hAa
      · -- the cubic coefficient dies: transverse face divides globally
        right; left
        have hPa : (A * b - 3 * D).eval a = 0 := by
          simp only [eval_sub, eval_mul, eval_ofNat]
          linear_combination b.eval a * hAa - 3 * hDa
        obtain ⟨F1, hF1, hbG⟩ := hFpack hPa
        have hGa : G.eval a = 0 := by
          have hkey : b.eval a * G.eval a = 0 := by
            have hev := congrArg (fun P : k[X] => P.eval a) hbG
            simp only [eval_mul, eval_ofNat] at hev
            linear_combination hev + 2 * F1.eval a * hwa
          exact (mul_eq_zero.mp hkey).resolve_left hba
        exact ⟨hwc, ⟨F1, hF1, hbG⟩, Or.inr ⟨hAa, hGa, hphi'a⟩⟩
      · -- transverse residual limb of order two at the deep root
        right; right
        have hw'a : w.derivative.eval a = 0 := hAW.resolve_left hAa
        have hg1 := congrArg (fun P : k[X] => P.derivative.eval a) hG
        simp only [derivative_add, derivative_mul, derivative_ofNat, zero_mul,
          zero_add, eval_add, eval_mul, eval_ofNat] at hg1
        have hGa : G.eval a = 0 := by
          have hkey : H.derivative.eval a * G.eval a = 0 := by
            linear_combination -hg1 + hphi'a + 2 * A.derivative.eval a * hwa +
              2 * A.eval a * hw'a - G.derivative.eval a * ha
          exact (mul_eq_zero.mp hkey).resolve_left (hsimple a ha)
        have hi2 := congrArg
          (fun P : k[X] => P.derivative.derivative.eval a) hI4
        simp only [derivative_add, derivative_mul, derivative_ofNat,
          derivative_zero, zero_mul, zero_add, eval_add, eval_mul, eval_ofNat,
          eval_zero] at hi2
        have hphi''a : phi.derivative.derivative.eval a = 0 := by
          have hkey : b.eval a * phi.derivative.derivative.eval a = 0 := by
            linear_combination hi2 - b.derivative.derivative.eval a * hphia -
              2 * b.derivative.eval a * hphi'a -
              6 * w.derivative.derivative.eval a * hDa -
              12 * D.derivative.eval a * hw'a -
              6 * D.derivative.derivative.eval a * hwa
          exact (mul_eq_zero.mp hkey).resolve_left hba
        have hg2 := congrArg
          (fun P : k[X] => P.derivative.derivative.eval a) hG
        simp only [derivative_add, derivative_mul, derivative_ofNat, zero_mul,
          zero_add, eval_add, eval_mul, eval_ofNat] at hg2
        have htie : H.derivative.eval a * G.derivative.eval a =
            A.eval a * w.derivative.derivative.eval a := by
          linear_combination (-1 / 2 : k) * hg2 + (1 / 2 : k) * hphi''a +
            A.derivative.derivative.eval a * hwa +
            2 * A.derivative.eval a * hw'a -
            (1 / 2 : k) * H.derivative.derivative.eval a * hGa -
            (1 / 2 : k) * G.derivative.derivative.eval a * ha
        have hi3 := congrArg
          (fun P : k[X] => P.derivative.derivative.derivative.eval a) hI4
        simp only [derivative_add, derivative_mul, derivative_ofNat,
          derivative_zero, zero_mul, zero_add, eval_add, eval_mul, eval_ofNat,
          eval_zero] at hi3
        have hI4third :
            b.eval a * phi.derivative.derivative.derivative.eval a +
              18 * w.derivative.derivative.eval a * D.derivative.eval a =
              0 := by
          linear_combination hi3 -
            b.derivative.derivative.derivative.eval a * hphia -
            3 * b.derivative.derivative.eval a * hphi'a -
            3 * b.derivative.eval a * hphi''a -
            6 * w.derivative.derivative.derivative.eval a * hDa -
            18 * D.derivative.derivative.eval a * hw'a -
            6 * D.derivative.derivative.derivative.eval a * hwa
        have hr2 := congrArg
          (fun P : k[X] => P.derivative.derivative.eval a) hrow
        simp only [derivative_add, derivative_sub, derivative_mul,
          derivative_pow, derivative_C, zero_mul, zero_add, eval_sub,
          eval_add, eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero, ha,
          hwa, hw'a, hDa, hKa, zero_pow, mul_zero, add_zero, sub_zero,
          zero_sub] at hr2
        have hrowtie : b.eval a * w.derivative.derivative.eval a * e.eval a =
            2 * D.derivative.eval a * K.derivative.eval a := by
          linear_combination hr2
        have hr3 := congrArg
          (fun P : k[X] => P.derivative.derivative.derivative.eval a) hrow
        simp only [derivative_sub, eval_sub] at hr3
        rw [terminalThirdTripleAt68_eq b w e a, terminalThirdPairAt68_eq D K a,
          terminalThirdCoreLoad68_eq H j a ha] at hr3
        simp only [terminalThirdTripleAt68, terminalThirdPairAt68, hwa, hw'a,
          hDa, hKa, mul_zero, zero_mul, add_zero, zero_add] at hr3
        have hloadtie :
            3 * b.derivative.eval a * w.derivative.derivative.eval a *
                e.eval a +
              b.eval a * w.derivative.derivative.derivative.eval a *
                e.eval a +
              3 * b.eval a * w.derivative.derivative.eval a *
                e.derivative.eval a -
              3 * D.derivative.derivative.eval a * K.derivative.eval a -
              3 * D.derivative.eval a * K.derivative.derivative.eval a =
              6 * j * H.derivative.eval a ^ 3 := by
          linear_combination hr3
        have hlc := congrArg (fun P : k[X] => P.derivative.eval c) hleaf
        simp only [derivative_sub, derivative_mul, derivative_ofNat,
          derivative_zero, zero_mul, zero_add, eval_sub, eval_add, eval_mul,
          eval_ofNat, eval_zero, hc, mul_zero, add_zero, zero_sub] at hlc
        have hctie : H.derivative.eval c * b.eval c * G.eval c =
            2 * w.eval c *
              (A.derivative.eval c * b.eval c +
                A.eval c * b.derivative.eval c -
                3 * D.derivative.eval c) := by
          linear_combination hlc + 2 * w.derivative.eval c * hFc
        exact ⟨hwc, hba, hAa, hw'a, hphi'a, hphi''a, hGa, htie, hI4third,
          hrowtie, hloadtie, hctie⟩

end RefinedIIIConjugateCommonAlgebra68

section RefinedIIIConjugateCommonSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing refinement of the conjugate packet.  Every deep root keeps
the full matching/global packet; if its conjugate lies on the common
component, the exact transverse split is attached to the canonical
quotients through the all-roots lower-third selector at the deep root. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateCommonTransversePacket
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
        ∃ phi2 k2 : k[X], phi1 = H * phi2 ∧ k1 = H * k2 ∧
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
           ∀ a : k, H.eval a = 0 → w2.eval a = 0 →
             phi2.eval a = 0 → d2.eval a = 0 → k2.eval a = 0 →
             ∃ c : k, c ≠ a ∧ H.eval c = 0 ∧
               terminalRefinedIIIConjugateMatching68
                 H A0 b2 d2 w2 phi2 eDot k2 j c ∧
               terminalRefinedIIIConjugateGlobalSplit68
                 H A0 b2 d2 w2 phi2 eDot k2 j ∧
               (A0.eval c * b2.eval c - 3 * d2.eval c = 0 →
                 phi2.eval c + 2 * A0.eval c * w2.eval c = 0 →
                 terminalRefinedIIIConjugateCommonTransverse68
                   H A0 b2 d2 w2 phi2 eDot k2 j a c))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorRefinedIIIPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hroots⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hrow hroots ⊢
  intro a ha hwa hphia hDa hKa
  let A0 := cubicANumerator68 t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hclass : ∀ x : k, H.eval x = 0 →
      terminalPhiDivisorLowerThirdClassification68 (A0.eval x)
        (H.derivative.eval x) (6 * j * (H.derivative.eval x) ^ 3)
        b2 d2 w2 phi2 eDot k2 x := fun x hx => (hroots x hx).1
  obtain ⟨c, hca, hc, hmatch⟩ := terminalRefinedIII_conjugate_matching_68
    H A0 b2 d2 w2 phi2 eDot k2 j a hdeg hsimple ha hwa hphia hDa hKa hclass
  have hglobal := terminalRefinedIII_conjugate_global_split_68
    H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
    hwa hphia hDa hKa hI4 hrow hmatch
  refine ⟨c, hca, hc, hmatch, hglobal, ?_⟩
  intro hFc hGc
  have hcls := hclass a ha
  dsimp only [terminalPhiDivisorLowerThirdClassification68] at hcls
  exact terminalRefinedIII_conjugateCommon_transverse_68
    H A0 b2 d2 w2 phi2 eDot k2 j a c hdeg hsimple ha hc hca.symm
    hwa hphia hDa hKa hI4 hrow (hcls.2.2.2.2 hwa hphia hDa) hFc hGc

end RefinedIIIConjugateCommonSource68

end Max11DegreeRoutes
