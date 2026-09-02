import Fable68ScaleTwoRefinedIIIConjugateCommonTransverseScratch

/-! # Finite refinement of the common-transverse conjugate packet

Both cheap finite faces of the common conjugate leaf are consumed; the
`H^2`-row loaded Taylor rung is deliberately left untouched.

* In the `F`-collapse branch the cancelled `G`-row is evaluated at the
  conjugate root, `b(c)*G(c) = 2*w(c)*F1(c)`, and the terminal row at `c`
  combines with the common face `A(c)*b(c) = 3*D(c)` into the exact product
  `b(c) * (3*w(c)*e(c) - A(c)*K(c)) = 0`.  Its allocation is decisive: if
  `b(c) = 0` then `D(c) = 0` and `F1(c) = 0`, both `D` and `b*w` divide by
  the core, and the leaf merges into the conjugate component-II global
  shape (`D = H*D1`, `b*w = H*BW`, `b*phi + 6*H*w*D1 = 0`,
  `BW*e - D1*K = C j * H^2`) with the extra `F`-collapse data
  `A*b = H*(F1 + 3*D1)` and, when the deep selector chose `b(a) = 0`, the
  full divisibility `H ∣ b`; otherwise `b(c) ≠ 0` and the conjugate root
  carries the exact `K`-tie `3*w(c)*e(c) = A(c)*K(c)`.
* In the transverse residual limb the order-two packet splits on `w''(a)`:
  if `w''(a) = 0` the retained ties collapse through the units `H'(a)`,
  `b(a)` to `G'(a) = 0`, `phi'''(a) = 0` and the product face
  `D'(a)*K'(a) = 0`, whose exclusive allocation reduces the j-loaded third
  row to `b*w'''*e - 3*D''*K' = 6*j*H'^3` resp.
  `b*w'''*e - 3*D'*K'' = 6*j*H'^3` at `a`; if `w''(a) ≠ 0` the tie
  `H'(a)*G'(a) = A(a)*w''(a)` pins the unit `G'(a) ≠ 0` and the row/I4
  ties become the exact equivalences `e(a) = 0 ↔ D'(a)*K'(a) = 0` and
  `phi'''(a) = 0 ↔ D'(a) = 0`.
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

section RefinedIIIConjugateCommonNextAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Refined transverse split of the common conjugate component.  The
component-III collapse branch is retained verbatim; the `F`-collapse branch
carries the conjugate evaluation of the cancelled `G`-row together with the
exclusive `b(c)`-allocation (component-II merge versus conjugate `K`-tie);
the transverse residual limb carries the exclusive `w''(a)`-dichotomy. -/
def terminalRefinedIIIConjugateCommonTransverseNext68
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
        A * b - 3 * D = H * F1 ∧ b * G = 2 * w * F1 ∧
        b.eval c * G.eval c = 2 * w.eval c * F1.eval c ∧
        ((b.eval c = 0 ∧ D.eval c = 0 ∧ F1.eval c = 0 ∧
          (b.eval a = 0 → H ∣ b) ∧
          ∃ D1 BW : k[X],
            D = H * D1 ∧ b * w = H * BW ∧
            A * b = H * (F1 + 3 * D1) ∧
            b * phi + 6 * H * w * D1 = 0 ∧
            BW * e - D1 * K = C j * H ^ 2) ∨
         (b.eval c ≠ 0 ∧
          3 * w.eval c * e.eval c = A.eval c * K.eval c))) ∧
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
            3 * D.derivative.eval c) ∧
      ((w.derivative.derivative.eval a = 0 ∧
        G.derivative.eval a = 0 ∧
        phi.derivative.derivative.derivative.eval a = 0 ∧
        D.derivative.eval a * K.derivative.eval a = 0 ∧
        ((D.derivative.eval a = 0 ∧
           b.eval a * w.derivative.derivative.derivative.eval a * e.eval a -
             3 * D.derivative.derivative.eval a * K.derivative.eval a =
             6 * j * H.derivative.eval a ^ 3) ∨
         (D.derivative.eval a ≠ 0 ∧ K.derivative.eval a = 0 ∧
           b.eval a * w.derivative.derivative.derivative.eval a * e.eval a -
             3 * D.derivative.eval a * K.derivative.derivative.eval a =
             6 * j * H.derivative.eval a ^ 3))) ∨
       (w.derivative.derivative.eval a ≠ 0 ∧
        G.derivative.eval a ≠ 0 ∧
        (e.eval a = 0 ↔
          D.derivative.eval a * K.derivative.eval a = 0) ∧
        (phi.derivative.derivative.derivative.eval a = 0 ↔
          D.derivative.eval a = 0)))))

/-- The transverse common packet refines to the `Next` form: the conjugate
evaluation of the cancelled `G`-row allocates through the terminal row at
the conjugate root, and the residual limb splits exclusively on `w''(a)`.
Only the retained ties, the global I4/terminal rows and the unit conditions
are consumed; no new loaded-row coefficient is opened. -/
theorem terminalRefinedIII_conjugateCommon_transverseNext_68
    (H A b D w phi e K : k[X]) (j a c : k)
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (ha : H.eval a = 0) (hc : H.eval c = 0) (hac : a ≠ c)
    (hwa : w.eval a = 0) (hphia : phi.eval a = 0)
    (hDa : D.eval a = 0) (hKa : K.eval a = 0)
    (hI4 : b * phi + 6 * w * D = 0)
    (hrow : b * w * e - D * K = C j * H ^ 3)
    (hFc : A.eval c * b.eval c - 3 * D.eval c = 0)
    (hprev : terminalRefinedIIIConjugateCommonTransverse68
      H A b D w phi e K j a c) :
    terminalRefinedIIIConjugateCommonTransverseNext68
      H A b D w phi e K j a c := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  obtain ⟨G, hG, hleaf, hsplit⟩ := hprev
  refine ⟨G, hG, hleaf, ?_⟩
  rcases hsplit with hIII | hF | htrans
  · exact Or.inl hIII
  · -- `F`-collapse branch: evaluate the cancelled `G`-row at the conjugate
    -- root and allocate through the terminal row there.
    right; left
    obtain ⟨hwc, ⟨F1, hF1, hbG⟩, hsel⟩ := hF
    have heval : b.eval c * G.eval c = 2 * w.eval c * F1.eval c := by
      have hev := congrArg (fun P : k[X] => P.eval c) hbG
      simp only [eval_mul, eval_ofNat] at hev
      linear_combination hev
    have hrowc : b.eval c * w.eval c * e.eval c -
        D.eval c * K.eval c = 0 := by
      have hev := congrArg (fun P : k[X] => P.eval c) hrow
      simp only [eval_sub, eval_mul, eval_pow, eval_C] at hev
      rw [hc] at hev
      linear_combination hev
    refine ⟨hwc, ⟨F1, hF1, hbG, heval, ?_⟩, hsel⟩
    rcases eq_or_ne (b.eval c) 0 with hbc | hbc
    · -- `b` dies at the conjugate root: component-II merge.
      left
      have hDc : D.eval c = 0 := by
        linear_combination (-1 / 3 : k) * hFc + (A.eval c / 3) * hbc
      have hF1c : F1.eval c = 0 := by
        have hkey : w.eval c * (2 * F1.eval c) = 0 := by
          linear_combination -heval + G.eval c * hbc
        have h2 := (mul_eq_zero.mp hkey).resolve_left hwc
        linear_combination (1 / 2 : k) * h2
      obtain ⟨D1, hD1⟩ := dvd_of_two_simple_root_evals_68
        H D hdeg hsimple a c hac ha hc hDa hDc
      have hbwa : (b * w).eval a = 0 := by simp [eval_mul, hwa]
      have hbwc : (b * w).eval c = 0 := by simp [eval_mul, hbc]
      obtain ⟨BW, hBW⟩ := dvd_of_two_simple_root_evals_68
        H (b * w) hdeg hsimple a c hac ha hc hbwa hbwc
      refine ⟨hbc, hDc, hF1c,
        fun hba0 => dvd_of_two_simple_root_evals_68
          H b hdeg hsimple a c hac ha hc hba0 hbc,
        D1, BW, hD1, hBW, ?_, ?_, ?_⟩
      · linear_combination hF1 + 3 * hD1
      · linear_combination hI4 - 6 * w * hD1
      · apply mul_left_cancel₀ hH
        linear_combination hrow - e * hBW + K * hD1
    · -- `b` survives at the conjugate root: exact conjugate `K`-tie.
      right
      refine ⟨hbc, ?_⟩
      have hkey : b.eval c *
          (3 * w.eval c * e.eval c - A.eval c * K.eval c) = 0 := by
        linear_combination 3 * hrowc - K.eval c * hFc
      have h := (mul_eq_zero.mp hkey).resolve_left hbc
      linear_combination h
  · -- transverse residual limb: exclusive split on `w''(a)`.
    right; right
    obtain ⟨hwc, hba, hAa, hw1a, hphi1a, hphi2a, hGa, htie, hI4third,
      hrowtie, hloadtie, hctie⟩ := htrans
    refine ⟨hwc, hba, hAa, hw1a, hphi1a, hphi2a, hGa, htie, hI4third,
      hrowtie, hloadtie, hctie, ?_⟩
    rcases eq_or_ne (w.derivative.derivative.eval a) 0 with hw2a | hw2a
    · -- `w''(a) = 0`: the ties collapse through the units `H'(a)`, `b(a)`.
      left
      have hGd : G.derivative.eval a = 0 := by
        have hkey : H.derivative.eval a * G.derivative.eval a = 0 := by
          linear_combination htie + A.eval a * hw2a
        exact (mul_eq_zero.mp hkey).resolve_left (hsimple a ha)
      have hphi3 : phi.derivative.derivative.derivative.eval a = 0 := by
        have hkey : b.eval a *
            phi.derivative.derivative.derivative.eval a = 0 := by
          linear_combination hI4third - 18 * D.derivative.eval a * hw2a
        exact (mul_eq_zero.mp hkey).resolve_left hba
      have hDK : D.derivative.eval a * K.derivative.eval a = 0 := by
        linear_combination (-1 / 2 : k) * hrowtie +
          (1 / 2 : k) * b.eval a * e.eval a * hw2a
      refine ⟨hw2a, hGd, hphi3, hDK, ?_⟩
      rcases eq_or_ne (D.derivative.eval a) 0 with hDd | hDd
      · left
        refine ⟨hDd, ?_⟩
        linear_combination hloadtie -
          (3 * b.derivative.eval a * e.eval a +
            3 * b.eval a * e.derivative.eval a) * hw2a +
          3 * K.derivative.derivative.eval a * hDd
      · right
        have hKd : K.derivative.eval a = 0 :=
          (mul_eq_zero.mp hDK).resolve_left hDd
        refine ⟨hDd, hKd, ?_⟩
        linear_combination hloadtie -
          (3 * b.derivative.eval a * e.eval a +
            3 * b.eval a * e.derivative.eval a) * hw2a +
          3 * D.derivative.derivative.eval a * hKd
    · -- `w''(a) ≠ 0`: unit pin on `G'(a)` and exact equivalences.
      right
      have hGd : G.derivative.eval a ≠ 0 := by
        intro h0
        have hkey : A.eval a * w.derivative.derivative.eval a = 0 := by
          linear_combination -htie + H.derivative.eval a * h0
        rcases mul_eq_zero.mp hkey with h | h
        · exact hAa h
        · exact hw2a h
      refine ⟨hw2a, hGd, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro he
        linear_combination (-1 / 2 : k) * hrowtie +
          (1 / 2 : k) * b.eval a * w.derivative.derivative.eval a * he
      · intro hDK
        have hkey : b.eval a *
            (w.derivative.derivative.eval a * e.eval a) = 0 := by
          linear_combination hrowtie + 2 * hDK
        have h2 := (mul_eq_zero.mp hkey).resolve_left hba
        exact (mul_eq_zero.mp h2).resolve_left hw2a
      · intro h3
        have hkey : w.derivative.derivative.eval a *
            (18 * D.derivative.eval a) = 0 := by
          linear_combination hI4third - b.eval a * h3
        have h18 := (mul_eq_zero.mp hkey).resolve_left hw2a
        linear_combination (1 / 18 : k) * h18
      · intro hDd
        have hkey : b.eval a *
            phi.derivative.derivative.derivative.eval a = 0 := by
          linear_combination hI4third -
            18 * w.derivative.derivative.eval a * hDd
        exact (mul_eq_zero.mp hkey).resolve_left hba

end RefinedIIIConjugateCommonNextAlgebra68

section RefinedIIIConjugateCommonNextSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing refinement of the conjugate common-transverse packet.
Every deep root keeps the matching/global packet; if its conjugate lies on
the common component, the refined transverse split with the conjugate
`G`-row allocation and the `w''(a)`-dichotomy is attached to the canonical
quotients. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOnePhiDivisorConjugateCommonTransverseNextPacket
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
                 terminalRefinedIIIConjugateCommonTransverseNext68
                   H A0 b2 d2 w2 phi2 eDot k2 j a c))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hbranch⟩ :=
    S.terminalAfterLowerOnePhiDivisorConjugateCommonTransversePacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, ?_⟩
  intro hphi
  obtain ⟨phi2, k2, hphi2, hk2, hI4, hrow, hroots⟩ := hbranch hphi
  refine ⟨phi2, k2, hphi2, hk2, hI4, hrow, ?_⟩
  dsimp only at hrow hroots ⊢
  intro a ha hwa hphia hDa hKa
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  obtain ⟨c, hca, hc, hmatch, hglobal, htransv⟩ :=
    hroots a ha hwa hphia hDa hKa
  refine ⟨c, hca, hc, hmatch, hglobal, ?_⟩
  intro hFc hGc
  exact terminalRefinedIII_conjugateCommon_transverseNext_68
    H _ b2 d2 w2 phi2 _ k2 j a c hdeg hsimple ha hc hca.symm
    hwa hphia hDa hKa hI4 hrow hFc (htransv hFc hGc)

end RefinedIIIConjugateCommonNextSource68

end Max11DegreeRoutes
