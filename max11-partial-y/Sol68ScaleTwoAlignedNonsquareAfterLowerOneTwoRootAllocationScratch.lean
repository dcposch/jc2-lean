import Sol68ScaleTwoAlignedNonsquareAfterLowerOneLowerZeroTransportScratch

/-! # Two-root classification after deleting the pure load wall -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section TwoRootAllocationAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Once the all-pure component is removed, the two simple roots of the
quadratic core have exactly two global possibilities: both lie on the
coordinate divisor `r*phi`, or one lies there and a distinct complementary
root carries the simultaneous double-zero component.  In either case the
weighted products have two full core factors. -/
theorem terminalAfterLowerOne_twoRoot_allocation_68
    (H r phi b d kap : k[X])
    (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hroots : ∀ a : k, H.eval a = 0 →
      r.eval a = 0 ∨ phi.eval a = 0 ∨
        (b.eval a = 0 ∧ b.derivative.eval a = 0 ∧
         d.eval a = 0 ∧ d.derivative.eval a = 0 ∧ kap.eval a ≠ 0))
    (hnotpure : ¬ (∀ a : k, H.eval a = 0 →
      r.eval a ≠ 0 ∧ phi.eval a ≠ 0)) :
    (H ∣ r * phi ∨
      ∃ a b0 : k, a ≠ b0 ∧ H.eval a = 0 ∧ H.eval b0 = 0 ∧
        (r.eval a = 0 ∨ phi.eval a = 0) ∧
        r.eval b0 ≠ 0 ∧ phi.eval b0 ≠ 0 ∧
        b.eval b0 = 0 ∧ b.derivative.eval b0 = 0 ∧
        d.eval b0 = 0 ∧ d.derivative.eval b0 = 0 ∧ kap.eval b0 ≠ 0) ∧
      H ^ 2 ∣ (r * phi) ^ 2 * b ∧
      H ^ 2 ∣ (r * phi) ^ 2 * d := by
  classical
  have hcoordinate : ∃ a : k, H.eval a = 0 ∧
      (r.eval a = 0 ∨ phi.eval a = 0) := by
    by_contra hnone
    push_neg at hnone
    exact hnotpure (fun a ha => ⟨(hnone a ha).1, (hnone a ha).2⟩)
  have hweightedB : H ^ 2 ∣ (r * phi) ^ 2 * b := by
    apply sq_dvd_of_eval_derivative_zero_simple_natDegree_two_68
      H ((r * phi) ^ 2 * b) hdeg hsimple
    intro a ha
    rcases hroots a ha with hr | hp | hdouble
    · constructor
      · simp [eval_mul, hr]
      · simp [derivative_mul, derivative_pow, eval_mul, hr]
    · constructor
      · simp [eval_mul, hp]
      · simp [derivative_mul, derivative_pow, eval_mul, hp]
    · constructor
      · simp [eval_mul, hdouble.1]
      · simp [derivative_mul, derivative_pow, eval_mul,
          hdouble.1, hdouble.2.1]
  have hweightedD : H ^ 2 ∣ (r * phi) ^ 2 * d := by
    apply sq_dvd_of_eval_derivative_zero_simple_natDegree_two_68
      H ((r * phi) ^ 2 * d) hdeg hsimple
    intro a ha
    rcases hroots a ha with hr | hp | hdouble
    · constructor
      · simp [eval_mul, hr]
      · simp [derivative_mul, derivative_pow, eval_mul, hr]
    · constructor
      · simp [eval_mul, hp]
      · simp [derivative_mul, derivative_pow, eval_mul, hp]
    · constructor
      · simp [eval_mul, hdouble.2.2.1]
      · simp [derivative_mul, derivative_pow, eval_mul,
          hdouble.2.2.1, hdouble.2.2.2.1]
  refine ⟨?_, hweightedB, hweightedD⟩
  by_cases hboth : H ∣ r * phi
  · exact Or.inl hboth
  · right
    obtain ⟨a, ha, hcoordinateA⟩ := hcoordinate
    have hcomplement : ∃ b0 : k, H.eval b0 = 0 ∧
        (r * phi).eval b0 ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      exact hboth (dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
        (fun b0 hb0 => hnone b0 hb0))
    obtain ⟨b0, hb0, hrphib⟩ := hcomplement
    have hrb : r.eval b0 ≠ 0 := by
      intro hr0
      exact hrphib (by simp [eval_mul, hr0])
    have hpb : phi.eval b0 ≠ 0 := by
      intro hp0
      exact hrphib (by simp [eval_mul, hp0])
    have hdouble := hroots b0 hb0
    rcases hdouble with hr0 | hp0 | hdouble
    · exact False.elim (hrb hr0)
    · exact False.elim (hpb hp0)
    · refine ⟨a, b0, ?_, ha, hb0, hcoordinateA, hrb, hpb,
        hdouble.1, hdouble.2.1, hdouble.2.2.1,
        hdouble.2.2.2.1, hdouble.2.2.2.2⟩
      intro hab
      subst b0
      rcases hcoordinateA with hra | hpa
      · exact hrb hra
      · exact hpb hpa

end TwoRootAllocationAlgebra68

section TwoRootAllocationSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Exact source-facing two-root packet.  It combines the lower-zero deletion,
the mixed-component derivative faces, and the simultaneous double-zero data
without identifying the two distinct roots by an arbitrary enumeration. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneTwoRootPacket
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
      (H ∣ r * phi1 ∨
        ∃ a b0 : k, a ≠ b0 ∧ H.eval a = 0 ∧ H.eval b0 = 0 ∧
          (r.eval a = 0 ∨ phi1.eval a = 0) ∧
          r.eval b0 ≠ 0 ∧ phi1.eval b0 ≠ 0 ∧
          b2.eval b0 = 0 ∧ b2.derivative.eval b0 = 0 ∧
          d2.eval b0 = 0 ∧ d2.derivative.eval b0 = 0 ∧ k1.eval b0 ≠ 0) ∧
      H ^ 2 ∣ (r * phi1) ^ 2 * b2 ∧
      H ^ 2 ∣ (r * phi1) ^ 2 * d2 ∧
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
      _hg, _hgr, ht, hX, hY, _hb1, _hd1, _hw1, _hphi, _hb2, _hd2,
      _hw2, hI4, hrow, hroots, _hpure⟩ :=
    S.terminalAfterLowerOneDoubleZeroPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  -- Apply the transported lower-zero row to these same canonical quotients.
  have hnotpure : ¬ (∀ a : k, H.eval a = 0 →
      r.eval a ≠ 0 ∧ phi1.eval a ≠ 0) := by
    intro hall
    have hpure := _hpure hall
    obtain ⟨b5, d4, hb5, hd4, hI4f, hrowf, hrootprod⟩ := hpure
    -- Reuse the already kernel-checked source deletion by rebuilding exactly
    -- its canonical witnesses rather than appealing to witness choice.
    have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
    let A0 := cubicANumerator68 t r
    let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
    let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r
    have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
      fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
        NonsquarePolynomial46.not_sq ha
    have hdegree : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hdeg]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegree
    have hd4ne : d4.eval a ≠ 0 := by
      intro hd4z
      have hp := congrArg id (hrootprod a ha)
      rw [hd4z, zero_mul] at hp
      exact hj (neg_eq_zero.mp hp.symm)
    have hW1 : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
      dsimp only [A0, C0, terminalScaledW68]
      rw [← _hw1]
      simp only [cubicWNumerator68]
    have hW2 : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w2 := by
      rw [hW1, _hw2]
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
      rw [← _hphi, ← _hb1]
      simp only [cubicPhiNumerator68]
    have hbshape : b1 = H ^ 6 * b5 := by rw [_hb2, hb5]; ring
    have hdshape : d1 = H ^ 5 * d4 := by rw [_hd2, hd4]; ring
    have hEshape : E0 = C (1 / 27 : k) * A0 ^ 3 +
        C (3 / 8 : k) * H * phi1 +
        H ^ 2 * (C (3 / 2 : k) * A0 * w2 -
          C (1 / 2 * S.gamma : k) * A0) -
        C (3 / 4 * S.epsilon : k) * H ^ 3 +
        C (1 / 9 : k) * (H * (H ^ 6 * b5)) ^ 2 := by
      apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
      have hPm := congrArg (algebraMap k[X] (RatFunc k)) hPhi
      have hCm := congrArg (algebraMap k[X] (RatFunc k)) hCshape
      dsimp only [terminalScaledPhi68] at hPm
      simp only [map_add, map_sub, map_neg, map_mul, map_pow,
        RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one] at hPm hCm ⊢
      have hbm := congrArg (algebraMap k[X] (RatFunc k)) hbshape
      simp only [map_mul, map_pow] at hbm
      rw [hbm] at hPm
      linear_combination (3 / 8 : RatFunc k) * hPm +
        (2 / 3 * algebraMap k[X] (RatFunc k) A0) * hCm
    have htransport := S.terminalLowerZeroClearedTransport_source (H := H)
      hp hp6 _hg _hgr ht hX hY
    obtain ⟨hAred, hBred, hCred, hDred, hEred⟩ :=
      cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
        (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
    have hbred : terminalGReducedB68 r X Yd = b1 := by
      apply mul_left_cancel₀ hH
      rw [← hBred, ← _hb1]
    have hdred : terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2) =
        d1 := by
      apply mul_left_cancel₀ hH
      rw [← hDred, ← _hd1]
    have hlower : terminalLowerZeroCleared68 H A0 b1 C0 d1 E0
        S.alpha S.gamma S.epsilon S.eta = 0 := by
      simpa only [A0, C0, E0, ← hAred, hbred, ← hCred, hdred, ← hEred]
        using htransport
    exact terminalLowerZero_pureLoadWall_impossible_68
      H A0 b1 C0 d1 E0 b5 d4 phi1 w2
      S.alpha S.gamma S.epsilon S.eta a ha (hsimple a ha) hd4ne
      (hall a ha).2 hbshape hdshape hCshape hEshape hlower
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  obtain ⟨halloc, hsqB, hsqD⟩ :=
    terminalAfterLowerOne_twoRoot_allocation_68 H r phi1 b2 d2 k1
      hdeg hsimple hroots hnotpure
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hrow' : H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4 := by
    simpa only [A0, C0, E0, eDot] using hrow
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
    ht, hX, hY, hI4, hrow, halloc, hsqB, hsqD, hfaces⟩

end TwoRootAllocationSource68

end Max11DegreeRoutes
