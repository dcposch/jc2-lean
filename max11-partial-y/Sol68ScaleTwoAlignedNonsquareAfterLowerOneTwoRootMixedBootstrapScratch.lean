import Sol68ScaleTwoAlignedNonsquareAfterLowerOneTwoRootAllocationScratch

/-! # Local bootstrap on the mixed coordinate/double-root allocation -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section MixedRootBootstrapAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem X_sub_C_sq_dvd_of_eval_derivative_zero_68
    (f : k[X]) (a : k) (hf : f.eval a = 0)
    (hf' : f.derivative.eval a = 0) :
    (X - C a) ^ 2 ∣ f := by
  have hlin : X - C a ∣ f := by
    rw [dvd_iff_isRoot]
    exact hf
  obtain ⟨f1, hf1⟩ := hlin
  have hf1root : f1.eval a = 0 := by
    have hder := congrArg (fun P : k[X] => P.derivative.eval a) hf1
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
      eval_add, eval_mul, eval_sub, eval_one, eval_X, eval_C, sub_self,
      zero_mul, one_mul, add_zero] at hder
    simpa using hder.symm.trans hf'
  have hlin1 : X - C a ∣ f1 := by
    rw [dvd_iff_isRoot]
    exact hf1root
  obtain ⟨f2, hf2⟩ := hlin1
  refine ⟨f2, ?_⟩
  rw [hf1, hf2]
  ring

/-- A nonzero root value is the exact coprimality needed to cancel every
power of the corresponding linear factor. -/
theorem X_sub_C_pow_dvd_mul_cancel_right_68
    (f u : k[X]) (a : k) (n : ℕ) (hu : u.eval a ≠ 0)
    (hdiv : (X - C a) ^ n ∣ f * u) :
    (X - C a) ^ n ∣ f := by
  have hcop : IsCoprime (X - C a) u := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := k) k]
    intro z
    rw [aeval_def, aeval_def]
    by_cases hz : z = a
    · right
      simpa [hz] using hu
    · left
      simpa using sub_ne_zero.mpr hz
  exact hcop.pow_left.dvd_of_dvd_mul_right hdiv

/-- At the complementary double-zero root, the two exact global rows
bootstrap the local orders from `(2,2)` to `(5,4)`.  This uses only that
`phi` and `kap` are units at that root; no assumption is made at the other
root of the quadratic core. -/
theorem terminalAfterLowerOne_mixedRoot_bootstrap_68
    (H b phi w d eDot kap : k[X]) (j a : k)
    (ha : H.eval a = 0)
    (hphi : phi.eval a ≠ 0) (hkap : kap.eval a ≠ 0)
    (hb0 : b.eval a = 0) (hb1 : b.derivative.eval a = 0)
    (hd0 : d.eval a = 0) (hd1 : d.derivative.eval a = 0)
    (hI4 : b * phi + (6 : k[X]) * H * w * d = 0)
    (hrow : H * b * w * eDot - d * kap = C j * H ^ 4) :
    (X - C a) ^ 5 ∣ b ∧ (X - C a) ^ 4 ∣ d := by
  let L : k[X] := X - C a
  have hLH : L ∣ H := by
    dsimp only [L]
    rw [dvd_iff_isRoot]
    exact ha
  have hb2 : L ^ 2 ∣ b := by
    simpa only [L] using X_sub_C_sq_dvd_of_eval_derivative_zero_68
      b a hb0 hb1
  have hd2 : L ^ 2 ∣ d := by
    simpa only [L] using X_sub_C_sq_dvd_of_eval_derivative_zero_68
      d a hd0 hd1
  obtain ⟨H1, hH1⟩ := hLH
  obtain ⟨b2, hb2eq⟩ := hb2
  obtain ⟨d2, hd2eq⟩ := hd2
  have hright3 : L ^ 3 ∣ (6 : k[X]) * H * w * d := by
    refine ⟨(6 : k[X]) * H1 * w * d2, ?_⟩
    rw [hH1, hd2eq]
    ring
  have hbphi3 : L ^ 3 ∣ b * phi := by
    obtain ⟨z, hz⟩ := hright3
    refine ⟨-z, ?_⟩
    linear_combination hI4 - hz
  have hb3 : L ^ 3 ∣ b := by
    simpa only [L] using X_sub_C_pow_dvd_mul_cancel_right_68
      b phi a 3 hphi (by simpa only [L] using hbphi3)
  obtain ⟨b3, hb3eq⟩ := hb3
  have hleft4 : L ^ 4 ∣ H * b * w * eDot := by
    refine ⟨H1 * b3 * w * eDot, ?_⟩
    rw [hH1, hb3eq]
    ring
  have hload4 : L ^ 4 ∣ C j * H ^ 4 := by
    refine ⟨C j * H1 ^ 4, ?_⟩
    rw [hH1]
    ring
  have hdkap4 : L ^ 4 ∣ d * kap := by
    obtain ⟨z1, hz1⟩ := hleft4
    obtain ⟨z2, hz2⟩ := hload4
    refine ⟨z1 - z2, ?_⟩
    linear_combination -hrow + hz1 - hz2
  have hd4 : L ^ 4 ∣ d := by
    simpa only [L] using X_sub_C_pow_dvd_mul_cancel_right_68
      d kap a 4 hkap (by simpa only [L] using hdkap4)
  obtain ⟨d4, hd4eq⟩ := hd4
  have hright5 : L ^ 5 ∣ (6 : k[X]) * H * w * d := by
    refine ⟨(6 : k[X]) * H1 * w * d4, ?_⟩
    rw [hH1, hd4eq]
    ring
  have hbphi5 : L ^ 5 ∣ b * phi := by
    obtain ⟨z, hz⟩ := hright5
    refine ⟨-z, ?_⟩
    linear_combination hI4 - hz
  have hb5 : L ^ 5 ∣ b := by
    simpa only [L] using X_sub_C_pow_dvd_mul_cancel_right_68
      b phi a 5 hphi (by simpa only [L] using hbphi5)
  refine ⟨by simpa only [L] using hb5, ?_⟩
  simpa only [L] using (show L ^ 4 ∣ d from ⟨d4, hd4eq⟩)

end MixedRootBootstrapAlgebra68

section MixedRootBootstrapSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing sharpening of the sole genuinely mixed two-root family.
At its complementary root, `b₂` has order at least five and `d₂` order at
least four.  The all-coordinate family and all `phi=0` derivative faces are
preserved verbatim. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneMixedBootstrapPacket
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
          d2.eval b0 = 0 ∧ d2.derivative.eval b0 = 0 ∧ k1.eval b0 ≠ 0 ∧
          (Polynomial.X - C b0) ^ 5 ∣ b2 ∧
          (Polynomial.X - C b0) ^ 4 ∣ d2) ∧
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
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, halloc, hsqB, hsqD, hfaces⟩ :=
    S.terminalAfterLowerOneTwoRootPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hrow' : H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4 := by
    simpa only [A0, C0, E0, eDot] using hrow
  have halloc' : H ∣ r * phi1 ∨
      ∃ a b0 : k, a ≠ b0 ∧ H.eval a = 0 ∧ H.eval b0 = 0 ∧
        (r.eval a = 0 ∨ phi1.eval a = 0) ∧
        r.eval b0 ≠ 0 ∧ phi1.eval b0 ≠ 0 ∧
        b2.eval b0 = 0 ∧ b2.derivative.eval b0 = 0 ∧
        d2.eval b0 = 0 ∧ d2.derivative.eval b0 = 0 ∧ k1.eval b0 ≠ 0 ∧
        (Polynomial.X - C b0) ^ 5 ∣ b2 ∧
        (Polynomial.X - C b0) ^ 4 ∣ d2 := by
    rcases halloc with hboth | hmixed
    · exact Or.inl hboth
    · right
      obtain ⟨a, b0, hab, ha, hb0, hcoord, hrb, hphib,
        hbz, hbz', hdz, hdz', hkne⟩ := hmixed
      have hboot := terminalAfterLowerOne_mixedRoot_bootstrap_68
        H b2 phi1 w2 d2 eDot k1 j b0 hb0 hphib hkne
        hbz hbz' hdz hdz' hI4 hrow'
      exact ⟨a, b0, hab, ha, hb0, hcoord, hrb, hphib,
        hbz, hbz', hdz, hdz', hkne, hboot.1, hboot.2⟩
  exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
    ht, hX, hY, hI4, hrow, halloc', hsqB, hsqD, hfaces⟩

end MixedRootBootstrapSource68

end Max11DegreeRoutes
