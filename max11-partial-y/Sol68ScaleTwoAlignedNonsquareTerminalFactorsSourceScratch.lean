import Sol68ScaleTwoAlignedNonsquareTerminalFactorsScratch

/-! # Source assembly of the terminal cubic-defect factors -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

section RefinedTerminalBranches68

variable {F : Type*} [Field F] [CharZero F]

/-- Each transverse terminal component fixes the two last-row cores `w,d`
as explicit multiples of `b`. -/
theorem terminalQuotientFace_cubicDefect_refinedSplit_68
    (r X Yd p2 b d w phi : F)
    (hb : b = (Yd - 6 * r * X) / 27)
    (hd : d = -(1 / 3 : F) * r * p2 + (1 / 324 : F) * r ^ 2 * Yd -
      (1 / 162 : F) * r ^ 3 * X)
    (hw : w = (4 / 9 : F) * p2 - (2 / 243 : F) * r * Yd +
      (8 / 243 : F) * r ^ 2 * X)
    (hphi : phi = (2 / 9 : F) * r ^ 2 * p2 -
      (7 / 2187 : F) * r ^ 3 * Yd + (8 / 729 : F) * r ^ 4 * X)
    (hI4 : b * phi + 6 * w * d = 0) :
    r = 0 ∨
      ((9 * r ^ 2 * X - 2 * r * Yd + 81 * p2 = 0) ∧
        w = (2 / 27 : F) * r * b ∧ d = -(5 / 36 : F) * r ^ 2 * b) ∨
      ((3 * r ^ 2 * X - r * Yd + 81 * p2 = 0) ∧
        w = -(2 / 27 : F) * r * b ∧ d = -(1 / 36 : F) * r ^ 2 * b) := by
  rcases terminalQuotientFace_cubicDefect_split_68 r X Yd p2 b d w phi
      hb hd hw hphi hI4 with hr | hleft | hright
  · exact Or.inl hr
  · right; left
    refine ⟨hleft, ?_, ?_⟩
    · rw [hb, hw]
      linear_combination (4 / 729 : F) * hleft
    · rw [hb, hd]
      linear_combination (-1 / 243 : F) * r * hleft
  · right; right
    refine ⟨hright, ?_, ?_⟩
    · rw [hb, hw]
      linear_combination (4 / 729 : F) * hright
    · rw [hb, hd]
      linear_combination (-1 / 243 : F) * r * hright

end RefinedTerminalBranches68

section TerminalFactorsSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Polynomial-ring version of the quotient formulas. -/
theorem terminalQuotientFactorsPolynomial_of_cubicDefects_68
    (core r t v p0 p1 p2 : k[X]) (gamma epsilon : k)
    (X Yd b d w phi : k[X]) (hcore : core ≠ 0)
    (ht : (3 : k[X]) * t - r ^ 2 = core * X)
    (hv : (27 : k[X]) * v - r ^ 3 = core * Yd)
    (hb : cubicBNumerator68 v t r = core * b)
    (hd : cubicDNumerator68 core p1 p2 v t r = core * d)
    (hw : cubicWNumerator68 core p2 v t r gamma = core * w)
    (hphi : cubicPhiNumerator68 core p0 p1 p2 v t r gamma epsilon = core * phi) :
    b = C (1 / 27 : k) * (Yd - (6 : k[X]) * r * X) ∧
    d = core * p1 - C (1 / 3 : k) * r * p2 +
        C (1 / 324 : k) * r ^ 2 * Yd - C (1 / 162 : k) * r ^ 3 * X ∧
    w = C (4 / 9 : k) * p2 - C (2 / 243 : k) * r * Yd +
        C (8 / 243 : k) * r ^ 2 * X +
        core * (-C (4 / 243 : k) * X ^ 2 + C (2 / 3 * gamma : k)) ∧
    phi = C (2 / 9 : k) * r ^ 2 * p2 - C (7 / 2187 : k) * r ^ 3 * Yd +
        C (8 / 729 : k) * r ^ 4 * X +
        core * (-C (134 / 2187 : k) * r ^ 2 * X ^ 2 +
          C (104 / 6561 : k) * r * X * Yd +
          C (1 / 9 * gamma : k) * r ^ 2 - C (8 / 19683 : k) * Yd ^ 2 -
          C (4 / 9 : k) * r * p1 - C (16 / 27 : k) * X * p2) +
        core ^ 2 * (C (40 / 2187 : k) * X ^ 3 -
          C (4 / 9 * gamma : k) * X + C (8 / 3 : k) * p0 +
          C (2 * epsilon : k)) := by
  have ht' : t = C (1 / 3 : k) * (r ^ 2 + core * X) := by
    have hunit : C (1 / 3 : k) * (3 : k[X]) = 1 := by
      apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
      simp only [map_mul, map_one, RatFunc.algebraMap_C, map_div₀, map_ofNat]
      ring
    calc
      t = (C (1 / 3 : k) * (3 : k[X])) * t := by rw [hunit, one_mul]
      _ = C (1 / 3 : k) * (r ^ 2 + core * X) := by
        rw [mul_assoc]
        congr 1
        linear_combination ht
  have hv' : v = C (1 / 27 : k) * (r ^ 3 + core * Yd) := by
    have hunit : C (1 / 27 : k) * (27 : k[X]) = 1 := by
      apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
      simp only [map_mul, map_one, RatFunc.algebraMap_C, map_div₀, map_ofNat]
      ring
    calc
      v = (C (1 / 27 : k) * (27 : k[X])) * v := by rw [hunit, one_mul]
      _ = C (1 / 27 : k) * (r ^ 3 + core * Yd) := by
        rw [mul_assoc]
        congr 1
        linear_combination hv
  have hb' : core * b = core * (C (1 / 27 : k) *
      (Yd - (6 : k[X]) * r * X)) := by
    rw [← hb, cubicBNumerator68, ht', hv']
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hd' : core * d = core * (core * p1 - C (1 / 3 : k) * r * p2 +
      C (1 / 324 : k) * r ^ 2 * Yd - C (1 / 162 : k) * r ^ 3 * X) := by
    rw [← hd, cubicDNumerator68, ht', hv']
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hw' : core * w = core * (C (4 / 9 : k) * p2 -
      C (2 / 243 : k) * r * Yd + C (8 / 243 : k) * r ^ 2 * X +
      core * (-C (4 / 243 : k) * X ^ 2 + C (2 / 3 * gamma : k))) := by
    rw [← hw, cubicWNumerator68, cubicANumerator68, cubicCNumerator68,
      ht', hv']
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hphi' : core * phi = core *
      (C (2 / 9 : k) * r ^ 2 * p2 - C (7 / 2187 : k) * r ^ 3 * Yd +
        C (8 / 729 : k) * r ^ 4 * X +
        core * (-C (134 / 2187 : k) * r ^ 2 * X ^ 2 +
          C (104 / 6561 : k) * r * X * Yd +
          C (1 / 9 * gamma : k) * r ^ 2 - C (8 / 19683 : k) * Yd ^ 2 -
          C (4 / 9 : k) * r * p1 - C (16 / 27 : k) * X * p2) +
        core ^ 2 * (C (40 / 2187 : k) * X ^ 3 -
          C (4 / 9 * gamma : k) * X + C (8 / 3 : k) * p0 +
          C (2 * epsilon : k))) := by
    rw [← hphi, cubicPhiNumerator68, cubicANumerator68,
      cubicBNumerator68, cubicCNumerator68, cubicENumerator68, ht', hv']
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  exact ⟨mul_left_cancel₀ hcore hb', mul_left_cancel₀ hcore hd',
    mul_left_cancel₀ hcore hw', mul_left_cancel₀ hcore hphi'⟩

/-- Fully source-facing defect and terminal quotient packet. -/
theorem NonsquareAlignedSourceCurveData68.terminalFactorsSourcePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (g r t X Yd b1 d1 w1 phi1 : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r = H * d1 ∧
      cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma = H * w1 ∧
      cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r S.gamma S.epsilon = H * phi1 ∧
      b1 * phi1 + (6 : k[X]) * w1 * d1 = 0 ∧
      ∀ a : k, H.eval a = 0 →
        r.eval a = 0 ∨
          ((9 * (r.eval a) ^ 2 * X.eval a -
              2 * r.eval a * Yd.eval a + 81 * (p.coeff 2).eval a = 0) ∧
            w1.eval a = (2 / 27 : k) * r.eval a * b1.eval a ∧
            d1.eval a = -(5 / 36 : k) * (r.eval a) ^ 2 * b1.eval a) ∨
          ((3 * (r.eval a) ^ 2 * X.eval a -
              r.eval a * Yd.eval a + 81 * (p.coeff 2).eval a = 0) ∧
            w1.eval a = -(2 / 27 : k) * r.eval a * b1.eval a ∧
            d1.eval a = -(1 / 36 : k) * (r.eval a) ^ 2 * b1.eval a) := by
  obtain ⟨g, r, t, b1, d1, w1, phi1, hg, hr, ht, hb1, hd1, hw1,
      hphi1, hI4⟩ :=
    S.terminalI4_quotientPacket (H := H) hdeg hp hq hp6 hq8 haligned hjac
  obtain ⟨_kappa, gc, rc, tc, _s, _u, hgc, hrc, htc, _hs, _hu,
      _hushape, hcorec⟩ :=
    S.integratedRSNext_cubicCorePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hgeq : g = gc := by
    apply mul_left_cancel₀ hH
    rw [← hg, ← hgc]
  have hreq : r = rc := by
    apply mul_left_cancel₀ hH
    rw [← hr, ← hrc, hgeq]
  have hteq : t = tc := by
    apply mul_left_cancel₀ hH
    rw [← ht, ← htc]
  have hcore : ∀ a : k, H.eval a = 0 →
      (3 : k) * t.eval a = (r.eval a) ^ 2 ∧
        (27 : k) * (p.coeff 3).eval a = (r.eval a) ^ 3 := by
    intro a ha
    simpa only [hteq, hreq] using hcorec a ha
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hXdvd : H ∣ (3 : k[X]) * t - r ^ 2 := by
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    simpa [eval_sub, eval_mul, eval_pow, eval_C] using
      sub_eq_zero.mpr (hcore a ha).1
  have hYdvd : H ∣ (27 : k[X]) * p.coeff 3 - r ^ 3 := by
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    simpa [eval_sub, eval_mul, eval_pow, eval_C] using
      sub_eq_zero.mpr (hcore a ha).2
  obtain ⟨X, hX⟩ := hXdvd
  obtain ⟨Yd, hY⟩ := hYdvd
  have hfactor := terminalQuotientFactorsPolynomial_of_cubicDefects_68
    H r t (p.coeff 3) (p.coeff 0) (p.coeff 1) (p.coeff 2)
    S.gamma S.epsilon X Yd b1 d1 w1 phi1 hH hX hY hb1 hd1 hw1 hphi1
  refine ⟨g, r, t, X, Yd, b1, d1, w1, phi1, hg, hr, ht, hX, hY,
    hb1, hd1, hw1, hphi1, hI4, ?_⟩
  intro a ha
  have hfa := hfactor
  rcases hfa with ⟨hbf, hdf, hwf, hphif⟩
  have hbf' := congrArg (fun f : k[X] => f.eval a) hbf
  have hdf' := congrArg (fun f : k[X] => f.eval a) hdf
  have hwf' := congrArg (fun f : k[X] => f.eval a) hwf
  have hphif' := congrArg (fun f : k[X] => f.eval a) hphif
  have hI4' := congrArg (fun f : k[X] => f.eval a) hI4
  simp only [eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_ofNat,
    eval_C, eval_zero, ha, zero_mul, zero_add, zero_sub, add_zero, zero_pow,
    OfNat.zero_ne_ofNat] at hbf' hdf' hwf' hphif' hI4'
  have hbf0 : b1.eval a = (Yd.eval a - 6 * r.eval a * X.eval a) / 27 := by
    rw [hbf']
    ring
  have hdf0 : d1.eval a = -(1 / 3 : k) * r.eval a * (p.coeff 2).eval a +
      (1 / 324 : k) * (r.eval a) ^ 2 * Yd.eval a -
      (1 / 162 : k) * (r.eval a) ^ 3 * X.eval a := by
    rw [hdf']
    ring
  have hphif0 : phi1.eval a = (2 / 9 : k) * (r.eval a) ^ 2 *
      (p.coeff 2).eval a - (7 / 2187 : k) * (r.eval a) ^ 3 * Yd.eval a +
      (8 / 729 : k) * (r.eval a) ^ 4 * X.eval a := by
    rw [hphif']
    ring
  exact terminalQuotientFace_cubicDefect_refinedSplit_68
    (r.eval a) (X.eval a) (Yd.eval a) ((p.coeff 2).eval a)
    (b1.eval a) (d1.eval a) (w1.eval a) (phi1.eval a)
    hbf0 hdf0 hwf' hphif0 hI4'

end TerminalFactorsSource68

end Max11DegreeRoutes
