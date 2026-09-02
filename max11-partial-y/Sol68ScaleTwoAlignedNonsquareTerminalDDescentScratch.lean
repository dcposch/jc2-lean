import Sol68ScaleTwoAlignedNonsquareTerminalI3AssemblyScratch

/-! # The next aligned-nonsquare terminal D descent -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section TerminalDDescentAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Once the new odd quotient `b` vanishes, either root allocation forces
the reduced `D` quotient to vanish as well. -/
theorem terminalD_zero_of_B_zero_and_allocations_68
    (r X Yd p2 d : k)
    (hb : 0 = (1 / 27 : k) * (Yd - 6 * r * X))
    (hd : d = -(1 / 3 : k) * r * p2 + (1 / 324 : k) * r ^ 2 * Yd -
      (1 / 162 : k) * r ^ 3 * X)
    (halloc : r = 0 ∨
      (9 * r ^ 2 * X - 2 * r * Yd + 81 * p2 = 0) ∨
      (3 * r ^ 2 * X - r * Yd + 81 * p2 = 0)) : d = 0 := by
  have hb0 : Yd - 6 * r * X = 0 := by
    have hc : (1 / 27 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hb.symm).resolve_left hc
  rcases halloc with hr | hF | hG
  · rw [hd, hr]
    ring
  · rw [hd]
    linear_combination (-1 / 243 : k) * r * hF +
      (-5 / 972 : k) * r ^ 2 * hb0
  · rw [hd]
    linear_combination (-1 / 243 : k) * r * hG +
      (-1 / 972 : k) * r ^ 2 * hb0

end TerminalDDescentAlgebra68

section TerminalDDescentSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- The `I₃`-improved terminal packet forces one more full core factor in
the odd `D` coordinate as well as in `B`. -/
theorem NonsquareAlignedSourceCurveData68.terminalDDescentSourcePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (g r t X Yd b1 d1 : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r = H * d1 ∧
      (∀ a : k, H.eval a = 0 → b1.eval a = 0 ∧ d1.eval a = 0) ∧
      H ∣ b1 ∧ H ∣ d1 ∧
      H ^ 2 ∣ cubicBNumerator68 (p.coeff 3) t r ∧
      H ^ 2 ∣ cubicDNumerator68 H (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, hg, hr, ht, hX, hY,
      hb1, hd1, hw1, hphi1, hkdef, hrowdef, hbranches⟩ :=
    S.terminalKOneNextSourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  obtain ⟨g0, r0, t0, X0, Yd0, b10, hg0, hr0, ht0, hX0, hY0,
      hb10, hrootB0, hdvdB0, hsqB0⟩ :=
    S.terminalGNextI3SourcePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hgg : g0 = g := by
    apply mul_left_cancel₀ hH
    rw [← hg0, ← hg]
  have hrr : r0 = r := by
    apply mul_left_cancel₀ hH
    rw [← hr0, ← hr, hgg]
  have htt : t0 = t := by
    apply mul_left_cancel₀ hH
    rw [← ht0, ← ht]
  have hXX : X0 = X := by
    apply mul_left_cancel₀ hH
    rw [← hX0, ← hX, htt, hrr]
  have hYY : Yd0 = Yd := by
    apply mul_left_cancel₀ hH
    rw [← hY0, ← hY, hrr]
  have hbb : b10 = b1 := by
    apply mul_left_cancel₀ hH
    rw [← hb10, ← hb1, htt, hrr]
  have hrootB : ∀ a : k, H.eval a = 0 → b1.eval a = 0 := by
    intro a ha
    simpa only [hbb] using hrootB0 a ha
  have hfactor := terminalQuotientFactorsPolynomial_of_cubicDefects_68
    H r t (p.coeff 3) (p.coeff 0) (p.coeff 1) (p.coeff 2)
    S.gamma S.epsilon X Yd b1 d1 w1 phi1 hH hX hY hb1 hd1 hw1 hphi1
  rcases hfactor with ⟨hbform, hdform, _hwform, _hphiform⟩
  have hrootD : ∀ a : k, H.eval a = 0 → d1.eval a = 0 := by
    intro a ha
    have hba := congrArg (fun f : k[X] => f.eval a) hbform
    have hda := congrArg (fun f : k[X] => f.eval a) hdform
    simp only [eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C,
      eval_ofNat, ha, zero_mul, zero_add, zero_sub] at hba hda
    have hbzero := hrootB a ha
    rw [hbzero] at hba
    have halloc : r.eval a = 0 ∨
        (9 * (r.eval a) ^ 2 * X.eval a -
          2 * r.eval a * Yd.eval a + 81 * (p.coeff 2).eval a = 0) ∨
        (3 * (r.eval a) ^ 2 * X.eval a -
          r.eval a * Yd.eval a + 81 * (p.coeff 2).eval a = 0) := by
      rcases hbranches a ha with hrzero | hF | hG
      · exact Or.inl hrzero
      · exact Or.inr (Or.inl hF.1)
      · exact Or.inr (Or.inr hG.1)
    have hda' : d1.eval a =
        -(1 / 3 : k) * r.eval a * (p.coeff 2).eval a +
          (1 / 324 : k) * (r.eval a) ^ 2 * Yd.eval a -
          (1 / 162 : k) * (r.eval a) ^ 3 * X.eval a := by
      rw [hda]
      ring
    exact terminalD_zero_of_B_zero_and_allocations_68
      (r.eval a) (X.eval a) (Yd.eval a) ((p.coeff 2).eval a)
      (d1.eval a) hba hda' halloc
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hdvdB : H ∣ b1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hrootB
  have hdvdD : H ∣ d1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hrootD
  have hsqB : H ^ 2 ∣ cubicBNumerator68 (p.coeff 3) t r :=
    terminalB_sq_dvd_of_all_quotient_roots_68 H
      (cubicBNumerator68 (p.coeff 3) t r) b1 hdeg hsimple hb1 hrootB
  have hsqD : H ^ 2 ∣
      cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r :=
    terminalB_sq_dvd_of_all_quotient_roots_68 H
      (cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r)
      d1 hdeg hsimple hd1 hrootD
  exact ⟨g, r, t, X, Yd, b1, d1, hg, hr, ht, hX, hY, hb1, hd1,
    fun a ha => ⟨hrootB a ha, hrootD a ha⟩, hdvdB, hdvdD, hsqB, hsqD⟩

end TerminalDDescentSource68

end Max11DegreeRoutes
