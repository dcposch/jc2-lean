import Sol610ScaleTwoNonzeroFourteenthMergedJetScratch

/-! # Collapse of the pinned complement child of the `(6,10)` fourth tail -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ComplementHeadCollapse610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- The recorded complement pinning reduces the 14-term fourth-tail head to
the single monomial `-302330880 a₄₁⁷`. -/
theorem nonzeroFourteenthMergedJetHead610_complementPinned
    (a41 s1 b62 p2 q41 : F)
    (hs : (3 : F) * s1 = 5 * a41)
    (hp2 : (6 : F) * p2 = a41 ^ 2)
    (hb62 : (6 : F) * b62 = 5 * a41 ^ 2)
    (hq41 : (324 : F) * q41 = 35 * a41 ^ 3) :
    nonzeroFourteenthMergedJetHead610 a41 s1 b62 p2 q41 =
      -(302330880 : F) * a41 ^ 7 := by
  have hs' : s1 = (5 / 3 : F) * a41 := by
    linear_combination (1 / 3 : F) * hs
  have hp2' : p2 = (1 / 6 : F) * a41 ^ 2 := by
    linear_combination (1 / 6 : F) * hp2
  have hb62' : b62 = (5 / 6 : F) * a41 ^ 2 := by
    linear_combination (1 / 6 : F) * hb62
  have hq41' : q41 = (35 / 324 : F) * a41 ^ 3 := by
    linear_combination (1 / 324 : F) * hq41
  rw [hs', hp2', hb62', hq41']
  simp only [nonzeroFourteenthMergedJetHead610]
  ring

set_option maxHeartbeats 4000000 in
/-- A vanishing pinned fourth-tail head collapses the complement child. -/
theorem nonzeroFourteenthMergedJetHead610_complementCollapse
    (a41 s1 b62 p2 q41 : F)
    (hhead : nonzeroFourteenthMergedJetHead610 a41 s1 b62 p2 q41 = 0)
    (hs : (3 : F) * s1 = 5 * a41)
    (hp2 : (6 : F) * p2 = a41 ^ 2)
    (hb62 : (6 : F) * b62 = 5 * a41 ^ 2)
    (hq41 : (324 : F) * q41 = 35 * a41 ^ 3) :
    a41 = 0 ∧ s1 = 0 ∧ p2 = 0 ∧ b62 = 0 ∧ q41 = 0 := by
  have hpinned := nonzeroFourteenthMergedJetHead610_complementPinned
    a41 s1 b62 p2 q41 hs hp2 hb62 hq41
  rw [hpinned] at hhead
  have ha41pow : a41 ^ 7 = 0 :=
    (mul_eq_zero.mp hhead).resolve_left (by norm_num)
  have ha41 : a41 = 0 :=
    (pow_eq_zero_iff (by norm_num : (7 : ℕ) ≠ 0)).mp ha41pow
  have hs1 : s1 = 0 := by
    have h : (3 : F) * s1 = 0 := by simpa [ha41] using hs
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hp2z : p2 = 0 := by
    have h : (6 : F) * p2 = 0 := by simpa [ha41] using hp2
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hb62z : b62 = 0 := by
    have h : (6 : F) * b62 = 0 := by simpa [ha41] using hb62
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hq41z : q41 = 0 := by
    have h : (324 : F) * q41 = 0 := by simpa [ha41] using hq41
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  exact ⟨ha41, hs1, hp2z, hb62z, hq41z⟩

end ComplementHeadCollapse610

section SourceComplementCollapse610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Source-facing collapse at the same supplied root and with the same jet
witnesses. -/
theorem nonzeroFace610_fourteenthComplementCollapse
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 = Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (w1 a41 p32 s1 u2 b62 q53 q41 : k[X])
    (hp5 : p.coeff 5 = h0 ^ 5 * w1)
    (hp4 : p.coeff 4 = h0 ^ 3 * a41)
    (hp3 : p.coeff 3 = h0 ^ 2 * p32)
    (hq8 : q.coeff 8 = h0 ^ 7 * s1)
    (hq7 : q.coeff 7 = h0 ^ 6 * u2)
    (hq6 : q.coeff 6 = h0 ^ 4 * b62)
    (hq5 : q.coeff 5 = h0 ^ 3 * q53)
    (hq4 : q.coeff 4 = h0 * q41)
    (hs : (3 : k) * s1.eval a = 5 * a41.eval a)
    (hp2pin : (6 : k) * (p.coeff 2).eval a = (a41.eval a) ^ 2)
    (hb62pin : (6 : k) * b62.eval a = 5 * (a41.eval a) ^ 2)
    (hq41pin : (324 : k) * q41.eval a = 35 * (a41.eval a) ^ 3) :
    a41.eval a = 0 ∧ s1.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
      b62.eval a = 0 ∧ q41.eval a = 0 := by
  have hhead := nonzeroFace610_fourteenthMergedHead_eval_zero
    p q H h0 j lambda a hp hq hh0 hH hp6 hq10 hN hD hroot
    w1 a41 p32 s1 u2 b62 q53 q41 hp5 hp4 hp3 hq8 hq7 hq6 hq5 hq4
  exact nonzeroFourteenthMergedJetHead610_complementCollapse
    (a41.eval a) (s1.eval a) (b62.eval a) ((p.coeff 2).eval a)
    (q41.eval a) hhead hs hp2pin hb62pin hq41pin

#print axioms nonzeroFourteenthMergedJetHead610_complementPinned
#print axioms nonzeroFourteenthMergedJetHead610_complementCollapse
#print axioms nonzeroFace610_fourteenthComplementCollapse

end SourceComplementCollapse610

end Max11DegreeRoutes
