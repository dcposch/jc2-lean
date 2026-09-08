import LowScale68SecondaryLaterDeepLowerOpenMiddleHighRightSevenRowOne

/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

private structure Leaf68Bound (p : k[X]) (u : ℕ) : Prop where
  le : p.natDegree ≤ u

private theorem leaf68_bd_of_le {p : k[X]} {u : ℕ} (h : p.natDegree ≤ u) :
    Leaf68Bound p u := ⟨h⟩

private theorem leaf68_bd_C (a : k) : Leaf68Bound (C a) 0 :=
  ⟨(natDegree_C a).le⟩

private theorem leaf68_bd_smul (r : k) {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (r • p) u :=
  ⟨(natDegree_smul_le r p).trans hp.le⟩

private theorem leaf68_bd_neg {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (-p) u :=
  ⟨(natDegree_neg p).le.trans hp.le⟩

private theorem leaf68_bd_add {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p + q) (max u v) :=
  ⟨(natDegree_add_le p q).trans (max_le_max hp.le hq.le)⟩

private theorem leaf68_bd_sub {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p - q) (max u v) :=
  ⟨(natDegree_sub_le p q).trans (max_le_max hp.le hq.le)⟩

private theorem leaf68_bd_mul {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p * q) (u + v) :=
  ⟨natDegree_mul_le.trans (Nat.add_le_add hp.le hq.le)⟩

private theorem leaf68_bd_pow {p : k[X]} {u : ℕ} (m : ℕ)
    (hp : Leaf68Bound p u) : Leaf68Bound (p ^ m) (m * u) :=
  ⟨natDegree_pow_le.trans (Nat.mul_le_mul (le_refl m) hp.le)⟩

private theorem leaf68_bd_deriv {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (derivative p) (u - 1) :=
  ⟨(natDegree_derivative_le p).trans (Nat.sub_le_sub_right hp.le 1)⟩

private theorem leaf68_lt_of_bd {p : k[X]} {u b : ℕ}
    (hp : Leaf68Bound p u) (h : u < b) : p.natDegree < b :=
  lt_of_le_of_lt hp.le h

private theorem leaf68_le_of_bd {p : k[X]} {u b : ℕ}
    (hp : Leaf68Bound p u) (h : u ≤ b) : p.natDegree ≤ b :=
  hp.le.trans h


set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

set_option maxHeartbeats 3000000 in
theorem residualIncidenceQ68_degree_le_twoRadius_of_coincidentSeven
    (gamma epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 2 * n := by
  have hQeq := residualIncidenceQ68_eq_I4load_of_alphaWall
    0 gamma 0 epsilon zeta i4 A B c d e hi4
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
    at hQeq
  rw [hQeq]
  apply leaf68_le_of_bd
  repeat'
    first
    | with_reducible exact leaf68_bd_of_le hA
    | with_reducible exact leaf68_bd_of_le hB
    | with_reducible exact leaf68_bd_of_le hd
    | with_reducible apply leaf68_bd_smul
    | with_reducible apply leaf68_bd_neg
    | with_reducible apply leaf68_bd_sub
    | with_reducible apply leaf68_bd_add
    | with_reducible apply leaf68_bd_pow
    | with_reducible apply leaf68_bd_deriv
    | with_reducible apply leaf68_bd_mul
    | with_reducible apply leaf68_bd_C
    | omega

set_option maxHeartbeats 3000000 in
theorem residualIncidenceQ68_coeff_twoRadius_of_coincidentSeven
    (gamma epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).coeff (2 * n) =
      -(3 / 8 : k) * zeta * A.coeff (2 * n) := by
  have hQeq := residualIncidenceQ68_eq_I4load_of_alphaWall
    0 gamma 0 epsilon zeta i4 A B c d e hi4
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
    at hQeq
  have hBlt : B.natDegree < 2 * n := hB.trans_lt (by omega)
  have hdlt : d.natDegree < 2 * n := hd.trans_lt (by omega)
  have hindex : 2 * n ≠ 0 := by omega
  rw [hQeq, coeff_smul, coeff_sub, coeff_C, if_neg hindex,
    coeff_add, coeff_add, coeff_smul, coeff_smul, coeff_smul, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hBlt,
    coeff_eq_zero_of_natDegree_lt hdlt]
  ring

def coincidentSevenRowZeroLoad68
    (gamma epsilon zeta : k) (A B c d e : k[X]) : k[X] :=
  fiveRadiusTerminalRowZeroLoad68 gamma epsilon A B c d e +
    zeta • derivative
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowZeroPolynomial68_coincidentSeven
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) :
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      coincidentSevenRowZeroLoad68 gamma epsilon zeta A B c d e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, fiveRadiusTerminalRowZeroLoad68,
    coincidentSevenRowZeroLoad68,
    zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem fiveRadiusTerminalRowZeroLoad68_degree_lt_sixRadius_of_coincidentSeven
    (gamma epsilon : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusTerminalRowZeroLoad68 gamma epsilon A B c d e).natDegree <
      6 * n - 1 := by
  simp only [fiveRadiusTerminalRowZeroLoad68]
  apply leaf68_lt_of_bd
  repeat'
    first
    | with_reducible exact leaf68_bd_of_le hA
    | with_reducible exact leaf68_bd_of_le hB
    | with_reducible exact leaf68_bd_of_le hd
    | with_reducible exact leaf68_bd_of_le hc
    | with_reducible exact leaf68_bd_of_le he
    | with_reducible apply leaf68_bd_smul
    | with_reducible apply leaf68_bd_neg
    | with_reducible apply leaf68_bd_sub
    | with_reducible apply leaf68_bd_add
    | with_reducible apply leaf68_bd_pow
    | with_reducible apply leaf68_bd_deriv
    | with_reducible apply leaf68_bd_mul
    | with_reducible apply leaf68_bd_C
    | omega

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
