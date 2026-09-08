import LowScale68SecondaryLaterDeepFiveRadiusTerminalEqualityAssembly
import LowScale68SecondaryAlphaWallBalancedRowZero

/-! # Terminal row-zero algebra on `2g = 5n`, `h = 5n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusTerminalRowZeroAlgebra68

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


set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- After `l=beta=delta=zeta=0`, the `alpha` terms in row zero cancel.
This is the exact remaining load in residual coordinates. -/
def fiveRadiusTerminalRowZeroLoad68
    (gamma epsilon : k) (A B c d e : k[X]) : k[X] :=
  gamma •
      ((2 / 9 : k) • (B * derivative A * c) +
        (2 / 3 : k) • (B * derivative e) -
        (2 / 9 : k) • (d * A * derivative A) -
        (2 / 3 : k) • (d * derivative c)) -
    (1 / 3 * epsilon : k) •
      (((1 / 3 : k) • (A * B) + d) * derivative A)

set_option maxHeartbeats 6000000 in
theorem cubicLoadRowZeroPolynomial68_terminalEquality
    (alpha gamma epsilon eta : k) (A B c d e : k[X]) :
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      fiveRadiusTerminalRowZeroLoad68 gamma epsilon A B c d e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, fiveRadiusTerminalRowZeroLoad68,
    zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 5000000 in
theorem fiveRadiusTerminalRowZeroLoad68_degree_lt
    (gamma epsilon : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 0) (he : e.natDegree ≤ n) :
    (fiveRadiusTerminalRowZeroLoad68 gamma epsilon A B c d e).natDegree <
      13 * n - 3 * g - 1 := by
  simp only [fiveRadiusTerminalRowZeroLoad68]
  apply leaf68_lt_of_bd
  repeat'
    first
    | with_reducible exact leaf68_bd_of_le hA
    | with_reducible exact leaf68_bd_of_le hB
    | with_reducible exact leaf68_bd_of_le hc
    | with_reducible exact leaf68_bd_of_le hd
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

def fiveRadiusTerminalRowZeroCore68
    (A B c d e : k[X]) : k[X] :=
  (4 / 27 : k) •
    (-(1 : k) • (A * derivative A * B * e) -
      A * derivative A * c * d + derivative A * B * c ^ 2)

def fiveRadiusTerminalRowZeroTail68
    (A B c d e : k[X]) : k[X] :=
  (4 / 27 : k) •
    (-(A * B ^ 2 * derivative d) - A * B * derivative B * d -
      (3 : k) • (derivative A * d * e) +
      (3 : k) • (B * c * derivative e) -
      (3 : k) • (B * d * derivative d) -
      (3 : k) • (derivative B * d ^ 2) -
      (3 : k) • (c * derivative c * d))

theorem secondaryResidualRowZeroPolynomial68_terminalEqualitySplit
    (A B c d e : k[X]) :
    secondaryResidualRowZeroPolynomial68 A B c d e =
      fiveRadiusTerminalRowZeroCore68 A B c d e +
        fiveRadiusTerminalRowZeroTail68 A B c d e := by
  simp only [secondaryResidualRowZeroPolynomial68,
    fiveRadiusTerminalRowZeroCore68, fiveRadiusTerminalRowZeroTail68]
  module

set_option maxHeartbeats 5000000 in
theorem fiveRadiusTerminalRowZeroTail68_degree_lt
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 0) (he : e.natDegree ≤ n) :
    (fiveRadiusTerminalRowZeroTail68 A B c d e).natDegree <
      13 * n - 3 * g - 1 := by
  simp only [fiveRadiusTerminalRowZeroTail68]
  apply leaf68_lt_of_bd
  repeat'
    first
    | with_reducible exact leaf68_bd_of_le hA
    | with_reducible exact leaf68_bd_of_le hB
    | with_reducible exact leaf68_bd_of_le hc
    | with_reducible exact leaf68_bd_of_le hd
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

end LaterDeepFiveRadiusTerminalRowZeroAlgebra68
end Max11DegreeRoutes
