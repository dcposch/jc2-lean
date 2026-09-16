import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2800 (a c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < a + e)
    (q2 : 2 * f < a + 2 * e)
    (q3 : 3 * a > e)
    (q4 : a + 2 * d < 2 * e)
    (q5 : g < a + e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2801 (a c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e)
    (q5 : c + g < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2802 (a c d e f g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 4 * a + d < 2 * c + e ∧ 3 * a + f < 2 * c + e)
    (q3 : c + g < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + f < 2 * c + e ∧ 2 * a + c + d < 2 * c + e ∧ a + c + f < 2 * c + e ∧ a + d + e < 2 * c + e ∧ 2 * c + d < 2 * c + e ∧ d + g < 2 * c + e ∧ e + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2803 (a c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e)
    (q5 : c + g < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2804 (a c d e f g : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e)
    (q5 : d + f < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ a + c + d < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2805 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : a + 2 * e = 2 * f)
    (q2 : a + e = g)
    (q3 : a + f < 2 * e)
    (q4 : c + g < 2 * e)
    (q5 : d + f < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2806 (a c d e f g : Nat)
    (q0 : 2 * f < a + 2 * e)
    (q1 : 3 * a > e)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + e = g)
    (q5 : c + g < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2807 (a d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + e = g) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2808 (a c d e f g : Nat)
    (q0 : 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + e = g)
    (q3 : c + g < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ a + c + d < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2809 (a c d e f g : Nat)
    (q0 : 2 * f < a + 2 * e)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + e = g)
    (q5 : c + g < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2810 (a c d e f g : Nat)
    (q0 : 2 * f < a + 2 * e)
    (q1 : 3 * a > e)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + e = g)
    (q5 : c + g < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2811 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + e = g)
    (q5 : c + g < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2812 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e)
    (q5 : d + f < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2813 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : 2 * f < a + 2 * e)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + e = g)
    (q5 : c + g < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2814 (a c d e f g : Nat)
    (q0 : 2 * g < a + 2 * f)
    (q1 : 3 * a + 2 * c < 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 7 * a > 2 * f)
    (q4 : a + 2 * e < 2 * f)
    (q5 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2815 (a c d e f g : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f)
    (q4 : a + d < f)
    (q5 : e + g < 2 * f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2816 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f)
    (q4 : a + d < f)
    (q5 : e + g < 2 * f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ a + c + d < 2 * f ∧ c + f < 2 * f ∧ d + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2817 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + c < g)
    (q2 : 3 * a + 2 * d < 2 * g)
    (q3 : 4 * a + f < 2 * g)
    (q4 : 4 * a > g)
    (q5 : a + e < g) :
    4 * a + f < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + c + f < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + 2 * c + d < 2 * g ∧ a + e + f < 2 * g ∧ 2 * c + f < 2 * g ∧ c + d + e < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2818 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + c < g)
    (q2 : 3 * a + 2 * d < 2 * g)
    (q3 : 3 * a + f < 2 * g)
    (q4 : 4 * a > g)
    (q5 : a + 2 * f < 2 * g)
    (q6 : a + e < g) :
    3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g ∧ a + c + f < 2 * g ∧ a + d + e < 2 * g ∧ 2 * c + d < 2 * g ∧ e + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2819 (a b c d e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : d < a + b)
    (q6 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2820 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2821 (a b c d e f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b)
    (q5 : e + g < 2 * a + b + f)
    (q6 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2822 (a b c d e f g : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b)
    (q5 : e + g < 2 * a + b + f)
    (q6 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2823 (a d e f g : Nat)
    (q0 : 2 * g < a + 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * e < 2 * f)
    (q4 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ a + d + e < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2824 (a d e f g : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + d < f)
    (q4 : e + g < 2 * f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ a + d + e < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2825 (a d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + d < f)
    (q4 : e + g < 2 * f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ d + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2826 (a d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d < 2 * g)
    (q2 : 4 * a + f < 2 * g)
    (q3 : 4 * a > g)
    (q4 : a + e < g) :
    4 * a + f < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + e + f < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2827 (a d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d < 2 * g)
    (q2 : 3 * a + f < 2 * g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + e < g) :
    3 * a + f < 2 * g ∧ a + d + e < 2 * g ∧ e + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2828 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2829 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2830 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2831 (a b c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2832 (a b c d e f : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2833 (a b c d e f : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2834 (a b c d e f : Nat)
    (q0 : 3 * a + f < a + 2 * f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + b + e < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ a + d + e < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + c + e < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2835 (a b c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2836 (a b c d f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2837 (a b c d e f : Nat)
    (q0 : 4 * a + d < a + d + f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + c + e < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2838 (a b c d e f : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2839 (a b c d f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2840 (a b c d e f : Nat)
    (q0 : 3 * a + d < a + d + f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a + d < a + d + f ∧ 2 * a + b + c < a + d + f ∧ a + 3 * b < a + d + f ∧ 2 * a + f < a + d + f ∧ a + b + e < a + d + f ∧ a + c + d < a + d + f ∧ 2 * b + d < a + d + f ∧ b + 2 * c < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2841 (a b c d e f : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2842 (a b c d f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2843 (a b c d e f : Nat)
    (q0 : 2 * a + d < a + d + f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    2 * a + d < a + d + f ∧ a + b + c < a + d + f ∧ 3 * b < a + d + f ∧ a + f < a + d + f ∧ b + e < a + d + f ∧ c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2844 (a b c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2845 (a b c d e f : Nat)
    (q0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2846 (a b c d e f : Nat)
    (q0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2847 (a b c d e f : Nat)
    (q0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q1 : 3 * a + f < a + 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + b + e < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ a + d + e < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + c + e < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2848 (a b c d e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : d < a + b) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2849 (a b c d e f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : d < a + b) :
    3 * a + d < 2 * f ∧ 2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + b + e < 2 * f ∧ a + c + d < 2 * f ∧ 2 * b + d < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f ∧ d + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2850 (a b c d e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f)
    (q5 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2851 (a b c d e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f)
    (q5 : d < a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2852 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q2 : 4 * a + d < a + d + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + c + e < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2853 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q2 : 3 * a + d < a + d + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a + d < a + d + f ∧ 2 * a + b + c < a + d + f ∧ a + 3 * b < a + d + f ∧ 2 * a + f < a + d + f ∧ a + b + e < a + d + f ∧ a + c + d < a + d + f ∧ 2 * b + d < a + d + f ∧ b + 2 * c < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2854 (a b c d e f : Nat)
    (q0 : 2 * a + d < a + d + f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    2 * a + d < a + d + f ∧ a + b + c < a + d + f ∧ 3 * b < a + d + f ∧ a + f < a + d + f ∧ b + e < a + d + f ∧ c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2855 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + b = d)
    (q4 : b + e < a + f)
    (q5 : b + f = 2 * d) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2856 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + b = d)
    (q4 : b + e < a + f)
    (q5 : b + f = 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2857 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + b = d)
    (q4 : b + e < a + f)
    (q5 : b + f = 2 * d) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2858 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + f < a + 2 * f)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + b = d)
    (q4 : b + e < a + f)
    (q5 : b + f = 2 * d) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + b + e < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ a + d + e < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + c + e < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2859 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q2 : 4 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b = d)
    (q5 : b + f = 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2860 (a b c d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q3 : 3 * a + f < a + 2 * f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : a + b = d)
    (q6 : b + f = 2 * d) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + b + e < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ a + d + e < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + c + e < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2861 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 4 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b + f = 2 * e)
    (q5 : d < a + b) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2862 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 3 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b + f = 2 * e)
    (q5 : d < a + b) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + b + e < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ a + d + e < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + c + e < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2863 (a b c d e f : Nat)
    (q0 : 2 * a + f < a + 2 * f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b + f = 2 * e)
    (q5 : d < a + b) :
    2 * a + b + c < a + 2 * f ∧ a + 3 * b < a + 2 * f ∧ 2 * a + f < a + 2 * f ∧ a + b + e < a + 2 * f ∧ a + c + d < a + 2 * f ∧ 2 * b + d < a + 2 * f ∧ b + 2 * c < a + 2 * f ∧ c + f < a + 2 * f ∧ d + e < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2864 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 3 * a + f < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : b + e < a + f)
    (q5 : d < a + b) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2865 (a b c d e f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + 2 * b = 2 * e)
    (q3 : a + b + f = 2 * e)
    (q4 : b + e < a + f)
    (q5 : d < a + b) :
    3 * a + d < 2 * f ∧ 2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + b + e < 2 * f ∧ a + c + d < 2 * f ∧ 2 * b + d < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f ∧ d + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2866 (a b c d e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < a + b + f)
    (q3 : 4 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2867 (a b c d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 2 * c < a + 2 * b)
    (q3 : 2 * e < a + b + f)
    (q4 : 3 * a + b < a + b + f)
    (q5 : a + 4 * b < 2 * f)
    (q6 : d < a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2868 (a b c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + 2 * f < 4 * c)
    (q5 : e < a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2869 (a b c d e f : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c ∧ d + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2870 (a b c d e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + 2 * f < 4 * c)
    (q5 : e < a + c) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ b + e < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2871 (a b c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f)
    (q5 : e < a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2872 (a b c d e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f)
    (q5 : e < a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c ∧ d + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2873 (a b c d e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : a + 4 * d < 2 * c + 2 * f)
    (q4 : b + c < f)
    (q5 : c + d < a + f)
    (q6 : e < a + c) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ b + e < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2874 (a b c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f)
    (q4 : b + c < f)
    (q5 : d + e < c + f) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2875 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f)
    (q6 : d + e < c + f) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2876 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : b + c < f)
    (q4 : d + e < c + f) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2877 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : 4 * c < a + 2 * f)
    (q4 : b + c < f)
    (q5 : d + e < c + f) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2878 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * e)
    (q3 : b + c < f)
    (q4 : d + e < c + f) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2879 (a b c d f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2880 (a b c d f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f)
    (q4 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2881 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + d < a + f)
    (q5 : c + f = d + e) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2882 (a b c d f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + c < f) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2883 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * a + d < a + d + f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : b + c < f)
    (q5 : c + f = d + e)
    (q6 : e < a + c) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + c + e < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2884 (a b c d f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + c < f) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2885 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 3 * a + d < a + d + f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : b + c < f)
    (q5 : c + f = d + e)
    (q6 : e < a + c) :
    3 * a + d < a + d + f ∧ 2 * a + b + c < a + d + f ∧ a + 3 * b < a + d + f ∧ 2 * a + f < a + d + f ∧ a + b + e < a + d + f ∧ a + c + d < a + d + f ∧ 2 * b + d < a + d + f ∧ b + 2 * c < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2886 (a b c d f : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a ≤ 4 * b)
    (q2 : b + c < f) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2887 (a b c d e f : Nat)
    (q0 : 2 * a + d < a + d + f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : b + c < f)
    (q5 : c + f = d + e)
    (q6 : e < a + c) :
    2 * a + d < a + d + f ∧ a + b + c < a + d + f ∧ 3 * b < a + d + f ∧ a + f < a + d + f ∧ b + e < a + d + f ∧ c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2888 (a b c d e f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : d + e < c + f)
    (q5 : e < a + c) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2889 (a b c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : d + e < c + f)
    (q5 : e < a + c) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2890 (a b c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : d + e < c + f)
    (q5 : e < a + c) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2891 (a b c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : d + e < c + f)
    (q5 : e < a + c) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2892 (a b c d e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : d + e < c + f)
    (q5 : e < a + c) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2893 (a b c d e f : Nat)
    (q0 : 4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : d + e < c + f)
    (q5 : e < a + c) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2894 (a b c d e f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f)
    (q3 : d + e < c + f)
    (q4 : e < a + c) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2895 (a b c d e f : Nat)
    (q0 : 3 * a + b < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : d + e < c + f)
    (q5 : e < a + c) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2896 (a b c d e f : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f)
    (q3 : d + e < c + f)
    (q4 : e < a + c) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2897 (a b c d e f : Nat)
    (q0 : 2 * a + b < 2 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : d + e < c + f)
    (q5 : e < a + c) :
    2 * a + b < 2 * e ∧ a + d < 2 * e ∧ b + c < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2898 (a b c d e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : a + c = e)
    (q5 : b + c < f)
    (q6 : d + e < c + f) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2899 (a b c d e f : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f)
    (q6 : e < a + c) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2900 (a b c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2901 (a b c d e f g : Nat)
    (q0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q1 : 4 * a + d < a + d + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d)
    (q6 : d < a + b) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + c + e < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2902 (a b c d e f : Nat)
    (q0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2903 (a b c d e f : Nat)
    (q0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q1 : 3 * a + d < a + d + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a + d < a + d + f ∧ 2 * a + b + c < a + d + f ∧ a + 3 * b < a + d + f ∧ 2 * a + f < a + d + f ∧ a + b + e < a + d + f ∧ a + c + d < a + d + f ∧ 2 * b + d < a + d + f ∧ b + 2 * c < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2904 (a b c d e f : Nat)
    (q0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2905 (a b c d e f : Nat)
    (q0 : 2 * a + d < a + d + f)
    (q1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    2 * a + d < a + d + f ∧ a + b + c < a + d + f ∧ 3 * b < a + d + f ∧ a + f < a + d + f ∧ b + e < a + d + f ∧ c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2906 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    3 * a + f < e + g ∧ 4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2907 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    3 * a + f < e + g ∧ 4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2908 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    3 * a + f < e + g ∧ 4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2909 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * d < b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    3 * a + f < e + g ∧ 4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2910 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * d < b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    3 * a + f < e + g ∧ 4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2911 (a b c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * d < b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    3 * a + f < e + g ∧ 4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2912 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a + f < e + g ∧ 4 * a + d < e + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2913 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    2 * a + f < e + g ∧ 3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2914 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    2 * a + f < e + g ∧ 3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2915 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    2 * a + f < e + g ∧ 3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2916 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    2 * a + f < e + g ∧ 3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2917 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * d < b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    2 * a + f < e + g ∧ 3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2918 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * d < b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    2 * a + f < e + g ∧ 3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2919 (a b c d e f g : Nat)
    (q0 : 2 * a + f < e + g ∧ 3 * a + d < e + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ 2 * a + f < e + g ∧ a + b + e < e + g ∧ a + c + d < e + g ∧ 2 * b + d < e + g ∧ b + 2 * c < e + g ∧ c + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2920 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : a ≤ 4 * b)
    (q5 : b + c < f) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2921 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2922 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2923 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2924 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2925 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * d < b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : b + c < f)
    (q6 : e + g < 2 * a + b + f) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2926 (a b c d e f g : Nat)
    (q0 : 2 * a + d < e + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + d < e + g ∧ a + b + c < e + g ∧ 3 * b < e + g ∧ a + f < e + g ∧ b + e < e + g ∧ c + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2927 (a b c d e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + c < f)
    (q5 : d < a + b)
    (q6 : e + g < 2 * a + b + f) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2928 (a b c d e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + c < f)
    (q5 : d < a + b)
    (q6 : e + g < 2 * a + b + f) :
    3 * a + d < 2 * f ∧ 2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + b + e < 2 * f ∧ a + c + d < 2 * f ∧ 2 * b + d < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f ∧ d + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2929 (a b c d e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * b < 2 * f)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b)
    (q6 : e + g < 2 * a + b + f) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2930 (a b c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + 4 * b < 2 * f)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b)
    (q7 : e + g < 2 * a + b + f) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2931 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b)
    (q6 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2932 (a b c d e f g : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d)
    (q6 : c + g < a + b + f) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2933 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : b + f = 2 * d)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2934 (a b c d e f g : Nat)
    (q0 : 4 * a + d < a + d + f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + c + e < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2935 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : b + f = 2 * d)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2936 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : b + f = 2 * d)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2937 (a b c d e f g : Nat)
    (q0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : b + c < f)
    (q5 : b + f = 2 * d)
    (q6 : c + g < a + b + f) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2938 (a b c d e f g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2939 (a b c d e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2940 (a b c d e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * a + d < a + d + f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : b + f = 2 * d)
    (q6 : d < a + b) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + c + e < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2941 (a b c d e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + b = d)
    (q4 : b + e < a + f)
    (q5 : b + f = 2 * d)
    (q6 : e + g < 2 * a + b + f) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2942 (a b c d e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * a + f < a + 2 * f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : a + b = d)
    (q6 : b + f = 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2943 (a b c d e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * a + f < a + 2 * f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : a + b + f = 2 * e)
    (q6 : d < a + b) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2944 (a b c d e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 3 * a + f < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : b + e < a + f)
    (q5 : d < a + b)
    (q6 : e + g < 2 * a + b + f) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2945 (a b c d e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < a + b + f)
    (q3 : 2 * g < a + 2 * f)
    (q4 : 4 * a + b < a + b + f)
    (q5 : a + 4 * b < 2 * f)
    (q6 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2946 (a b c d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a + b < c + g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g ∧ d + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2947 (a b c d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a + b < c + g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ b + e < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2948 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + g = d + e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2949 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b = d)
    (q5 : b + g = d + e)
    (q6 : c + f < b + g) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2950 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + d < e + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b = d)
    (q5 : b + g = d + e)
    (q6 : c + f < b + g) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2951 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + g = d + e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2952 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b = d)
    (q5 : b + g = d + e)
    (q6 : c + f < b + g) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2953 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + d < e + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b = d)
    (q5 : b + g = d + e)
    (q6 : c + f < b + g) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ 2 * a + f < e + g ∧ a + b + e < e + g ∧ a + c + d < e + g ∧ 2 * b + d < e + g ∧ b + 2 * c < e + g ∧ c + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2954 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + g = d + e)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2955 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + d < e + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + g = d + e)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2956 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + g = d + e)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2957 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + d < e + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + g = d + e)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ 2 * a + f < e + g ∧ a + b + e < e + g ∧ a + c + d < e + g ∧ 2 * b + d < e + g ∧ b + 2 * c < e + g ∧ c + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2958 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + g = d + e) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2959 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + g = d + e)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2960 (a b c d e f g : Nat)
    (q0 : 2 * a + d < e + g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + g = d + e)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    2 * a + d < e + g ∧ a + b + c < e + g ∧ 3 * b < e + g ∧ a + f < e + g ∧ b + e < e + g ∧ c + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2961 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b = d)
    (q5 : c + f < b + g)
    (q6 : d + e < b + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2962 (a b c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : 4 * a + f < 2 * g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b = d)
    (q6 : d + e < b + g) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + b + e < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + c + e < 2 * g ∧ a + b + 2 * d < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 3 * b + e < 2 * g ∧ 2 * b + c + d < 2 * g ∧ b + 3 * c < 2 * g ∧ a + e + f < 2 * g ∧ b + c + g < 2 * g ∧ b + d + f < 2 * g ∧ b + 2 * e < 2 * g ∧ 2 * c + f < 2 * g ∧ c + d + e < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2963 (a b c d e f g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g)
    (q6 : d + e < b + g) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2964 (a b c d e f g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g)
    (q6 : d + e < b + g) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2965 (a b c d e f g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g)
    (q6 : d + e < b + g) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2966 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g)
    (q6 : d + e < b + g) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2967 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g)
    (q6 : d + e < b + g) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2968 (a b c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g)
    (q6 : d + e < b + g) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2969 (a b c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 4 * a + d < e + g ∧ 3 * a + f < e + g)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : a + 2 * b = 2 * c)
    (q6 : d + e < b + g) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2970 (a b c d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : 5 * a + 2 * b = 2 * g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g ∧ d + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2971 (a b c d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : 5 * a + 2 * b = 2 * g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ b + e < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2972 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + f < b + g)
    (q6 : d + e < b + g)
    (q7 : d < a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2973 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : d + e < b + g)
    (q6 : d < a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2974 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + d < e + g)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d)
    (q5 : b + g = d + e)
    (q6 : e + f < a + b + g) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2975 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + d < e + g)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d)
    (q5 : b + g = d + e)
    (q6 : e + f < a + b + g) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ 2 * a + f < e + g ∧ a + b + e < e + g ∧ a + c + d < e + g ∧ 2 * b + d < e + g ∧ b + 2 * c < e + g ∧ c + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2976 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + d < e + g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : b + g = d + e)
    (q6 : d < a + b) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2977 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + d < e + g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : b + g = d + e)
    (q6 : c + f < b + g)
    (q7 : d < a + b) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ 2 * a + f < e + g ∧ a + b + e < e + g ∧ a + c + d < e + g ∧ 2 * b + d < e + g ∧ b + 2 * c < e + g ∧ c + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2978 (a b c d e f g : Nat)
    (q0 : 2 * a + d < e + g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : 2 * c < a + 2 * b)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : b + g = d + e)
    (q6 : d < a + b) :
    2 * a + d < e + g ∧ a + b + c < e + g ∧ 3 * b < e + g ∧ a + f < e + g ∧ b + e < e + g ∧ c + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2979 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d)
    (q5 : d + e < b + g)
    (q6 : f < 2 * a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2980 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d)
    (q5 : d + e < b + g)
    (q6 : f < 2 * a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2981 (a b c d e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 4 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : d + e < b + g)
    (q6 : e + f < a + b + g) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2982 (a b c d e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : d + e < b + g)
    (q6 : e + f < a + b + g) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2983 (a b c d e f g : Nat)
    (q0 : 2 * a + b < 2 * e)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : d + e < b + g)
    (q6 : e + f < a + b + g) :
    2 * a + b < 2 * e ∧ a + d < 2 * e ∧ b + c < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2984 (a b c d e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 4 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : d + e < b + g)
    (q6 : e + f < a + b + g) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2985 (a b c d e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : d + e < b + g)
    (q6 : e + f < a + b + g) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2986 (a b c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : 4 * a + f < 2 * g)
    (q4 : 5 * a + 2 * b = 2 * g)
    (q5 : a + 2 * b < g)
    (q6 : d < a + b) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + b + e < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + c + e < 2 * g ∧ a + b + 2 * d < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 3 * b + e < 2 * g ∧ 2 * b + c + d < 2 * g ∧ b + 3 * c < 2 * g ∧ a + e + f < 2 * g ∧ b + c + g < 2 * g ∧ b + d + f < 2 * g ∧ b + 2 * e < 2 * g ∧ 2 * c + f < 2 * g ∧ c + d + e < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2987 (a b c d e f g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : e < a + c)
    (q5 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c ∧ d + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2988 (a b c d e f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f)
    (q5 : c + d < a + f)
    (q6 : e < a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c ∧ d + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2989 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d + g < a + c + f)
    (q5 : e < a + c)
    (q6 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2990 (a b c d e f g : Nat)
    (q0 : 4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d + g < a + c + f)
    (q5 : e < a + c)
    (q6 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g ∧ d + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2991 (a b c d e f g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * d < 2 * c + 2 * f)
    (q4 : b + g < c + f)
    (q5 : d + g < a + c + f)
    (q6 : e < a + c)
    (q7 : g < 2 * a + c) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ b + e < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2992 (a b c d e f g : Nat)
    (q0 : 2 * a + f < c + g)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + g < c + f)
    (q5 : d + g < a + c + f)
    (q6 : e < a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g ∧ d + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2993 (a b c d e f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q4 : 4 * c < a + 2 * f)
    (q5 : a + 2 * b < 2 * c)
    (q6 : b + c < f)
    (q7 : d + e < c + f) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2994 (a b c d e f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + d < a + f)
    (q5 : c + f = d + e)
    (q6 : d + g < a + c + f) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2995 (a b c d e f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + d < a + d + f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f)
    (q6 : c + f = d + e)
    (q7 : e < a + c) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + c + e < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2996 (a b c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : b + c < f)
    (q5 : d + e < c + f)
    (q6 : e < a + c) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2997 (a b c d e f g : Nat)
    (q0 : 2 * g < a + 2 * f)
    (q1 : 4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : b + c < f)
    (q5 : d + e < c + f)
    (q6 : e < a + c) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2998 (a b c d e f g : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : a + c = e)
    (q5 : b + c < f)
    (q6 : d + e < c + f)
    (q7 : g < 2 * a + c) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2999 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f)
    (q6 : e < a + c)
    (q7 : g < 2 * a + c) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega

end Max11DegreeRoutes
