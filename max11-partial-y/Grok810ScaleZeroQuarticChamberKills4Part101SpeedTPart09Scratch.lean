import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1800 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1801 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1802 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1803 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1804 (a b c f : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1805 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1806 (a b c e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1807 (a b c e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1808 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1809 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1810 (a b c e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1811 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1812 (a b c e f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f) :
    2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + b + e < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1813 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a + b = f)
    (q2 : 2 * e < a + b + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1814 (a b c e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1815 (a b c e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1816 (a b c e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1817 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1818 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1819 (a b e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1820 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1821 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 4 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b + f = 2 * e) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1822 (a b f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 4 * b < 2 * f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1823 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1824 (a b e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 4 * b < 2 * f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1825 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1826 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1827 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 3 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b + f = 2 * e) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + b + e < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + c + e < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1828 (a b f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : a ≤ 4 * b) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1829 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1830 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1831 (a b e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 4 * b < 2 * f) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1832 (a b e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1833 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1834 (a b c e f : Nat)
    (q0 : 2 * a + f < a + 2 * f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b + f = 2 * e) :
    2 * a + b + c < a + 2 * f ∧ a + 3 * b < a + 2 * f ∧ 2 * a + f < a + 2 * f ∧ a + b + e < a + 2 * f ∧ b + 2 * c < a + 2 * f ∧ c + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1835 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : b + e < a + f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1836 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 3 * a + f < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : b + e < a + f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1837 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : b + e < a + f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1838 (a b c e f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + 2 * b = 2 * e)
    (q3 : a + b + f = 2 * e)
    (q4 : b + e < a + f) :
    2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + b + e < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1839 (a b c e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < a + b + f)
    (q3 : 4 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1840 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 2 * c < a + 2 * b)
    (q3 : 2 * e < a + b + f)
    (q4 : 3 * a + b < a + b + f)
    (q5 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1841 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 4 * c)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1842 (a b c e f : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1843 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 4 * c)
    (q4 : e < a + c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ b + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1844 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1845 (a b c e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1846 (a b c e f : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1847 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ b + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1848 (a b c e f : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1849 (a b c e f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1850 (a b c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1851 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1852 (a b c e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1853 (a b c e f : Nat)
    (q0 : 4 * a + b < 2 * e ∧ 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1854 (a b c e f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1855 (a b c e f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1856 (a b c e f : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1857 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1858 (a b c e f : Nat)
    (q0 : 3 * a + b < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1859 (a b c e f : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : a ≤ 4 * b)
    (q3 : b + c < f) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1860 (a b c e f : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1861 (a b c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : d = 0)
    (q4 : e < a + c) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1862 (a b c e f : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1863 (a b c e f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1864 (a b c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c)
    (q4 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1865 (a b c e f : Nat)
    (q0 : 2 * a + b < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : b + c < f)
    (q5 : e < a + c) :
    2 * a + b < 2 * e ∧ b + c < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1866 (a b c e f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e)
    (q4 : b + c < f) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1867 (a b c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : a + c = e)
    (q5 : b + c < f) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1868 (a b c e f : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : b + c < f)
    (q5 : e < a + c) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1869 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * c < 2 * e)
    (q3 : 7 * a ≤ 4 * c)
    (q4 : a + 2 * b + c < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1870 (a b c e f : Nat)
    (q0 : 2 * b < e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e)
    (q3 : 4 * a + b < 2 * e ∧ 2 * a + f < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1871 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 2 * c < a + e)
    (q3 : 3 * a + b < 2 * e)
    (q4 : a + b + f < 2 * e) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1872 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 2 * e)
    (q2 : 3 * c < 2 * e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + b + f < 2 * e) :
    2 * a + b < 2 * e ∧ b + c < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1873 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + b + f < 2 * e) :
    3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1874 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * c + 2 * f < 4 * e) :
    3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1875 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1876 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * c + 2 * f < 4 * e) :
    3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1877 (a b c e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + b + f < 2 * e) :
    3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1878 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + b + f < 2 * e) :
    3 * a + b + c < 2 * c + e ∧ 2 * a + 3 * b < 2 * c + e ∧ 3 * a + f < 2 * c + e ∧ 2 * a + b + e < 2 * c + e ∧ a + b + 2 * c < 2 * c + e ∧ 3 * b + c < 2 * c + e ∧ a + c + f < 2 * c + e ∧ 2 * b + f < 2 * c + e ∧ b + c + e < 2 * c + e ∧ e + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1879 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 3 * a ≤ 4 * b)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + b + f < 2 * e) :
    2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1880 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * c + 2 * f < 4 * e) :
    2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1881 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1882 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * c + 2 * f < 4 * e) :
    2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1883 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + b + f < 2 * e) :
    2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1884 (a b c e f : Nat)
    (q0 : 2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e) :
    2 * a + b + c < 2 * c + e ∧ a + 3 * b < 2 * c + e ∧ 2 * a + f < 2 * c + e ∧ a + b + e < 2 * c + e ∧ b + 2 * c < 2 * c + e ∧ c + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1885 (a b c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * c + 2 * f < 4 * e)
    (q3 : a + 2 * e = 2 * f)
    (q4 : a + b + f < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1886 (a b c e f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + 2 * c < 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 7 * a > 2 * f)
    (q4 : a + 2 * e < 2 * f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1887 (a b c e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1888 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a + b < c + g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1889 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1890 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a + b < c + g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ b + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1891 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1892 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : 5 * a + 2 * b = 2 * g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1893 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : 5 * a + 2 * b = 2 * g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ b + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1894 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1895 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 4 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1896 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1897 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1898 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1899 (a b c e g : Nat)
    (q0 : 2 * a + b < 2 * e)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g) :
    2 * a + b < 2 * e ∧ b + c < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1900 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 4 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1901 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1902 (a b c e g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c)
    (q4 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1903 (a b c e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1904 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1905 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1906 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ b + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1907 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1908 (a b c e g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 4 * a + b < c + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : e < a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1909 (a b c e g : Nat)
    (q0 : 2 * b < e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e)
    (q3 : 4 * a + b < 2 * e)
    (q4 : g < a + e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1910 (a b c e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1911 (a b c e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 4 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1912 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1913 (a b c f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1914 (a b c f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1915 (a b c f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1916 (a b c f g : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1917 (a b c f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1918 (a b c f g : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1919 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1920 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1921 (a b c f : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1922 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1923 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1924 (a b c f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1925 (a b c f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : a ≤ 4 * b)
    (q2 : b + c < f) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1926 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1927 (a b c f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1928 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1929 (a b c f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : a + f < 2 * f)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    a + b + c < 2 * f ∧ 3 * b < 2 * f ∧ a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1930 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1931 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1932 (a b c f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1933 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1934 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1935 (a b c f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1936 (a b c f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * b < 2 * f)
    (q4 : c + g < a + b + f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1937 (a b c f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + 4 * b < 2 * f)
    (q5 : c + g < a + b + f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1938 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1939 (a b c f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1940 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1941 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1942 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : c + g < a + b + f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1943 (a b c f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : c + g < a + b + f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1944 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : c + g < a + b + f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1945 (a b c f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1946 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1947 (a b c f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1948 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1949 (a b c f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1950 (a b c f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1951 (a b c f g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    2 * a + b < c + g ∧ b + c < c + g ∧ f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1952 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1953 (a b c f g : Nat)
    (q0 : 4 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1954 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1955 (a b c f g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1956 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b < g)
    (q4 : f < 2 * a + b) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1957 (a b c f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + f < 2 * g)
    (q3 : 5 * a + 2 * b = 2 * g)
    (q4 : a + 2 * b < g) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * b + f < 2 * g ∧ b + 3 * c < 2 * g ∧ b + c + g < 2 * g ∧ 2 * c + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1958 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 4 * c)
    (q4 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1959 (a b c f g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1960 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1961 (a b c f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1962 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1963 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1964 (a b c f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1965 (a b c f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1966 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : d = 0)
    (q4 : g < 2 * a + c) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1967 (a b c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : e = 0)
    (q4 : g < 2 * a + c) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1968 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1969 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1970 (a b c f g : Nat)
    (q0 : 4 * a + b < c + g ∧ 2 * a + f < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1971 (a b c f g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1972 (a b c f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1973 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : d = 0)
    (q4 : g < 2 * a + c) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1974 (a b c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : e = 0)
    (q4 : g < 2 * a + c) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1975 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1976 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1977 (a b c f g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1978 (a b c f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a ≤ 4 * b)
    (q3 : b + g < c + f) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1979 (a b c f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1980 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : d = 0)
    (q4 : g < 2 * a + c) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1981 (a b c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : e = 0)
    (q4 : g < 2 * a + c) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1982 (a b c f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1983 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1984 (a b c f g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g ∧ b + c < c + g ∧ f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1985 (a b c f g : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + g < c + f) :
    2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1986 (a c f g : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * f = 2 * g) :
    2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1987 (a b c d f g : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1988 (a b c e f g : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1989 (a c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * f = 2 * g) :
    2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1990 (a c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * f = 2 * g) :
    2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1991 (a b c f g : Nat)
    (q0 : 2 * a + f < c + g)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + g < c + f) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1992 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1993 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1994 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1995 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1996 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g ∧ 2 * a + f < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1997 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1998 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1999 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g := by
  omega

end Max11DegreeRoutes
