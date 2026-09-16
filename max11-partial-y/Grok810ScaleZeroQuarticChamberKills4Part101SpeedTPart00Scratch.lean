import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0000 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 4 * a > g)
    (q2 : 6 * a ≤ d + g)
    (q3 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0001 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 6 * a ≤ e + f)
    (q2 : 7 * a > 2 * f)
    (q3 : e = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0002 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0003 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 6 * a ≤ 2 * b + f)
    (q3 : f = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0004 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 6 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : e = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0005 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 6 * a ≤ b + 2 * d)
    (q3 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0006 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 6 * a ≤ 2 * c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0007 (a b c : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 6 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0008 (a b c : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0009 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 4 * a > g)
    (q2 : 5 * a ≤ d + g)
    (q3 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0010 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ e + f)
    (q2 : 7 * a > 2 * f)
    (q3 : e = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0011 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ 2 * b + d)
    (q3 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0012 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ 2 * b + f)
    (q3 : f = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0013 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : e = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0014 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ b + 2 * d)
    (q3 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0015 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ 2 * c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0016 (a b c : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0017 (a b c : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0018 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 4 * a ≤ d + g)
    (q2 : d = 0)
    (q3 : g = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0019 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 4 * a ≤ e + f)
    (q2 : 7 * a > 2 * f)
    (q3 : e = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0020 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ 2 * b + d)
    (q3 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0021 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ 2 * b + f)
    (q3 : f = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0022 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : e = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0023 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ b + 2 * d)
    (q3 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0024 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ 2 * c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0025 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0026 (a b e : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ b + e)
    (q3 : e = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0027 (a b c d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ c + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0028 (a b : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ 3 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0029 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0030 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ d + g)
    (q2 : d = 0)
    (q3 : g = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0031 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ e + f)
    (q2 : e = 0)
    (q3 : f = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0032 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 2 * b + d)
    (q2 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0033 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ 2 * b + f)
    (q3 : f = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0034 (a b c e : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : e = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0035 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ b + 2 * d)
    (q3 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0036 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ 2 * c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0037 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0038 (a b e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ b + e)
    (q3 : e = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0039 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0040 (a b : Nat)
    (q0 : 0 < a)
    (q1 : a ≤ b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0041 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ f)
    (q2 : f = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0042 (a b c : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0043 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c) :
    2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0044 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ d + g)
    (q2 : d = 0)
    (q3 : g = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0045 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ e + f)
    (q2 : e = 0)
    (q3 : f = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0046 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : a ≤ 2 * b + d)
    (q2 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0047 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 2 * b + f)
    (q2 : f = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0048 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : e = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0049 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + 2 * d)
    (q2 : 3 * a > 2 * b)
    (q3 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0050 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 2 * c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0051 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0052 (a b e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + e)
    (q2 : 3 * a > 2 * b)
    (q3 : e = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0053 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ c + d)
    (q2 : 3 * a > 2 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0054 (a b : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 3 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0055 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ f)
    (q2 : f = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0056 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0057 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ d)
    (q2 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0058 (a b c g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : g = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0059 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ c + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0060 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0061 (a b c : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0062 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0063 (a b c : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0064 (a b c : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0065 (a b c g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : g = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0066 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ c + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0067 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0068 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a ≤ b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0069 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0070 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0071 (a b c : Nat)
    (q0 : 3 * a + b < a + 2 * b + c)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c) :
    3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0072 (a b c g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : g = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0073 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ c + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0074 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d = 0)
    (q4 : e = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0075 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0076 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0077 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0078 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0079 (a b c : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0080 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c) :
    2 * a + b < a + 2 * b + c ∧ b + c < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0081 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 6 * a ≤ d + g)
    (q3 : d < a + b)
    (q4 : g = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0082 (a b d : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0083 (a b d : Nat)
    (q0 : 6 * a ≤ b + 2 * d)
    (q1 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0084 (a b c d : Nat)
    (q0 : 6 * a ≤ 2 * c + d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0085 (a b c d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0086 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ d + g)
    (q3 : d < a + b)
    (q4 : g = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0087 (a b d : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0088 (a b d : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0089 (a b c d : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0090 (a b c d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0091 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ d + g)
    (q3 : d < a + b)
    (q4 : g = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0092 (a b d : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0093 (a b d : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0094 (a b c d : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0095 (a b c d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0096 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ d + g)
    (q3 : d < a + b)
    (q4 : g = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0097 (a b d : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0098 (a b d : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0099 (a b c d : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0100 (a b c d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0101 (a b d g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : 3 * a > 2 * b)
    (q2 : d < a + b)
    (q3 : g = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0102 (a b d : Nat)
    (q0 : a ≤ 2 * b + d)
    (q1 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0103 (a b d : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0104 (a b c d : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0105 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0106 (a b d : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 3 * a > 2 * b)
    (q2 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0107 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : e = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0108 (a b c d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0109 (a b c d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0110 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : e = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0111 (a b c d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0112 (a b c d : Nat)
    (q0 : 3 * a + b < a + 2 * b + c)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0113 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : e = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0114 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0115 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0116 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 6 * a ≤ e + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + e < 2 * a + 2 * b)
    (q5 : f = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0117 (a b c e : Nat)
    (q0 : 6 * a ≤ b + c + e)
    (q1 : c + e < 2 * a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0118 (a b c e : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ c + e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0119 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ e + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + e < 2 * a + 2 * b)
    (q5 : f = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0120 (a b c e : Nat)
    (q0 : 5 * a ≤ b + c + e)
    (q1 : c + e < 2 * a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0121 (a b c e : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0122 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ e + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + e < 2 * a + 2 * b)
    (q5 : f = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0123 (a b c e : Nat)
    (q0 : 4 * a ≤ b + c + e)
    (q1 : c + e < 2 * a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0124 (a b c e : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0125 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0126 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ e + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + e < 2 * a + 2 * b)
    (q5 : f = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0127 (a b c e : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : c + e < 2 * a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0128 (a b c e : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0129 (a b c e f : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : f = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0130 (a b c e : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : c + e < 2 * a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0131 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0132 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + e < 2 * a + 2 * b)
    (q5 : d = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0133 (a b c e : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0134 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + e < 2 * a + 2 * b)
    (q5 : d = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0135 (a b c e : Nat)
    (q0 : 3 * a + b < a + 2 * b + c)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b) :
    3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ b + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0136 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + e < 2 * a + 2 * b)
    (q5 : d = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0137 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * f < 5 * a + 6 * b)
    (q3 : 6 * a ≤ e + f)
    (q4 : e = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0138 (a b c f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 6 * a ≤ 2 * b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0139 (a b c f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0140 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ e + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < a + 3 * b)
    (q5 : e = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0141 (a b c f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ 2 * b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0142 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ e + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < a + 3 * b)
    (q5 : e = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0143 (a b c f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ 2 * b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0144 (a b c e f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ e + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b)
    (q4 : e = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0145 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ 2 * b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0146 (a b c f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0147 (a b c e f : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b)
    (q4 : e = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0148 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 2 * b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0149 (a b c f : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0150 (a b c f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0151 (a b c f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0152 (a b c f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0153 (a b c f : Nat)
    (q0 : 3 * a + b < a + 2 * b + c)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0154 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0155 (a b c f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0156 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b) :
    2 * a + b < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0157 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 6 * a ≤ d + g)
    (q3 : d = 0)
    (q4 : g < a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0158 (a b c g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : g < a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0159 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ d + g)
    (q3 : d = 0)
    (q4 : g < a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0160 (a b c g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : g < a + 2 * b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0161 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ d + g)
    (q3 : d = 0)
    (q4 : g < a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0162 (a b d g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ d + g)
    (q2 : d = 0)
    (q3 : g < a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0163 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ d + g)
    (q2 : d = 0)
    (q3 : g < a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0164 (a b c g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : g < a + 2 * b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0165 (a b c g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : g < a + 2 * b) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0166 (a b c g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : g < a + 2 * b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0167 (a b c g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : g < a + 2 * b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0168 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 6 * a ≤ d + g)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0169 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 6 * a ≤ e + f)
    (q3 : 7 * a > 2 * f)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0170 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0171 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 6 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0172 (a b c e g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 6 * a ≤ b + c + e)
    (q4 : c = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0173 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 6 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0174 (a b c d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 6 * a ≤ 2 * c + d)
    (q4 : c = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0175 (a b c g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 6 * a ≤ 3 * b + c)
    (q3 : c = 0)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0176 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0177 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ d + g)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0178 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ e + f)
    (q3 : 7 * a > 2 * f)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0179 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0180 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0181 (a b c e g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 5 * a ≤ b + c + e)
    (q4 : c = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0182 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0183 (a b c d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ 2 * c + d)
    (q4 : c = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0184 (a b c g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ 3 * b + c)
    (q3 : c = 0)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0185 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a < a + 3 * b)
    (q3 : g = a + 2 * b) :
    4 * a < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0186 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ d + g)
    (q2 : 5 * a > 2 * d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0187 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ e + f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0188 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0189 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0190 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ b + c + e)
    (q3 : c = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0191 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0192 (a b c d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ 2 * c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : c = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0193 (a b c g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : c = 0)
    (q3 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0194 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ b + e)
    (q3 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0195 (a b c d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : c = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0196 (a b g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0197 (a b e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a < a + 3 * b)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : g = a + 2 * b) :
    3 * a < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0198 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ d + g)
    (q2 : d = 0)
    (q3 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0199 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ e + f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega

end Max11DegreeRoutes
