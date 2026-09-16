import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2200 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 9 * a ≤ 4 * e)
    (q4 : d + e < c + f) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2201 (a c d e f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : d + e < c + f)
    (q4 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2202 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : b = 0)
    (q4 : d + e < c + f) :
    ¬ (a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2203 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 7 * a ≤ 4 * e)
    (q4 : d + e < c + f) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2204 (a c d e f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : d + e < c + f)
    (q4 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2205 (a c d f : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * c = 2 * d)
    (q2 : c + d < a + f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2206 (a c d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * c = 2 * d)
    (q2 : c + d < a + f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2207 (a c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2208 (a c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2209 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e) :
    4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ a + e + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2210 (a c d f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * c = 2 * d)
    (q2 : c + d < a + f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2211 (a c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * c = 2 * d)
    (q2 : c + d < a + f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2212 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2213 (a c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2214 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 3 * a + f < a + 2 * f)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e) :
    3 * a + f < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + c + f < a + 2 * f ∧ a + d + e < a + 2 * f ∧ 2 * c + d < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2215 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * c < a + 2 * f)
    (q2 : b = 0)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    ¬ (5 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2216 (a c d f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2217 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2218 (a c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : e < a + c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2219 (a c d e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 4 * c < a + 2 * f)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2220 (a c d e f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * c < a + 2 * f)
    (q2 : c + f = d + e)
    (q3 : e < a + c)
    (q4 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2221 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * a + d < a + d + f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    4 * a + d < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * c + d < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2222 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * c < a + 2 * f)
    (q2 : b = 0)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    ¬ (3 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2223 (a c d f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 5 * a ≤ 4 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2224 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2225 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : e < a + c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2226 (a c d e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 4 * c < a + 2 * f)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2227 (a c d e f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * c < a + 2 * f)
    (q2 : c + f = d + e)
    (q3 : e < a + c)
    (q4 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2228 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 3 * a + d < a + d + f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    3 * a + d < a + d + f ∧ 2 * a + f < a + d + f ∧ a + c + d < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2229 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * c < a + 2 * f)
    (q2 : b = 0)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    ¬ (a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2230 (a c d f : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : 4 * c < a + 2 * f) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2231 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2232 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : e < a + c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2233 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 9 * a ≤ 4 * f)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2234 (a c d e f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * c < a + 2 * f)
    (q2 : c + f = d + e)
    (q3 : e < a + c)
    (q4 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2235 (a c d e f : Nat)
    (q0 : 2 * a + d < a + d + f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 4 * c < a + 2 * f)
    (q3 : c + f = d + e)
    (q4 : e < a + c) :
    2 * a + d < a + d + f ∧ a + f < a + d + f ∧ c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2236 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : d + e < c + f)
    (q4 : e < a + c) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2237 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : d + e < c + f)
    (q4 : e < a + c) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2238 (a c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : d + e < c + f)
    (q4 : e < a + c) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2239 (a c d e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : d + e < c + f)
    (q4 : e < a + c) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2240 (a c d e f : Nat)
    (q0 : 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ a + c + d < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2241 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : d + e < c + f)
    (q4 : e < a + c) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2242 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : d + e < c + f)
    (q4 : e < a + c) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2243 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : d + e < c + f)
    (q4 : e < a + c) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2244 (a c d e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : d + e < c + f)
    (q4 : e < a + c) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2245 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e)
    (q4 : d + e < c + f) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2246 (a c d e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e)
    (q4 : d + e < c + f) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ a + c + d < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2247 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e)
    (q4 : d + e < c + f) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2248 (a c d e f : Nat)
    (q0 : 0 < a)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : a + c = e)
    (q3 : a + f < 2 * e)
    (q4 : d + e < c + f) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2249 (a c d e f : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : e < a + c) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * c + d < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2250 (a c d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 3 * a + 2 * c = 2 * f)
    (q4 : e < a + c) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ a + c + d < 2 * f ∧ c + f < 2 * f ∧ d + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2251 (a c d e f : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 3 * c < a + 2 * d)
    (q3 : 5 * a > 2 * d)
    (q4 : f < a + d) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2252 (a c d f : Nat)
    (q0 : 2 * c + 2 * f < a + 4 * d)
    (q1 : 5 * a > 2 * d)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + d = f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2253 (a c d e f : Nat)
    (q0 : 2 * c + 2 * f < a + 4 * d)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e)
    (q4 : a + d = f) :
    4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ a + e + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2254 (a c d f : Nat)
    (q0 : 2 * c + 2 * f < a + 4 * d)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + d = f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2255 (a c d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c + 2 * f < a + 4 * d)
    (q2 : 3 * a + f < a + 2 * f)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * d = 2 * e)
    (q5 : a + d = f) :
    3 * a + f < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + c + f < a + 2 * f ∧ a + d + e < a + 2 * f ∧ 2 * c + d < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2256 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2257 (a d e f : Nat)
    (q0 : 2 * f < a + 2 * e)
    (q1 : 3 * a > e)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2258 (a d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2259 (a d e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2260 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e)
    (q2 : 3 * a > e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ a + c + d < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2261 (a c d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + e)
    (q2 : 2 * f < a + 2 * e)
    (q3 : 5 * a ≤ 4 * c)
    (q4 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2262 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : 7 * a ≤ 4 * d)
    (q4 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2263 (a c d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + e)
    (q2 : 2 * f < a + 2 * e)
    (q3 : 9 * a ≤ 4 * e)
    (q4 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2264 (a c d e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < a + e)
    (q2 : 2 * f < a + 2 * e)
    (q3 : 3 * a > e)
    (q4 : d + f < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2265 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * d < 2 * e)
    (q3 : b = 0) :
    ¬ (5 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2266 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2267 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2268 (a c d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2269 (a c d e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2270 (a c d e g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * d < 2 * e)
    (q3 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2271 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 4 * a + d < 2 * c + e ∧ 3 * a + f < 2 * c + e) :
    4 * a + d < 2 * c + e ∧ 3 * a + f < 2 * c + e ∧ 2 * a + c + d < 2 * c + e ∧ a + c + f < 2 * c + e ∧ a + d + e < 2 * c + e ∧ 2 * c + d < 2 * c + e ∧ e + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2272 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * d < 2 * e)
    (q3 : b = 0) :
    ¬ (3 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2273 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2274 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2275 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2276 (a c d e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2277 (a c d e g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * d < 2 * e)
    (q3 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2278 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 3 * a + d < 2 * c + e ∧ 2 * a + f < 2 * c + e) :
    3 * a + d < 2 * c + e ∧ 2 * a + f < 2 * c + e ∧ a + c + d < 2 * c + e ∧ c + f < 2 * c + e ∧ d + e < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2279 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * d < 2 * e)
    (q3 : b = 0) :
    ¬ (a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2280 (a c d e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 9 * a ≤ 4 * f)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2281 (a c d e g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * d < 2 * e)
    (q3 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2282 (a c d e f : Nat)
    (q0 : 2 * a + d < 2 * c + e)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e) :
    2 * a + d < 2 * c + e ∧ a + f < 2 * c + e ∧ c + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2283 (a c d e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * c + 2 * f < 4 * e)
    (q3 : a + 2 * e = 2 * f)
    (q4 : d + f < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ a + c + d < 2 * e ∧ c + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2284 (a c d e f : Nat)
    (q0 : 0 < a)
    (q1 : a + 2 * c + 2 * f < 4 * e)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + f < 2 * e)
    (q4 : d + f < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2285 (a c d e f : Nat)
    (q0 : 3 * a + 2 * c < 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * e < 2 * f)
    (q4 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * c + d < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2286 (a c d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : 3 * a + 2 * c < 2 * f)
    (q3 : a + 2 * e < 2 * f)
    (q4 : a + d < f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ a + c + d < 2 * f ∧ c + f < 2 * f ∧ d + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2287 (a c d e g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : c + g = a + 2 * d) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2288 (a c d e g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2289 (a c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q2 : 2 * c < g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2290 (a c d e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q2 : 2 * c < g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2291 (a c d e g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 4 * a + d < e + g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d) :
    4 * a + d < e + g ∧ 2 * a + c + d < e + g ∧ a + d + e < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2292 (a c d e g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : c + g = a + 2 * d) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2293 (a c d e g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2294 (a c d e g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2295 (a c d e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q2 : 2 * c < g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2296 (a c d e g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 3 * a + d < e + g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d) :
    3 * a + d < e + g ∧ a + c + d < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2297 (a c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2298 (a c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * d < c + g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2299 (a c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2300 (a c d e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2301 (a c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + d < e + g)
    (q2 : a + c = e)
    (q3 : c + g = 2 * e) :
    4 * a + d < e + g ∧ 2 * a + c + d < e + g ∧ a + d + e < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2302 (a c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2303 (a c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * d < c + g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2304 (a c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * d < c + g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2305 (a c d e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2306 (a c d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + d < e + g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    3 * a + d < e + g ∧ a + c + d < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2307 (a c d e g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * d = 2 * e)
    (q4 : c + g < a + 2 * d) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2308 (a c d e g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 4 * a + d < e + g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e)
    (q4 : c + g < a + 2 * d) :
    4 * a + d < e + g ∧ 2 * a + c + d < e + g ∧ a + d + e < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2309 (a c d e g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * d = 2 * e)
    (q4 : c + g < a + 2 * d) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2310 (a c d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < e + g)
    (q3 : a + 2 * d = 2 * e)
    (q4 : c + g < a + 2 * d) :
    3 * a + d < e + g ∧ a + c + d < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2311 (a c d e g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : c + g < a + 2 * d)
    (q4 : e + g < 2 * a + 2 * d) :
    3 * a + d < a + 2 * d ∧ a + c + d < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2312 (a d e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a > e)
    (q2 : a + 2 * d < 2 * e)
    (q3 : g < a + e) :
    3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2313 (a d e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 3 * a > e)
    (q2 : a + 2 * d < 2 * e)
    (q3 : g < a + e) :
    2 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2314 (a c d e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * d < 2 * e)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2315 (a d e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a > e)
    (q2 : a + 2 * d < 2 * e)
    (q3 : a + e = g) :
    3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2316 (a c d e g : Nat)
    (q0 : 3 * a + d < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + e = g)
    (q3 : c + g < 2 * e) :
    3 * a + d < 2 * e ∧ a + c + d < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2317 (a c d e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * d < 2 * e)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    2 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2318 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : a + 2 * d < 2 * e)
    (q3 : a + e = g) :
    2 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2319 (a c d e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < 2 * e)
    (q2 : a + 2 * d < 2 * e)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    2 * a + d < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2320 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c)
    (q4 : g < 2 * c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2321 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 2 * f = 4 * c)
    (q4 : c + d < a + f) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2322 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 2 * f = 4 * c)
    (q4 : c + d < a + f) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2323 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 2 * g < a + 2 * f)
    (q4 : 4 * c < a + 2 * f) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2324 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 2 * g < a + 2 * f)
    (q4 : 4 * c < a + 2 * f) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2325 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 2 * g < a + 2 * f)
    (q4 : 4 * c < a + 2 * f) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2326 (a c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : g < 2 * a + c) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2327 (a c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c = 2 * d)
    (q3 : d + f < c + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2328 (a c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * c = 2 * d)
    (q3 : d + f < c + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2329 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2330 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2331 (a c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < g)
    (q2 : 4 * a + f < 2 * g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d) :
    4 * a + f < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 2 * c + f < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2332 (a c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * c = 2 * d)
    (q3 : d + f < c + g) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2333 (a c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * c = 2 * d)
    (q3 : d + f < c + g) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2334 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2335 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2336 (a c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < g)
    (q2 : 3 * a + f < 2 * g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g ∧ a + c + f < 2 * g ∧ 2 * c + d < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2337 (a c d f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : c + g < a + 2 * d)
    (q4 : f < a + d) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2338 (a c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < a + 2 * d)
    (q2 : 3 * a + 2 * d = 2 * g)
    (q3 : c + g < a + 2 * d)
    (q4 : f < a + d) :
    2 * a + d < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2339 (a c d f g : Nat)
    (q0 : 2 * g < a + 2 * f)
    (q1 : 3 * a + 2 * c < 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 7 * a > 2 * f)
    (q4 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2340 (a c d f g : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f)
    (q4 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2341 (a c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f)
    (q4 : a + d < f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ a + c + d < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2342 (a c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + c < g)
    (q2 : 3 * a + 2 * d < 2 * g)
    (q3 : 4 * a + f < 2 * g)
    (q4 : 4 * a > g) :
    4 * a + f < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 2 * c + f < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2343 (a c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + c < g)
    (q2 : 3 * a + 2 * d < 2 * g)
    (q3 : 3 * a + f < 2 * g)
    (q4 : 4 * a > g)
    (q5 : a + 2 * f < 2 * g) :
    3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g ∧ a + c + f < 2 * g ∧ 2 * c + d < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2344 (a c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : e < a + c) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2345 (a c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : e < a + c) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2346 (a c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e)
    (q4 : g < 2 * a + c) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2347 (a c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e)
    (q4 : g < 2 * a + c) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2348 (a c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2349 (a c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2350 (a c e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2351 (a c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2352 (a c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + f < e + g)
    (q2 : a + c = e)
    (q3 : c + g = 2 * e) :
    3 * a + f < e + g ∧ a + c + f < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2353 (a c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2354 (a c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2355 (a c e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2356 (a c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + c = e)
    (q4 : c + g = 2 * e) :
    2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2357 (a c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < e + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + c = e) :
    2 * a + f < e + g ∧ c + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2358 (a e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : g < a + e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2359 (a e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : g < a + e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2360 (a c e f g : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2361 (a c e f g : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + e = g)
    (q3 : c + g < 2 * e) :
    2 * a + f < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2362 (a c e f g : Nat)
    (q0 : 3 * a > e)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2363 (a e f g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + e = g) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2364 (a e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f)
    (q3 : g < a + e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2365 (a c e f g : Nat)
    (q0 : 2 * f < a + 2 * e)
    (q1 : 3 * a > e)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2366 (a e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + e = g) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2367 (a c e f g : Nat)
    (q0 : 2 * f < a + 2 * e)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2368 (a e f g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : 2 * f < a + 2 * e)
    (q3 : a + e = g) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2369 (a c e f g : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f)
    (q4 : e + g < 2 * f) :
    3 * a + f < 2 * f ∧ a + c + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2370 (a c e f g : Nat)
    (q0 : 2 * a + c < g)
    (q1 : 4 * a + f < 2 * g)
    (q2 : 4 * a > g)
    (q3 : a + e < g) :
    4 * a + f < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + e + f < 2 * g ∧ 2 * c + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2371 (a c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + c < g)
    (q2 : 3 * a + f < 2 * g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + e < g) :
    3 * a + f < 2 * g ∧ a + c + f < 2 * g ∧ e + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2372 (a d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f)
    (q4 : e + g < 2 * a + 2 * d) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2373 (a d e f g : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f)
    (q4 : e + g < 2 * a + 2 * d) :
    4 * a + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + e + f < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2374 (a d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f)
    (q4 : e + g < 2 * a + 2 * d) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2375 (a d e f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f)
    (q4 : e + g < 2 * a + 2 * d) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2376 (a d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e)
    (q4 : f < a + d) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2377 (a d e f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 4 * a + d < e + g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e)
    (q4 : f < a + d) :
    4 * a + d < e + g ∧ 3 * a + f < e + g ∧ a + d + e < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2378 (a d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e)
    (q4 : f < a + d) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2379 (a d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < e + g)
    (q3 : f < a + d) :
    3 * a + d < e + g ∧ 2 * a + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2380 (a d e f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 9 * a ≤ 4 * f)
    (q3 : a + 2 * d = 2 * e)
    (q4 : f < a + d) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2381 (a d e f g : Nat)
    (q0 : 2 * a + d < e + g)
    (q1 : f < a + d) :
    2 * a + d < e + g ∧ a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2382 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2383 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2384 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b < g)
    (q4 : b + g = d + e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2385 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + d < e + g)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d)
    (q5 : b + g = d + e) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + d + e < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2386 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * b < g)
    (q4 : b + g = d + e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2387 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + d < e + g)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d)
    (q5 : b + g = d + e) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ a + b + e < e + g ∧ a + c + d < e + g ∧ 2 * b + d < e + g ∧ b + 2 * c < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2388 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + d < e + g)
    (q3 : a + 2 * b < g)
    (q4 : b + g = d + e)
    (q5 : d < a + b) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + d + e < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2389 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + d < e + g)
    (q3 : a + 2 * b < g)
    (q4 : b + g = d + e)
    (q5 : d < a + b) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ a + b + e < e + g ∧ a + c + d < e + g ∧ 2 * b + d < e + g ∧ b + 2 * c < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2390 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a ≤ 4 * c)
    (q3 : a + 2 * b < g)
    (q4 : b + g = d + e) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2391 (a b c d e g : Nat)
    (q0 : 2 * a + d < e + g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : 2 * c < a + 2 * b)
    (q3 : a + 2 * b < g)
    (q4 : b + g = d + e)
    (q5 : d < a + b) :
    2 * a + d < e + g ∧ a + b + c < e + g ∧ 3 * b < e + g ∧ b + e < e + g ∧ c + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2392 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d)
    (q5 : d + e < b + g) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2393 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d)
    (q5 : d + e < b + g) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2394 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 4 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : d + e < b + g) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2395 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : d + e < b + g) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2396 (a b c d e g : Nat)
    (q0 : 2 * a + b < 2 * e)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : d + e < b + g) :
    2 * a + b < 2 * e ∧ a + d < 2 * e ∧ b + c < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2397 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 4 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : d + e < b + g) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2398 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : d + e < b + g) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2399 (a b c d e g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : e < a + c)
    (q5 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + b + e < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ d + e < 3 * c := by
  omega

end Max11DegreeRoutes
