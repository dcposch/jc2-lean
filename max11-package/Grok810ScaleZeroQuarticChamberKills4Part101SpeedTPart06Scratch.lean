import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1200 (a b c e : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1201 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ b + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1202 (a b c e : Nat)
    (q0 : 3 * c < 2 * e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b + c < 2 * e) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1203 (a b c e : Nat)
    (q0 : 2 * b < e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e)
    (q3 : 4 * a + b < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1204 (a b c e : Nat)
    (q0 : 3 * c < 2 * e)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b + c < 2 * e) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1205 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 2 * c < a + e)
    (q3 : 3 * a + b < 2 * e) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1206 (a b c e : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : 3 * c < 2 * e)
    (q2 : a + 2 * b + c < 2 * e) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1207 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 2 * e)
    (q2 : 3 * c < 2 * e)
    (q3 : a + 2 * b + c < 2 * e) :
    2 * a + b < 2 * e ∧ b + c < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1208 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1209 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1210 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1211 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1212 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1213 (a b c f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1214 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1215 (a b c f : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1216 (a b c d f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0)
    (q3 : f < 2 * a + b) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1217 (a b c e f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0)
    (q3 : f < 2 * a + b) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1218 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1219 (a b c f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : f < 2 * a + b)
    (q3 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1220 (a b c f : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1221 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1222 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1223 (a b c d f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0)
    (q3 : f < 2 * a + b) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1224 (a b c e f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0)
    (q3 : f < 2 * a + b) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1225 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1226 (a b c f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : f < 2 * a + b)
    (q3 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1227 (a b c f : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1228 (a b c f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : a ≤ 4 * b)
    (q2 : b + c < f) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1229 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1230 (a b c d f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0)
    (q3 : f < 2 * a + b) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1231 (a b c e f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0)
    (q3 : f < 2 * a + b) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1232 (a b c f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1233 (a b c f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : f < 2 * a + b)
    (q3 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1234 (a b c f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : b + c < f)
    (q2 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1235 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1236 (a b c f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1237 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1238 (a b c f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1239 (a b c f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1240 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 2 * c < a + 2 * b)
    (q3 : 3 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1241 (a b c f : Nat)
    (q0 : 2 * a > c)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < 3 * c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1242 (a b c f : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 4 * c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1243 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c)
    (q3 : a + b + f < 3 * c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1244 (a b c f : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1245 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c)
    (q3 : a + b + f < 3 * c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1246 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 4 * c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1247 (a b c f : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * f < 4 * c)
    (q3 : a + b + f < 3 * c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1248 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < 3 * c) :
    2 * a + b < 3 * c ∧ b + c < 3 * c ∧ f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1249 (a b c f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1250 (a b c f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1251 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1252 (a b c e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1253 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1254 (a b c f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1255 (a b c f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1256 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1257 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1258 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1259 (a b c e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1260 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1261 (a b c f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1262 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1263 (a b c f : Nat)
    (q0 : a + 2 * f = 4 * c)
    (q1 : a ≤ 4 * b)
    (q2 : b + c < f) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1264 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1265 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1266 (a b c e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1267 (a b c f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1268 (a b c f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1269 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    2 * a + b < 3 * c ∧ b + c < 3 * c ∧ f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1270 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1271 (a b c f : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : b + c < f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1272 (a b c f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + 2 * c < 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 7 * a > 2 * f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1273 (a b c g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1274 (a b c g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1275 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1276 (a b e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1277 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1278 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1279 (a b c g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1280 (a b c g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1281 (a b c g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1282 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1283 (a b e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1284 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1285 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1286 (a b c g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1287 (a b c g : Nat)
    (q0 : a + 2 * b < g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a ≤ 4 * b) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1288 (a b c g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1289 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : d = 0) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1290 (a b e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1291 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1292 (a b c g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1293 (a b c g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    2 * a + b < c + g ∧ b + c < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1294 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1295 (a b c g : Nat)
    (q0 : 4 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1296 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1297 (a b c g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1298 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * c) :
    4 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1299 (a b c g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1300 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1301 (a b c g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1302 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1303 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1304 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : g < 2 * a + c) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1305 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e = 0)
    (q3 : g < 2 * a + c) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1306 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : f = 0)
    (q3 : g < 2 * a + c) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1307 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1308 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1309 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1310 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1311 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : g < 2 * a + c) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1312 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e = 0)
    (q3 : g < 2 * a + c) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1313 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : f = 0)
    (q3 : g < 2 * a + c) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1314 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1315 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1316 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a ≤ 4 * b) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1317 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1318 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : g < 2 * a + c) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1319 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e = 0)
    (q3 : g < 2 * a + c) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1320 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : f = 0)
    (q3 : g < 2 * a + c) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1321 (a b c g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1322 (a b c g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    2 * a + b < c + g ∧ b + c < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1323 (a b c d g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1324 (a b c e g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1325 (a b c f g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1326 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + c = g)
    (q2 : 2 * c < g)
    (q3 : a + 2 * b < 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1327 (a b c g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 4 * a + b < c + g)
    (q3 : a + 2 * b < 2 * c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1328 (a b d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 3 * a > 2 * b)
    (q3 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1329 (a b d e : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1330 (a b d e : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 9 * a ≤ 4 * e) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1331 (a b d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 6 * b < 4 * d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d ∧ b + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1332 (a b d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 7 * a ≤ 4 * e)
    (q3 : a + 6 * b < 4 * d) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1333 (a b d e : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a + 6 * b < 4 * e)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1334 (a b d e : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1335 (a b d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * b < e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1336 (a b d e : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 4 * a + b < 2 * e ∧ 3 * a + d < 2 * e)
    (q3 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ 2 * b + d < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1337 (a b d e : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1338 (a b d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1339 (a b d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : a + 2 * d < 2 * e) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1340 (a b d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 2 * e)
    (q2 : a + 2 * d < 2 * e) :
    2 * a + b < 2 * e ∧ a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1341 (a b d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1342 (a b d f : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ 2 * b + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1343 (a b d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1344 (a b d f : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1345 (a b d f : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1346 (a b d f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : d < a + b)
    (q2 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ a + d < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1347 (a b f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 4 * b < 2 * f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1348 (a b d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : a + b = d) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1349 (a b d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : a + b = d)
    (q3 : b + f = 2 * d) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1350 (a b d f : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : a + b = d)
    (q3 : b + f = 2 * d) :
    3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 5 * b < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ b + d + f < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1351 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + b = d)
    (q3 : b + f = 2 * d) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1352 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + b = d)
    (q3 : b + f = 2 * d) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1353 (a f : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1354 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + f < a + 2 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b = d)
    (q4 : b + f = 2 * d) :
    2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + 2 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1355 (a b d f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ 2 * b + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1356 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : d < a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1357 (a b d : Nat)
    (q0 : 4 * b < a + 2 * d)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 6 * b < 4 * d) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1358 (a b d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 9 * a ≤ 4 * d) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1359 (a b d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : f < a + d) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1360 (a b d f : Nat)
    (q0 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * b < a + 2 * d)
    (q3 : f < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ 2 * b + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1361 (a b d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 3 * a > 2 * b)
    (q2 : f < a + d) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1362 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : a + 6 * b < 4 * d)
    (q3 : f < a + d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1363 (a b d f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : f < a + d) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1364 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < a + 2 * d)
    (q2 : b + f < 2 * d) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1365 (a b d f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + d < f) :
    4 * a + d < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ a + 2 * b + d < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1366 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < g) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1367 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : c = 0)
    (q3 : d < a + b) :
    ¬ (7 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1368 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1369 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1370 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1371 (a b d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1372 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1373 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < g) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1374 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : c = 0)
    (q3 : d < a + b) :
    ¬ (5 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1375 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1376 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1377 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1378 (a b d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1379 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1380 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : a ≤ 4 * b) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1381 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : c = 0)
    (q3 : d < a + b) :
    ¬ (3 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1382 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1383 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1384 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1385 (a b d g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1386 (a b d : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : d < a + b) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1387 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1388 (a b d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1389 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1390 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1391 (a b d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1392 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1393 (a b d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 3 * a > 2 * b)
    (q3 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1394 (a b d g : Nat)
    (q0 : 2 * g < 3 * a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1395 (a b d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 3 * a > 2 * b) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1396 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : 2 * b + 2 * g < a + 4 * d) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1397 (a b d g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ 4 * b) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1398 (a b d g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1399 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega

end Max11DegreeRoutes
